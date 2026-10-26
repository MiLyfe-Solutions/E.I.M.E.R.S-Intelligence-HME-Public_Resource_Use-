import V185TrunkScan23Chunk0020

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_124520 : List Nat := [2, 1, 4, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_124520 : Nat := 118140960795 + 124520 * 2 ^ 59
def prefixEnd_124520 : Nat := 4983230072969 + 3 ^ 40 * 124520 * 2
def baseEnd_124520 : Nat := 63938611097958048627349

theorem tailTrace_124520 : CollatzResearch.WordTrace tailWord_124520 prefixEnd_124520 63938611097958048627349 := by
  unfold tailWord_124520
  simp only [CollatzResearch.WordTrace]
  refine ⟨2270808754446390584005507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3027745005928520778674009 2270808754446390584005507)
  ·
    refine ⟨3406213131669585876008261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2270808754446390584005507 3406213131669585876008261)
    ·
      refine ⟨638664962188047351751549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3406213131669585876008261 638664962188047351751549)
      ·
        refine ⟨239499360820517756906831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 638664962188047351751549 239499360820517756906831)
        ·
          refine ⟨359249041230776635360247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239499360820517756906831 359249041230776635360247)
          ·
            refine ⟨538873561846164953040371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359249041230776635360247 538873561846164953040371)
            ·
              refine ⟨808310342769247429560557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538873561846164953040371 808310342769247429560557)
              ·
                refine ⟨303116378538467786085209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 808310342769247429560557 303116378538467786085209)
                ·
                  refine ⟨227337283903850839563907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303116378538467786085209 227337283903850839563907)
                  ·
                    refine ⟨341005925855776259345861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 227337283903850839563907 341005925855776259345861)
                    ·
                      refine ⟨63938611097958048627349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 341005925855776259345861 63938611097958048627349)
                      ·
                        rfl

theorem cell23_124520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_124520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124520 prefixEnd_124520 := by exact prefixLift 124520
  have htrace : WordTrace (prefixWord ++ tailWord_124520) baseStart_124520 baseEnd_124520 := by
    simpa [prefixWord, tailWord_124520, baseEnd_124520] using wordTrace_append hprefix tailTrace_124520
  have hstable : (prefixWord ++ tailWord_124520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124520).length < 2 ^ (prefixWord ++ tailWord_124520).sum := by decide
  have hdescent : baseEnd_124520 < baseStart_124520 := by decide
  rcases family_descends (prefixWord ++ tailWord_124520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124574 : List Nat := [4, 3, 1, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_124574 : Nat := 118140960795 + 124574 * 2 ^ 59
def prefixEnd_124574 : Nat := 4983230072969 + 3 ^ 40 * 124574 * 2
def baseEnd_124574 : Nat := 63966339053300837352101

theorem tailTrace_124574 : CollatzResearch.WordTrace tailWord_124574 prefixEnd_124574 63966339053300837352101 := by
  unfold tailWord_124574
  simp only [CollatzResearch.WordTrace]
  refine ⟨567948381337143548809597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3029058033798098926984517 567948381337143548809597)
  ·
    refine ⟨212980643001428830803599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 567948381337143548809597 212980643001428830803599)
    ·
      refine ⟨319470964502143246205399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212980643001428830803599 319470964502143246205399)
      ·
        refine ⟨479206446753214869308099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319470964502143246205399 479206446753214869308099)
        ·
          refine ⟨718809670129822303962149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479206446753214869308099 718809670129822303962149)
          ·
            refine ⟨134776813149341681992903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 718809670129822303962149 134776813149341681992903)
            ·
              refine ⟨202165219724012522989355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134776813149341681992903 202165219724012522989355)
              ·
                refine ⟨303247829586018784484033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202165219724012522989355 303247829586018784484033)
                ·
                  refine ⟨227435872189514088363025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303247829586018784484033 227435872189514088363025)
                  ·
                    refine ⟨170576904142135566272269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 227435872189514088363025 170576904142135566272269)
                    ·
                      refine ⟨63966339053300837352101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 170576904142135566272269 63966339053300837352101)
                      ·
                        rfl

theorem cell23_124574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_124574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124574 prefixEnd_124574 := by exact prefixLift 124574
  have htrace : WordTrace (prefixWord ++ tailWord_124574) baseStart_124574 baseEnd_124574 := by
    simpa [prefixWord, tailWord_124574, baseEnd_124574] using wordTrace_append hprefix tailTrace_124574
  have hstable : (prefixWord ++ tailWord_124574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124574).length < 2 ^ (prefixWord ++ tailWord_124574).sum := by decide
  have hdescent : baseEnd_124574 < baseStart_124574 := by decide
  rcases family_descends (prefixWord ++ tailWord_124574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124604 : List Nat := [2, 2, 2, 3, 1, 2, 2, 4, 1, 1, 3]
def baseStart_124604 : Nat := 118140960795 + 124604 * 2 ^ 59
def prefixEnd_124604 : Nat := 4983230072969 + 3 ^ 40 * 124604 * 2
def baseEnd_124604 : Nat := 63981743472935719976963

theorem tailTrace_124604 : CollatzResearch.WordTrace tailWord_124604 prefixEnd_124604 63981743472935719976963 := by
  unfold tailWord_124604
  simp only [CollatzResearch.WordTrace]
  refine ⟨2272340620294231757034433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3029787493725642342712577 2272340620294231757034433)
  ·
    refine ⟨1704255465220673817775825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2272340620294231757034433 1704255465220673817775825)
    ·
      refine ⟨1278191598915505363331869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1704255465220673817775825 1278191598915505363331869)
      ·
        refine ⟨479321849593314511249451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1278191598915505363331869 479321849593314511249451)
        ·
          refine ⟨718982774389971766874177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479321849593314511249451 718982774389971766874177)
          ·
            refine ⟨539237080792478825155633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718982774389971766874177 539237080792478825155633)
            ·
              refine ⟨404427810594359118866725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539237080792478825155633 404427810594359118866725)
              ·
                refine ⟨75830214486442334787511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 404427810594359118866725 75830214486442334787511)
                ·
                  refine ⟨113745321729663502181267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75830214486442334787511 113745321729663502181267)
                  ·
                    refine ⟨170617982594495253271901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113745321729663502181267 170617982594495253271901)
                    ·
                      refine ⟨63981743472935719976963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 170617982594495253271901 63981743472935719976963)
                      ·
                        rfl

theorem cell23_124604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_124604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124604 prefixEnd_124604 := by exact prefixLift 124604
  have htrace : WordTrace (prefixWord ++ tailWord_124604) baseStart_124604 baseEnd_124604 := by
    simpa [prefixWord, tailWord_124604, baseEnd_124604] using wordTrace_append hprefix tailTrace_124604
  have hstable : (prefixWord ++ tailWord_124604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124604).length < 2 ^ (prefixWord ++ tailWord_124604).sum := by decide
  have hdescent : baseEnd_124604 < baseStart_124604 := by decide
  rcases family_descends (prefixWord ++ tailWord_124604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124613 : List Nat := [1, 3, 1, 1, 1, 1, 2, 6, 1, 1, 5]
def baseStart_124613 : Nat := 118140960795 + 124613 * 2 ^ 59
def prefixEnd_124613 : Nat := 4983230072969 + 3 ^ 40 * 124613 * 2
def baseEnd_124613 : Nat := 63986364798826184764421

theorem tailTrace_124613 : CollatzResearch.WordTrace tailWord_124613 prefixEnd_124613 63986364798826184764421 := by
  unfold tailWord_124613
  simp only [CollatzResearch.WordTrace]
  refine ⟨4545009497555858051146493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3030006331703905367430995 4545009497555858051146493)
  ·
    refine ⟨1704378561583446769179935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4545009497555858051146493 1704378561583446769179935)
    ·
      refine ⟨2556567842375170153769903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1704378561583446769179935 2556567842375170153769903)
      ·
        refine ⟨3834851763562755230654855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2556567842375170153769903 3834851763562755230654855)
        ·
          refine ⟨5752277645344132845982283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3834851763562755230654855 5752277645344132845982283)
          ·
            refine ⟨8628416468016199268973425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5752277645344132845982283 8628416468016199268973425)
            ·
              refine ⟨6471312351012149451730069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8628416468016199268973425 6471312351012149451730069)
              ·
                refine ⟨303342766453694505549847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6471312351012149451730069 303342766453694505549847)
                ·
                  refine ⟨455014149680541758324771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303342766453694505549847 455014149680541758324771)
                  ·
                    refine ⟨682521224520812637487157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 455014149680541758324771 682521224520812637487157)
                    ·
                      refine ⟨63986364798826184764421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 682521224520812637487157 63986364798826184764421)
                      ·
                        rfl

theorem cell23_124613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_124613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124613 prefixEnd_124613 := by exact prefixLift 124613
  have htrace : WordTrace (prefixWord ++ tailWord_124613) baseStart_124613 baseEnd_124613 := by
    simpa [prefixWord, tailWord_124613, baseEnd_124613] using wordTrace_append hprefix tailTrace_124613
  have hstable : (prefixWord ++ tailWord_124613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124613).length < 2 ^ (prefixWord ++ tailWord_124613).sum := by decide
  have hdescent : baseEnd_124613 < baseStart_124613 := by decide
  rcases family_descends (prefixWord ++ tailWord_124613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124633 : List Nat := [1, 2, 1, 2, 3, 4, 1, 9]
def baseStart_124633 : Nat := 118140960795 + 124633 * 2 ^ 59
def prefixEnd_124633 : Nat := 4983230072969 + 3 ^ 40 * 124633 * 2
def baseEnd_124633 : Nat := 2370245718959855796827

theorem tailTrace_124633 : CollatzResearch.WordTrace tailWord_124633 prefixEnd_124633 2370245718959855796827 := by
  unfold tailWord_124633
  simp only [CollatzResearch.WordTrace]
  refine ⟨4545738957483401466874553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3030492638322267644583035 4545738957483401466874553)
  ·
    refine ⟨3409304218112551100155915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4545738957483401466874553 3409304218112551100155915)
    ·
      refine ⟨5113956327168826650233873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3409304218112551100155915 5113956327168826650233873)
      ·
        refine ⟨3835467245376619987675405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5113956327168826650233873 3835467245376619987675405)
        ·
          refine ⟨1438300217016232495378277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3835467245376619987675405 1438300217016232495378277)
          ·
            refine ⟨269681290690543592883427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1438300217016232495378277 269681290690543592883427)
            ·
              refine ⟨404521936035815389325141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269681290690543592883427 404521936035815389325141)
              ·
                refine ⟨2370245718959855796827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 404521936035815389325141 2370245718959855796827)
                ·
                  rfl

theorem cell23_124633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 9].length) (baseStart_124633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124633 prefixEnd_124633 := by exact prefixLift 124633
  have htrace : WordTrace (prefixWord ++ tailWord_124633) baseStart_124633 baseEnd_124633 := by
    simpa [prefixWord, tailWord_124633, baseEnd_124633] using wordTrace_append hprefix tailTrace_124633
  have hstable : (prefixWord ++ tailWord_124633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124633).length < 2 ^ (prefixWord ++ tailWord_124633).sum := by decide
  have hdescent : baseEnd_124633 < baseStart_124633 := by decide
  rcases family_descends (prefixWord ++ tailWord_124633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124687 : List Nat := [1, 1, 2, 1, 1, 1, 4, 6, 1, 3, 2]
def baseStart_124687 : Nat := 118140960795 + 124687 * 2 ^ 59
def prefixEnd_124687 : Nat := 4983230072969 + 3 ^ 40 * 124687 * 2
def baseEnd_124687 : Nat := 64024362367258895239081

theorem tailTrace_124687 : CollatzResearch.WordTrace tailWord_124687 prefixEnd_124687 64024362367258895239081 := by
  unfold tailWord_124687
  simp only [CollatzResearch.WordTrace]
  refine ⟨4547708499287768689340315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3031805666191845792893543 4547708499287768689340315)
  ·
    refine ⟨6821562748931653034010473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4547708499287768689340315 6821562748931653034010473)
    ·
      refine ⟨5116172061698739775507855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6821562748931653034010473 5116172061698739775507855)
      ·
        refine ⟨7674258092548109663261783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5116172061698739775507855 7674258092548109663261783)
        ·
          refine ⟨11511387138822164494892675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7674258092548109663261783 11511387138822164494892675)
          ·
            refine ⟨17267080708233246742339013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11511387138822164494892675 17267080708233246742339013)
            ·
              refine ⟨3237577632793733764188565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17267080708233246742339013 3237577632793733764188565)
              ·
                refine ⟨151761451537206270196339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3237577632793733764188565 151761451537206270196339)
                ·
                  refine ⟨227642177305809405294509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151761451537206270196339 227642177305809405294509)
                  ·
                    refine ⟨85365816489678526985441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 227642177305809405294509 85365816489678526985441)
                    ·
                      refine ⟨64024362367258895239081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 85365816489678526985441 64024362367258895239081)
                      ·
                        rfl

theorem cell23_124687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 3, 2].length) (baseStart_124687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124687 prefixEnd_124687 := by exact prefixLift 124687
  have htrace : WordTrace (prefixWord ++ tailWord_124687) baseStart_124687 baseEnd_124687 := by
    simpa [prefixWord, tailWord_124687, baseEnd_124687] using wordTrace_append hprefix tailTrace_124687
  have hstable : (prefixWord ++ tailWord_124687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124687).length < 2 ^ (prefixWord ++ tailWord_124687).sum := by decide
  have hdescent : baseEnd_124687 < baseStart_124687 := by decide
  rcases family_descends (prefixWord ++ tailWord_124687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124730 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4]
def baseStart_124730 : Nat := 118140960795 + 124730 * 2 ^ 59
def prefixEnd_124730 : Nat := 4983230072969 + 3 ^ 40 * 124730 * 2
def baseEnd_124730 : Nat := 64046442035402227001383

theorem tailTrace_124730 : CollatzResearch.WordTrace tailWord_124730 prefixEnd_124730 64046442035402227001383 := by
  unfold tailWord_124730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1137319209532996758288911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3032851225421324688770429 1137319209532996758288911)
  ·
    refine ⟨1705978814299495137433367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1137319209532996758288911 1705978814299495137433367)
    ·
      refine ⟨2558968221449242706150051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1705978814299495137433367 2558968221449242706150051)
      ·
        refine ⟨3838452332173864059225077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2558968221449242706150051 3838452332173864059225077)
        ·
          refine ⟨359854906141299755552351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3838452332173864059225077 359854906141299755552351)
          ·
            refine ⟨539782359211949633328527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359854906141299755552351 539782359211949633328527)
            ·
              refine ⟨809673538817924449992791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539782359211949633328527 809673538817924449992791)
              ·
                refine ⟨1214510308226886674989187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809673538817924449992791 1214510308226886674989187)
                ·
                  refine ⟨1821765462340330012483781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1214510308226886674989187 1821765462340330012483781)
                  ·
                    refine ⟨341581024188811877340709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1821765462340330012483781 341581024188811877340709)
                    ·
                      refine ⟨64046442035402227001383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 341581024188811877340709 64046442035402227001383)
                      ·
                        rfl

theorem cell23_124730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_124730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124730 prefixEnd_124730 := by exact prefixLift 124730
  have htrace : WordTrace (prefixWord ++ tailWord_124730) baseStart_124730 baseEnd_124730 := by
    simpa [prefixWord, tailWord_124730, baseEnd_124730] using wordTrace_append hprefix tailTrace_124730
  have hstable : (prefixWord ++ tailWord_124730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124730).length < 2 ^ (prefixWord ++ tailWord_124730).sum := by decide
  have hdescent : baseEnd_124730 < baseStart_124730 := by decide
  rcases family_descends (prefixWord ++ tailWord_124730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124734 : List Nat := [4, 2, 1, 2, 2, 1, 1, 3, 1, 4, 2]
def baseStart_124734 : Nat := 118140960795 + 124734 * 2 ^ 59
def prefixEnd_124734 : Nat := 4983230072969 + 3 ^ 40 * 124734 * 2
def baseEnd_124734 : Nat := 64048495958020211351365

theorem tailTrace_124734 : CollatzResearch.WordTrace tailWord_124734 prefixEnd_124734 64048495958020211351365 := by
  unfold tailWord_124734
  simp only [CollatzResearch.WordTrace]
  refine ⟨568677841264686964537657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3032948486744997144200837 568677841264686964537657)
  ·
    refine ⟨426508380948515223403243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 568677841264686964537657 426508380948515223403243)
    ·
      refine ⟨639762571422772835104865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426508380948515223403243 639762571422772835104865)
      ·
        refine ⟨479821928567079626328649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 639762571422772835104865 479821928567079626328649)
        ·
          refine ⟨359866446425309719746487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479821928567079626328649 359866446425309719746487)
          ·
            refine ⟨539799669637964579619731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359866446425309719746487 539799669637964579619731)
            ·
              refine ⟨809699504456946869429597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539799669637964579619731 809699504456946869429597)
              ·
                refine ⟨303637314171355076036099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 809699504456946869429597 303637314171355076036099)
                ·
                  refine ⟨455455971257032614054149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303637314171355076036099 455455971257032614054149)
                  ·
                    refine ⟨85397994610693615135153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 455455971257032614054149 85397994610693615135153)
                    ·
                      refine ⟨64048495958020211351365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 85397994610693615135153 64048495958020211351365)
                      ·
                        rfl

theorem cell23_124734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_124734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124734 prefixEnd_124734 := by exact prefixLift 124734
  have htrace : WordTrace (prefixWord ++ tailWord_124734) baseStart_124734 baseEnd_124734 := by
    simpa [prefixWord, tailWord_124734, baseEnd_124734] using wordTrace_append hprefix tailTrace_124734
  have hstable : (prefixWord ++ tailWord_124734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124734).length < 2 ^ (prefixWord ++ tailWord_124734).sum := by decide
  have hdescent : baseEnd_124734 < baseStart_124734 := by decide
  rcases family_descends (prefixWord ++ tailWord_124734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124757 : List Nat := [1, 3, 2, 2, 2, 2, 1, 5, 5]
def baseStart_124757 : Nat := 118140960795 + 124757 * 2 ^ 59
def prefixEnd_124757 : Nat := 4983230072969 + 3 ^ 40 * 124757 * 2
def baseEnd_124757 : Nat := 7117811779230402373751

theorem tailTrace_124757 : CollatzResearch.WordTrace tailWord_124757 prefixEnd_124757 7117811779230402373751 := by
  unfold tailWord_124757
  simp only [CollatzResearch.WordTrace]
  refine ⟨4550261609034170644388525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3033507739356113762925683 4550261609034170644388525)
  ·
    refine ⟨1706348103387813991645697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4550261609034170644388525 1706348103387813991645697)
    ·
      refine ⟨1279761077540860493734273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1706348103387813991645697 1279761077540860493734273)
      ·
        refine ⟨959820808155645370300705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1279761077540860493734273 959820808155645370300705)
        ·
          refine ⟨719865606116734027725529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 959820808155645370300705 719865606116734027725529)
          ·
            refine ⟨539899204587550520794147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 719865606116734027725529 539899204587550520794147)
            ·
              refine ⟨809848806881325781191221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539899204587550520794147 809848806881325781191221)
              ·
                refine ⟨75923325645124291986677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 809848806881325781191221 75923325645124291986677)
                ·
                  refine ⟨7117811779230402373751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75923325645124291986677 7117811779230402373751)
                  ·
                    rfl

theorem cell23_124757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 5].length) (baseStart_124757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124757 prefixEnd_124757 := by exact prefixLift 124757
  have htrace : WordTrace (prefixWord ++ tailWord_124757) baseStart_124757 baseEnd_124757 := by
    simpa [prefixWord, tailWord_124757, baseEnd_124757] using wordTrace_append hprefix tailTrace_124757
  have hstable : (prefixWord ++ tailWord_124757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124757).length < 2 ^ (prefixWord ++ tailWord_124757).sum := by decide
  have hdescent : baseEnd_124757 < baseStart_124757 := by decide
  rcases family_descends (prefixWord ++ tailWord_124757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124850 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_124850 : Nat := 118140960795 + 124850 * 2 ^ 59
def prefixEnd_124850 : Nat := 4983230072969 + 3 ^ 40 * 124850 * 2
def baseEnd_124850 : Nat := 64108059713941757500831

theorem tailTrace_124850 : CollatzResearch.WordTrace tailWord_124850 prefixEnd_124850 64108059713941757500831 := by
  unfold tailWord_124850
  simp only [CollatzResearch.WordTrace]
  refine ⟨1138413399424311881881001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3035769065131498351682669 1138413399424311881881001)
  ·
    refine ⟨853810049568233911410751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1138413399424311881881001 853810049568233911410751)
    ·
      refine ⟨1280715074352350867116127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 853810049568233911410751 1280715074352350867116127)
      ·
        refine ⟨1921072611528526300674191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1280715074352350867116127 1921072611528526300674191)
        ·
          refine ⟨2881608917292789451011287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1921072611528526300674191 2881608917292789451011287)
          ·
            refine ⟨4322413375939184176516931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2881608917292789451011287 4322413375939184176516931)
            ·
              refine ⟨6483620063908776264775397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4322413375939184176516931 6483620063908776264775397)
              ·
                refine ⟨1215678761982895549645387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6483620063908776264775397 1215678761982895549645387)
                ·
                  refine ⟨1823518142974343324468081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1215678761982895549645387 1823518142974343324468081)
                  ·
                    refine ⟨1367638607230757493351061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1823518142974343324468081 1367638607230757493351061)
                    ·
                      refine ⟨64108059713941757500831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1367638607230757493351061 64108059713941757500831)
                      ·
                        rfl

theorem cell23_124850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_124850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124850 prefixEnd_124850 := by exact prefixLift 124850
  have htrace : WordTrace (prefixWord ++ tailWord_124850) baseStart_124850 baseEnd_124850 := by
    simpa [prefixWord, tailWord_124850, baseEnd_124850] using wordTrace_append hprefix tailTrace_124850
  have hstable : (prefixWord ++ tailWord_124850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124850).length < 2 ^ (prefixWord ++ tailWord_124850).sum := by decide
  have hdescent : baseEnd_124850 < baseStart_124850 := by decide
  rcases family_descends (prefixWord ++ tailWord_124850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124897 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_124897 : Nat := 118140960795 + 124897 * 2 ^ 59
def prefixEnd_124897 : Nat := 4983230072969 + 3 ^ 40 * 124897 * 2
def baseEnd_124897 : Nat := 64132193304703073613115

theorem tailTrace_124897 : CollatzResearch.WordTrace tailWord_124897 prefixEnd_124897 64132193304703073613115 := by
  unfold tailWord_124897
  simp only [CollatzResearch.WordTrace]
  refine ⟨4555367828526974554484945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3036911885684649702989963 4555367828526974554484945)
  ·
    refine ⟨3416525871395230915863709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4555367828526974554484945 3416525871395230915863709)
    ·
      refine ⟨1281197201773211593448891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3416525871395230915863709 1281197201773211593448891)
      ·
        refine ⟨1921795802659817390173337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1281197201773211593448891 1921795802659817390173337)
        ·
          refine ⟨1441346851994863042630003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1921795802659817390173337 1441346851994863042630003)
          ·
            refine ⟨2162020277992294563945005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441346851994863042630003 2162020277992294563945005)
            ·
              refine ⟨810757604247110461479377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2162020277992294563945005 810757604247110461479377)
              ·
                refine ⟨608068203185332846109533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 810757604247110461479377 608068203185332846109533)
                ·
                  refine ⟨228025576194499817291075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608068203185332846109533 228025576194499817291075)
                  ·
                    refine ⟨342038364291749725936613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 228025576194499817291075 342038364291749725936613)
                    ·
                      refine ⟨64132193304703073613115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 342038364291749725936613 64132193304703073613115)
                      ·
                        rfl

theorem cell23_124897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_124897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124897 prefixEnd_124897 := by exact prefixLift 124897
  have htrace : WordTrace (prefixWord ++ tailWord_124897) baseStart_124897 baseEnd_124897 := by
    simpa [prefixWord, tailWord_124897, baseEnd_124897] using wordTrace_append hprefix tailTrace_124897
  have hstable : (prefixWord ++ tailWord_124897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124897).length < 2 ^ (prefixWord ++ tailWord_124897).sum := by decide
  have hdescent : baseEnd_124897 < baseStart_124897 := by decide
  rcases family_descends (prefixWord ++ tailWord_124897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124920 : List Nat := [2, 1, 2, 1, 1, 3, 2, 11]
def baseStart_124920 : Nat := 118140960795 + 124920 * 2 ^ 59
def prefixEnd_124920 : Nat := 4983230072969 + 3 ^ 40 * 124920 * 2
def baseEnd_124920 : Nat := 2375703828139129023167

theorem tailTrace_124920 : CollatzResearch.WordTrace tailWord_124920 prefixEnd_124920 2375703828139129023167 := by
  unfold tailWord_124920
  simp only [CollatzResearch.WordTrace]
  refine ⟨2278103353721824741286107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3037471138295766321714809 2278103353721824741286107)
  ·
    refine ⟨3417155030582737111929161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2278103353721824741286107 3417155030582737111929161)
    ·
      refine ⟨2562866272937052833946871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3417155030582737111929161 2562866272937052833946871)
      ·
        refine ⟨3844299409405579250920307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2562866272937052833946871 3844299409405579250920307)
        ·
          refine ⟨5766449114108368876380461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3844299409405579250920307 5766449114108368876380461)
          ·
            refine ⟨2162418417790638328642673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5766449114108368876380461 2162418417790638328642673)
            ·
              refine ⟨1621813813342978746482005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2162418417790638328642673 1621813813342978746482005)
              ·
                refine ⟨2375703828139129023167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 1621813813342978746482005 2375703828139129023167)
                ·
                  rfl

theorem cell23_124920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 11].length) (baseStart_124920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124920 prefixEnd_124920 := by exact prefixLift 124920
  have htrace : WordTrace (prefixWord ++ tailWord_124920) baseStart_124920 baseEnd_124920 := by
    simpa [prefixWord, tailWord_124920, baseEnd_124920] using wordTrace_append hprefix tailTrace_124920
  have hstable : (prefixWord ++ tailWord_124920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124920).length < 2 ^ (prefixWord ++ tailWord_124920).sum := by decide
  have hdescent : baseEnd_124920 < baseStart_124920 := by decide
  rcases family_descends (prefixWord ++ tailWord_124920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124947 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 3]
def baseStart_124947 : Nat := 118140960795 + 124947 * 2 ^ 59
def prefixEnd_124947 : Nat := 4983230072969 + 3 ^ 40 * 124947 * 2
def baseEnd_124947 : Nat := 64157867337427877987885

theorem tailTrace_124947 : CollatzResearch.WordTrace tailWord_124947 prefixEnd_124947 64157867337427877987885 := by
  unfold tailWord_124947
  simp only [CollatzResearch.WordTrace]
  refine ⟨4557191478345833093805095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3038127652230555395870063 4557191478345833093805095)
  ·
    refine ⟨6835787217518749640707643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4557191478345833093805095 6835787217518749640707643)
    ·
      refine ⟨10253680826278124461061465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6835787217518749640707643 10253680826278124461061465)
      ·
        refine ⟨7690260619708593345796099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10253680826278124461061465 7690260619708593345796099)
        ·
          refine ⟨11535390929562890018694149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7690260619708593345796099 11535390929562890018694149)
          ·
            refine ⟨2162885799293041878505153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11535390929562890018694149 2162885799293041878505153)
            ·
              refine ⟨1622164349469781408878865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2162885799293041878505153 1622164349469781408878865)
              ·
                refine ⟨1216623262102336056659149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1622164349469781408878865 1216623262102336056659149)
                ·
                  refine ⟨456233723288376021247181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1216623262102336056659149 456233723288376021247181)
                  ·
                    refine ⟨171087646233141007967693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 456233723288376021247181 171087646233141007967693)
                    ·
                      refine ⟨64157867337427877987885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 171087646233141007967693 64157867337427877987885)
                      ·
                        rfl

theorem cell23_124947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 3].length) (baseStart_124947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124947 prefixEnd_124947 := by exact prefixLift 124947
  have htrace : WordTrace (prefixWord ++ tailWord_124947) baseStart_124947 baseEnd_124947 := by
    simpa [prefixWord, tailWord_124947, baseEnd_124947] using wordTrace_append hprefix tailTrace_124947
  have hstable : (prefixWord ++ tailWord_124947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124947).length < 2 ^ (prefixWord ++ tailWord_124947).sum := by decide
  have hdescent : baseEnd_124947 < baseStart_124947 := by decide
  rcases family_descends (prefixWord ++ tailWord_124947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124961 : List Nat := [1, 2, 3, 2, 4, 2, 1, 1, 1, 2, 4]
def baseStart_124961 : Nat := 118140960795 + 124961 * 2 ^ 59
def prefixEnd_124961 : Nat := 4983230072969 + 3 ^ 40 * 124961 * 2
def baseEnd_124961 : Nat := 64165056066590823212821

theorem tailTrace_124961 : CollatzResearch.WordTrace tailWord_124961 prefixEnd_124961 64165056066590823212821 := by
  unfold tailWord_124961
  simp only [CollatzResearch.WordTrace]
  refine ⟨4557702100295113484814737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3038468066863408989876491 4557702100295113484814737)
  ·
    refine ⟨3418276575221335113611053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4557702100295113484814737 3418276575221335113611053)
    ·
      refine ⟨1281853715708000667604145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3418276575221335113611053 1281853715708000667604145)
      ·
        refine ⟨961390286781000500703109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1281853715708000667604145 961390286781000500703109)
        ·
          refine ⟨180260678771437593881833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 961390286781000500703109 180260678771437593881833)
          ·
            refine ⟨135195509078578195411375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180260678771437593881833 135195509078578195411375)
            ·
              refine ⟨202793263617867293117063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135195509078578195411375 202793263617867293117063)
              ·
                refine ⟨304189895426800939675595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202793263617867293117063 304189895426800939675595)
                ·
                  refine ⟨456284843140201409513393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304189895426800939675595 456284843140201409513393)
                  ·
                    refine ⟨342213632355151057135045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 456284843140201409513393 342213632355151057135045)
                    ·
                      refine ⟨64165056066590823212821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 342213632355151057135045 64165056066590823212821)
                      ·
                        rfl

theorem cell23_124961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_124961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124961 prefixEnd_124961 := by exact prefixLift 124961
  have htrace : WordTrace (prefixWord ++ tailWord_124961) baseStart_124961 baseEnd_124961 := by
    simpa [prefixWord, tailWord_124961, baseEnd_124961] using wordTrace_append hprefix tailTrace_124961
  have hstable : (prefixWord ++ tailWord_124961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124961).length < 2 ^ (prefixWord ++ tailWord_124961).sum := by decide
  have hdescent : baseEnd_124961 < baseStart_124961 := by decide
  rcases family_descends (prefixWord ++ tailWord_124961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124977 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 2, 2, 5]
def baseStart_124977 : Nat := 118140960795 + 124977 * 2 ^ 59
def prefixEnd_124977 : Nat := 4983230072969 + 3 ^ 40 * 124977 * 2
def baseEnd_124977 : Nat := 64173271757062760612747

theorem tailTrace_124977 : CollatzResearch.WordTrace tailWord_124977 prefixEnd_124977 64173271757062760612747 := by
  unfold tailWord_124977
  simp only [CollatzResearch.WordTrace]
  refine ⟨4558285668237148217397185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3038857112158098811598123 4558285668237148217397185)
  ·
    refine ⟨3418714251177861163047889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4558285668237148217397185 3418714251177861163047889)
    ·
      refine ⟨2564035688383395872285917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3418714251177861163047889 2564035688383395872285917)
      ·
        refine ⟨961513383143773452107219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2564035688383395872285917 961513383143773452107219)
        ·
          refine ⟨1442270074715660178160829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961513383143773452107219 1442270074715660178160829)
          ·
            refine ⟨540851278018372566810311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1442270074715660178160829 540851278018372566810311)
            ·
              refine ⟨811276917027558850215467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540851278018372566810311 811276917027558850215467)
              ·
                refine ⟨1216915375541338275323201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811276917027558850215467 1216915375541338275323201)
                ·
                  refine ⟨912686531656003706492401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1216915375541338275323201 912686531656003706492401)
                  ·
                    refine ⟨684514898742002779869301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 912686531656003706492401 684514898742002779869301)
                    ·
                      refine ⟨64173271757062760612747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 684514898742002779869301 64173271757062760612747)
                      ·
                        rfl

theorem cell23_124977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_124977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124977 prefixEnd_124977 := by exact prefixLift 124977
  have htrace : WordTrace (prefixWord ++ tailWord_124977) baseStart_124977 baseEnd_124977 := by
    simpa [prefixWord, tailWord_124977, baseEnd_124977] using wordTrace_append hprefix tailTrace_124977
  have hstable : (prefixWord ++ tailWord_124977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124977).length < 2 ^ (prefixWord ++ tailWord_124977).sum := by decide
  have hdescent : baseEnd_124977 < baseStart_124977 := by decide
  rcases family_descends (prefixWord ++ tailWord_124977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124991 : List Nat := [1, 1, 2, 2, 3, 1, 4, 3, 1, 3, 2]
def baseStart_124991 : Nat := 118140960795 + 124991 * 2 ^ 59
def prefixEnd_124991 : Nat := 4983230072969 + 3 ^ 40 * 124991 * 2
def baseEnd_124991 : Nat := 64180460486225705837683

theorem tailTrace_124991 : CollatzResearch.WordTrace tailWord_124991 prefixEnd_124991 64180460486225705837683 := by
  unfold tailWord_124991
  simp only [CollatzResearch.WordTrace]
  refine ⟨4558796290186428608406827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3039197526790952405604551 4558796290186428608406827)
  ·
    refine ⟨6838194435279642912610241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4558796290186428608406827 6838194435279642912610241)
    ·
      refine ⟨5128645826459732184457681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6838194435279642912610241 5128645826459732184457681)
      ·
        refine ⟨3846484369844799138343261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5128645826459732184457681 3846484369844799138343261)
        ·
          refine ⟨1442431638691799676878723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3846484369844799138343261 1442431638691799676878723)
          ·
            refine ⟨2163647458037699515318085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442431638691799676878723 2163647458037699515318085)
            ·
              refine ⟨405683898382068659122141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2163647458037699515318085 405683898382068659122141)
              ·
                refine ⟨152131461893275747170803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405683898382068659122141 152131461893275747170803)
                ·
                  refine ⟨228197192839913620756205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152131461893275747170803 228197192839913620756205)
                  ·
                    refine ⟨85573947314967607783577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 228197192839913620756205 85573947314967607783577)
                    ·
                      refine ⟨64180460486225705837683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 85573947314967607783577 64180460486225705837683)
                      ·
                        rfl

theorem cell23_124991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 3, 2].length) (baseStart_124991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124991 prefixEnd_124991 := by exact prefixLift 124991
  have htrace : WordTrace (prefixWord ++ tailWord_124991) baseStart_124991 baseEnd_124991 := by
    simpa [prefixWord, tailWord_124991, baseEnd_124991] using wordTrace_append hprefix tailTrace_124991
  have hstable : (prefixWord ++ tailWord_124991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124991).length < 2 ^ (prefixWord ++ tailWord_124991).sum := by decide
  have hdescent : baseEnd_124991 < baseStart_124991 := by decide
  rcases family_descends (prefixWord ++ tailWord_124991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_124998 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_124998 : Nat := 118140960795 + 124998 * 2 ^ 59
def prefixEnd_124998 : Nat := 4983230072969 + 3 ^ 40 * 124998 * 2
def baseEnd_124998 : Nat := 64184054850807178450151

theorem tailTrace_124998 : CollatzResearch.WordTrace tailWord_124998 prefixEnd_124998 64184054850807178450151 := by
  unfold tailWord_124998
  simp only [CollatzResearch.WordTrace]
  refine ⟨142470362536283400122239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3039367734107379202607765 142470362536283400122239)
  ·
    refine ⟨213705543804425100183359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142470362536283400122239 213705543804425100183359)
    ·
      refine ⟨320558315706637650275039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213705543804425100183359 320558315706637650275039)
      ·
        refine ⟨480837473559956475412559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320558315706637650275039 480837473559956475412559)
        ·
          refine ⟨721256210339934713118839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480837473559956475412559 721256210339934713118839)
          ·
            refine ⟨1081884315509902069678259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721256210339934713118839 1081884315509902069678259)
            ·
              refine ⟨1622826473264853104517389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081884315509902069678259 1622826473264853104517389)
              ·
                refine ⟨608559927474319914194021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1622826473264853104517389 608559927474319914194021)
                ·
                  refine ⟨114104986401434983911379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 608559927474319914194021 114104986401434983911379)
                  ·
                    refine ⟨171157479602152475867069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114104986401434983911379 171157479602152475867069)
                    ·
                      refine ⟨64184054850807178450151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 171157479602152475867069 64184054850807178450151)
                      ·
                        rfl

theorem cell23_124998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_124998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_124998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_124998 prefixEnd_124998 := by exact prefixLift 124998
  have htrace : WordTrace (prefixWord ++ tailWord_124998) baseStart_124998 baseEnd_124998 := by
    simpa [prefixWord, tailWord_124998, baseEnd_124998] using wordTrace_append hprefix tailTrace_124998
  have hstable : (prefixWord ++ tailWord_124998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_124998).length < 2 ^ (prefixWord ++ tailWord_124998).sum := by decide
  have hdescent : baseEnd_124998 < baseStart_124998 := by decide
  rcases family_descends (prefixWord ++ tailWord_124998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125007 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 3]
def baseStart_125007 : Nat := 118140960795 + 125007 * 2 ^ 59
def prefixEnd_125007 : Nat := 4983230072969 + 3 ^ 40 * 125007 * 2
def baseEnd_125007 : Nat := 64188676176697643237609

theorem tailTrace_125007 : CollatzResearch.WordTrace tailWord_125007 prefixEnd_125007 64188676176697643237609 := by
  unfold tailWord_125007
  simp only [CollatzResearch.WordTrace]
  refine ⟨4559379858128463340989275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3039586572085642227326183 4559379858128463340989275)
  ·
    refine ⟨6839069787192695011483913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4559379858128463340989275 6839069787192695011483913)
    ·
      refine ⟨5129302340394521258612935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6839069787192695011483913 5129302340394521258612935)
      ·
        refine ⟨7693953510591781887919403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5129302340394521258612935 7693953510591781887919403)
        ·
          refine ⟨11540930265887672831879105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7693953510591781887919403 11540930265887672831879105)
          ·
            refine ⟨8655697699415754623909329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11540930265887672831879105 8655697699415754623909329)
            ·
              refine ⟨6491773274561815967931997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8655697699415754623909329 6491773274561815967931997)
              ·
                refine ⟨2434414977960680987974499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6491773274561815967931997 2434414977960680987974499)
                ·
                  refine ⟨3651622466941021481961749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2434414977960680987974499 3651622466941021481961749)
                  ·
                    refine ⟨171169803137860381966957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3651622466941021481961749 171169803137860381966957)
                    ·
                      refine ⟨64188676176697643237609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 171169803137860381966957 64188676176697643237609)
                      ·
                        rfl

theorem cell23_125007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 3].length) (baseStart_125007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125007 prefixEnd_125007 := by exact prefixLift 125007
  have htrace : WordTrace (prefixWord ++ tailWord_125007) baseStart_125007 baseEnd_125007 := by
    simpa [prefixWord, tailWord_125007, baseEnd_125007] using wordTrace_append hprefix tailTrace_125007
  have hstable : (prefixWord ++ tailWord_125007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125007).length < 2 ^ (prefixWord ++ tailWord_125007).sum := by decide
  have hdescent : baseEnd_125007 < baseStart_125007 := by decide
  rcases family_descends (prefixWord ++ tailWord_125007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125017 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 1, 4, 4]
def baseStart_125017 : Nat := 118140960795 + 125017 * 2 ^ 59
def prefixEnd_125017 : Nat := 4983230072969 + 3 ^ 40 * 125017 * 2
def baseEnd_125017 : Nat := 64193810983242604112563

theorem tailTrace_125017 : CollatzResearch.WordTrace tailWord_125017 prefixEnd_125017 64193810983242604112563 := by
  unfold tailWord_125017
  simp only [CollatzResearch.WordTrace]
  refine ⟨4559744588092235048853305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3039829725394823365902203 4559744588092235048853305)
  ·
    refine ⟨3419808441069176286639979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4559744588092235048853305 3419808441069176286639979)
    ·
      refine ⟨5129712661603764429959969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3419808441069176286639979 5129712661603764429959969)
      ·
        refine ⟨3847284496202823322469977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5129712661603764429959969 3847284496202823322469977)
        ·
          refine ⟨2885463372152117491852483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3847284496202823322469977 2885463372152117491852483)
          ·
            refine ⟨4328195058228176237778725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885463372152117491852483 4328195058228176237778725)
            ·
              refine ⟨811536573417783044583511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4328195058228176237778725 811536573417783044583511)
              ·
                refine ⟨1217304860126674566875267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811536573417783044583511 1217304860126674566875267)
                ·
                  refine ⟨1825957290190011850312901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1217304860126674566875267 1825957290190011850312901)
                  ·
                    refine ⟨342366991910627221933669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1825957290190011850312901 342366991910627221933669)
                    ·
                      refine ⟨64193810983242604112563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 342366991910627221933669 64193810983242604112563)
                      ·
                        rfl

theorem cell23_125017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_125017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125017 prefixEnd_125017 := by exact prefixLift 125017
  have htrace : WordTrace (prefixWord ++ tailWord_125017) baseStart_125017 baseEnd_125017 := by
    simpa [prefixWord, tailWord_125017, baseEnd_125017] using wordTrace_append hprefix tailTrace_125017
  have hstable : (prefixWord ++ tailWord_125017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125017).length < 2 ^ (prefixWord ++ tailWord_125017).sum := by decide
  have hdescent : baseEnd_125017 < baseStart_125017 := by decide
  rcases family_descends (prefixWord ++ tailWord_125017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125027 : List Nat := [1, 1, 1, 5, 1, 1, 2, 4, 7]
def baseStart_125027 : Nat := 118140960795 + 125027 * 2 ^ 59
def prefixEnd_125027 : Nat := 4983230072969 + 3 ^ 40 * 125027 * 2
def baseEnd_125027 : Nat := 7133216198865284998613

theorem tailTrace_125027 : CollatzResearch.WordTrace tailWord_125027 prefixEnd_125027 7133216198865284998613 := by
  unfold tailWord_125027
  simp only [CollatzResearch.WordTrace]
  refine ⟨4560109318056006756717335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3040072878704004504478223 4560109318056006756717335)
  ·
    refine ⟨6840163977084010135076003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4560109318056006756717335 6840163977084010135076003)
    ·
      refine ⟨10260245965626015202614005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6840163977084010135076003 10260245965626015202614005)
      ·
        refine ⟨961898059277438925245063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10260245965626015202614005 961898059277438925245063)
        ·
          refine ⟨1442847088916158387867595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961898059277438925245063 1442847088916158387867595)
          ·
            refine ⟨2164270633374237581801393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442847088916158387867595 2164270633374237581801393)
            ·
              refine ⟨1623202975030678186351045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2164270633374237581801393 1623202975030678186351045)
              ·
                refine ⟨304350557818252159940821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1623202975030678186351045 304350557818252159940821)
                ·
                  refine ⟨7133216198865284998613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 304350557818252159940821 7133216198865284998613)
                  ·
                    rfl

theorem cell23_125027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 7].length) (baseStart_125027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125027 prefixEnd_125027 := by exact prefixLift 125027
  have htrace : WordTrace (prefixWord ++ tailWord_125027) baseStart_125027 baseEnd_125027 := by
    simpa [prefixWord, tailWord_125027, baseEnd_125027] using wordTrace_append hprefix tailTrace_125027
  have hstable : (prefixWord ++ tailWord_125027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125027).length < 2 ^ (prefixWord ++ tailWord_125027).sum := by decide
  have hdescent : baseEnd_125027 < baseStart_125027 := by decide
  rcases family_descends (prefixWord ++ tailWord_125027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125061 : List Nat := [1, 3, 1, 1, 5, 2, 1, 4, 5]
def baseStart_125061 : Nat := 118140960795 + 125061 * 2 ^ 59
def prefixEnd_125061 : Nat := 4983230072969 + 3 ^ 40 * 125061 * 2
def baseEnd_125061 : Nat := 7135156014671159106929

theorem tailTrace_125061 : CollatzResearch.WordTrace tailWord_125061 prefixEnd_125061 7135156014671159106929 := by
  unfold tailWord_125061
  simp only [CollatzResearch.WordTrace]
  refine ⟨4561349399932830563455037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3040899599955220375636691 4561349399932830563455037)
  ·
    refine ⟨1710506024974811461295639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4561349399932830563455037 1710506024974811461295639)
    ·
      refine ⟨2565759037462217191943459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1710506024974811461295639 2565759037462217191943459)
      ·
        refine ⟨3848638556193325787915189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2565759037462217191943459 3848638556193325787915189)
        ·
          refine ⟨360809864643124292617049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3848638556193325787915189 360809864643124292617049)
          ·
            refine ⟨270607398482343219462787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360809864643124292617049 270607398482343219462787)
            ·
              refine ⟨405911097723514829194181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270607398482343219462787 405911097723514829194181)
              ·
                refine ⟨76108330823159030473909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405911097723514829194181 76108330823159030473909)
                ·
                  refine ⟨7135156014671159106929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76108330823159030473909 7135156014671159106929)
                  ·
                    rfl

theorem cell23_125061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 5].length) (baseStart_125061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125061 prefixEnd_125061 := by exact prefixLift 125061
  have htrace : WordTrace (prefixWord ++ tailWord_125061) baseStart_125061 baseEnd_125061 := by
    simpa [prefixWord, tailWord_125061, baseEnd_125061] using wordTrace_append hprefix tailTrace_125061
  have hstable : (prefixWord ++ tailWord_125061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125061).length < 2 ^ (prefixWord ++ tailWord_125061).sum := by decide
  have hdescent : baseEnd_125061 < baseStart_125061 := by decide
  rcases family_descends (prefixWord ++ tailWord_125061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125074 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 1, 7]
def baseStart_125074 : Nat := 118140960795 + 125074 * 2 ^ 59
def prefixEnd_125074 : Nat := 4983230072969 + 3 ^ 40 * 125074 * 2
def baseEnd_125074 : Nat := 21407693126849627033267

theorem tailTrace_125074 : CollatzResearch.WordTrace tailWord_125074 prefixEnd_125074 21407693126849627033267 := by
  unfold tailWord_125074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1140455887221433445919569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3041215699257155855785517 1140455887221433445919569)
  ·
    refine ⟨855341915416075084439677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1140455887221433445919569 855341915416075084439677)
    ·
      refine ⟨320753218281028156664879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 855341915416075084439677 320753218281028156664879)
      ·
        refine ⟨481129827421542234997319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320753218281028156664879 481129827421542234997319)
        ·
          refine ⟨721694741132313352495979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481129827421542234997319 721694741132313352495979)
          ·
            refine ⟨1082542111698470028743969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721694741132313352495979 1082542111698470028743969)
            ·
              refine ⟨811906583773852521557977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1082542111698470028743969 811906583773852521557977)
              ·
                refine ⟨608929937830389391168483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811906583773852521557977 608929937830389391168483)
                ·
                  refine ⟨913394906745584086752725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 608929937830389391168483 913394906745584086752725)
                  ·
                    refine ⟨21407693126849627033267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 913394906745584086752725 21407693126849627033267)
                    ·
                      rfl

theorem cell23_125074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_125074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125074 prefixEnd_125074 := by exact prefixLift 125074
  have htrace : WordTrace (prefixWord ++ tailWord_125074) baseStart_125074 baseEnd_125074 := by
    simpa [prefixWord, tailWord_125074, baseEnd_125074] using wordTrace_append hprefix tailTrace_125074
  have hstable : (prefixWord ++ tailWord_125074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125074).length < 2 ^ (prefixWord ++ tailWord_125074).sum := by decide
  have hdescent : baseEnd_125074 < baseStart_125074 := by decide
  rcases family_descends (prefixWord ++ tailWord_125074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125111 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 2, 4, 2]
def baseStart_125111 : Nat := 118140960795 + 125111 * 2 ^ 59
def prefixEnd_125111 : Nat := 4983230072969 + 3 ^ 40 * 125111 * 2
def baseEnd_125111 : Nat := 64242078164765236337131

theorem tailTrace_125111 : CollatzResearch.WordTrace tailWord_125111 prefixEnd_125111 64242078164765236337131 := by
  unfold tailWord_125111
  simp only [CollatzResearch.WordTrace]
  refine ⟨4563173049751689102775187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3042115366501126068516791 4563173049751689102775187)
  ·
    refine ⟨6844759574627533654162781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4563173049751689102775187 6844759574627533654162781)
    ·
      refine ⟨2566784840485325120311043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6844759574627533654162781 2566784840485325120311043)
      ·
        refine ⟨3850177260727987680466565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2566784840485325120311043 3850177260727987680466565)
        ·
          refine ⟨721908236386497690087481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3850177260727987680466565 721908236386497690087481)
          ·
            refine ⟨541431177289873267565611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 721908236386497690087481 541431177289873267565611)
            ·
              refine ⟨812146765934809901348417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541431177289873267565611 812146765934809901348417)
              ·
                refine ⟨609110074451107426011313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 812146765934809901348417 609110074451107426011313)
                ·
                  refine ⟨456832555838330569508485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609110074451107426011313 456832555838330569508485)
                  ·
                    refine ⟨85656104219686981782841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 456832555838330569508485 85656104219686981782841)
                    ·
                      refine ⟨64242078164765236337131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 85656104219686981782841 64242078164765236337131)
                      ·
                        rfl

theorem cell23_125111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 4, 2].length) (baseStart_125111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125111 prefixEnd_125111 := by exact prefixLift 125111
  have htrace : WordTrace (prefixWord ++ tailWord_125111) baseStart_125111 baseEnd_125111 := by
    simpa [prefixWord, tailWord_125111, baseEnd_125111] using wordTrace_append hprefix tailTrace_125111
  have hstable : (prefixWord ++ tailWord_125111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125111).length < 2 ^ (prefixWord ++ tailWord_125111).sum := by decide
  have hdescent : baseEnd_125111 < baseStart_125111 := by decide
  rcases family_descends (prefixWord ++ tailWord_125111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125178 : List Nat := [3, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3]
def baseStart_125178 : Nat := 118140960795 + 125178 * 2 ^ 59
def prefixEnd_125178 : Nat := 4983230072969 + 3 ^ 40 * 125178 * 2
def baseEnd_125178 : Nat := 64276481368616474199323

theorem tailTrace_125178 : CollatzResearch.WordTrace tailWord_125178 prefixEnd_125178 64276481368616474199323 := by
  unfold tailWord_125178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1141404185127239886366047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3043744493672639696976125 1141404185127239886366047)
  ·
    refine ⟨1712106277690859829549071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1141404185127239886366047 1712106277690859829549071)
    ·
      refine ⟨2568159416536289744323607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1712106277690859829549071 2568159416536289744323607)
      ·
        refine ⟨3852239124804434616485411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2568159416536289744323607 3852239124804434616485411)
        ·
          refine ⟨5778358687206651924728117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3852239124804434616485411 5778358687206651924728117)
          ·
            refine ⟨541721126925623617943261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5778358687206651924728117 541721126925623617943261)
            ·
              refine ⟨203145422597108856728723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 541721126925623617943261 203145422597108856728723)
              ·
                refine ⟨304718133895663285093085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203145422597108856728723 304718133895663285093085)
                ·
                  refine ⟨114269300210873731909907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304718133895663285093085 114269300210873731909907)
                  ·
                    refine ⟨171403950316310597864861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114269300210873731909907 171403950316310597864861)
                    ·
                      refine ⟨64276481368616474199323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 171403950316310597864861 64276481368616474199323)
                      ·
                        rfl

theorem cell23_125178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3].length) (baseStart_125178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125178 prefixEnd_125178 := by exact prefixLift 125178
  have htrace : WordTrace (prefixWord ++ tailWord_125178) baseStart_125178 baseEnd_125178 := by
    simpa [prefixWord, tailWord_125178, baseEnd_125178] using wordTrace_append hprefix tailTrace_125178
  have hstable : (prefixWord ++ tailWord_125178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125178).length < 2 ^ (prefixWord ++ tailWord_125178).sum := by decide
  have hdescent : baseEnd_125178 < baseStart_125178 := by decide
  rcases family_descends (prefixWord ++ tailWord_125178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125201 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 4]
def baseStart_125201 : Nat := 118140960795 + 125201 * 2 ^ 59
def prefixEnd_125201 : Nat := 4983230072969 + 3 ^ 40 * 125201 * 2
def baseEnd_125201 : Nat := 64288291423669884211717

theorem tailTrace_125201 : CollatzResearch.WordTrace tailWord_125201 prefixEnd_125201 64288291423669884211717 := by
  unfold tailWord_125201
  simp only [CollatzResearch.WordTrace]
  refine ⟨4566455619425634473551457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3044303746283756315700971 4566455619425634473551457)
  ·
    refine ⟨3424841714569225855163593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4566455619425634473551457 3424841714569225855163593)
    ·
      refine ⟨2568631285926919391372695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3424841714569225855163593 2568631285926919391372695)
      ·
        refine ⟨3852946928890379087059043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2568631285926919391372695 3852946928890379087059043)
        ·
          refine ⟨5779420393335568630588565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3852946928890379087059043 5779420393335568630588565)
          ·
            refine ⟨270910330937604779558839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5779420393335568630588565 270910330937604779558839)
            ·
              refine ⟨406365496406407169338259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270910330937604779558839 406365496406407169338259)
              ·
                refine ⟨609548244609610754007389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406365496406407169338259 609548244609610754007389)
                ·
                  refine ⟨228580591728604032752771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 609548244609610754007389 228580591728604032752771)
                  ·
                    refine ⟨342870887592906049129157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 228580591728604032752771 342870887592906049129157)
                    ·
                      refine ⟨64288291423669884211717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 342870887592906049129157 64288291423669884211717)
                      ·
                        rfl

theorem cell23_125201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_125201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125201 prefixEnd_125201 := by exact prefixLift 125201
  have htrace : WordTrace (prefixWord ++ tailWord_125201) baseStart_125201 baseEnd_125201 := by
    simpa [prefixWord, tailWord_125201, baseEnd_125201] using wordTrace_append hprefix tailTrace_125201
  have hstable : (prefixWord ++ tailWord_125201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125201).length < 2 ^ (prefixWord ++ tailWord_125201).sum := by decide
  have hdescent : baseEnd_125201 < baseStart_125201 := by decide
  rcases family_descends (prefixWord ++ tailWord_125201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125223 : List Nat := [1, 1, 8, 1, 2, 1, 2, 2, 1, 4]
def baseStart_125223 : Nat := 118140960795 + 125223 * 2 ^ 59
def prefixEnd_125223 : Nat := 4983230072969 + 3 ^ 40 * 125223 * 2
def baseEnd_125223 : Nat := 21433195999356266045539

theorem tailTrace_125223 : CollatzResearch.WordTrace tailWord_125223 prefixEnd_125223 21433195999356266045539 := by
  unfold tailWord_125223
  simp only [CollatzResearch.WordTrace]
  refine ⟨4567258025345932230852323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3044838683563954820568215 4567258025345932230852323)
  ·
    refine ⟨6850887038018898346278485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4567258025345932230852323 6850887038018898346278485)
    ·
      refine ⟨80283832476783964995451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 6850887038018898346278485 80283832476783964995451)
      ·
        refine ⟨120425748715175947493177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80283832476783964995451 120425748715175947493177)
        ·
          refine ⟨90319311536381960619883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120425748715175947493177 90319311536381960619883)
          ·
            refine ⟨135478967304572940929825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90319311536381960619883 135478967304572940929825)
            ·
              refine ⟨101609225478429705697369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135478967304572940929825 101609225478429705697369)
              ·
                refine ⟨76206919108822279273027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101609225478429705697369 76206919108822279273027)
                ·
                  refine ⟨114310378663233418909541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76206919108822279273027 114310378663233418909541)
                  ·
                    refine ⟨21433195999356266045539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114310378663233418909541 21433195999356266045539)
                    ·
                      rfl

theorem cell23_125223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_125223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125223 prefixEnd_125223 := by exact prefixLift 125223
  have htrace : WordTrace (prefixWord ++ tailWord_125223) baseStart_125223 baseEnd_125223 := by
    simpa [prefixWord, tailWord_125223, baseEnd_125223] using wordTrace_append hprefix tailTrace_125223
  have hstable : (prefixWord ++ tailWord_125223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125223).length < 2 ^ (prefixWord ++ tailWord_125223).sum := by decide
  have hdescent : baseEnd_125223 < baseStart_125223 := by decide
  rcases family_descends (prefixWord ++ tailWord_125223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125224 : List Nat := [2, 1, 5, 1, 14]
def baseStart_125224 : Nat := 118140960795 + 125224 * 2 ^ 59
def prefixEnd_125224 : Nat := 4983230072969 + 3 ^ 40 * 125224 * 2
def baseEnd_125224 : Nat := 88203157035285725959

theorem tailTrace_125224 : CollatzResearch.WordTrace tailWord_125224 prefixEnd_125224 88203157035285725959 := by
  unfold tailWord_125224
  simp only [CollatzResearch.WordTrace]
  refine ⟨2283647249171154700819363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3044862998894872934425817 2283647249171154700819363)
  ·
    refine ⟨3425470873756732051229045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2283647249171154700819363 3425470873756732051229045)
    ·
      refine ⟨321137894414693629802723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3425470873756732051229045 321137894414693629802723)
      ·
        refine ⟨481706841622040444704085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321137894414693629802723 481706841622040444704085)
        ·
          refine ⟨88203157035285725959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 481706841622040444704085 88203157035285725959)
          ·
            rfl

theorem cell23_125224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 14].length) (baseStart_125224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125224 prefixEnd_125224 := by exact prefixLift 125224
  have htrace : WordTrace (prefixWord ++ tailWord_125224) baseStart_125224 baseEnd_125224 := by
    simpa [prefixWord, tailWord_125224, baseEnd_125224] using wordTrace_append hprefix tailTrace_125224
  have hstable : (prefixWord ++ tailWord_125224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125224).length < 2 ^ (prefixWord ++ tailWord_125224).sum := by decide
  have hdescent : baseEnd_125224 < baseStart_125224 := by decide
  rcases family_descends (prefixWord ++ tailWord_125224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125229 : List Nat := [1, 5, 3, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_125229 : Nat := 118140960795 + 125229 * 2 ^ 59
def prefixEnd_125229 : Nat := 4983230072969 + 3 ^ 40 * 125229 * 2
def baseEnd_125229 : Nat := 64302668881995774661589

theorem tailTrace_125229 : CollatzResearch.WordTrace tailWord_125229 prefixEnd_125229 64302668881995774661589 := by
  unfold tailWord_125229
  simp only [CollatzResearch.WordTrace]
  refine ⟨4567476863324195255570741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3044984575549463503713827 4567476863324195255570741)
  ·
    refine ⟨428200955936643305209757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4567476863324195255570741 428200955936643305209757)
    ·
      refine ⟨160575358476241239453659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428200955936643305209757 160575358476241239453659)
      ·
        refine ⟨240863037714361859180489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160575358476241239453659 240863037714361859180489)
        ·
          refine ⟨180647278285771394385367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240863037714361859180489 180647278285771394385367)
          ·
            refine ⟨270970917428657091578051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180647278285771394385367 270970917428657091578051)
            ·
              refine ⟨406456376142985637367077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270970917428657091578051 406456376142985637367077)
              ·
                refine ⟨76210570526809807006327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 406456376142985637367077 76210570526809807006327)
                ·
                  refine ⟨114315855790214710509491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76210570526809807006327 114315855790214710509491)
                  ·
                    refine ⟨171473783685322065764237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114315855790214710509491 171473783685322065764237)
                    ·
                      refine ⟨64302668881995774661589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 171473783685322065764237 64302668881995774661589)
                      ·
                        rfl

theorem cell23_125229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_125229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125229 prefixEnd_125229 := by exact prefixLift 125229
  have htrace : WordTrace (prefixWord ++ tailWord_125229) baseStart_125229 baseEnd_125229 := by
    simpa [prefixWord, tailWord_125229, baseEnd_125229] using wordTrace_append hprefix tailTrace_125229
  have hstable : (prefixWord ++ tailWord_125229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125229).length < 2 ^ (prefixWord ++ tailWord_125229).sum := by decide
  have hdescent : baseEnd_125229 < baseStart_125229 := by decide
  rcases family_descends (prefixWord ++ tailWord_125229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125241 : List Nat := [1, 2, 1, 6, 1, 1, 3, 8]
def baseStart_125241 : Nat := 118140960795 + 125241 * 2 ^ 59
def prefixEnd_125241 : Nat := 4983230072969 + 3 ^ 40 * 125241 * 2
def baseEnd_125241 : Nat := 2381808542587026952279

theorem tailTrace_125241 : CollatzResearch.WordTrace tailWord_125241 prefixEnd_125241 2381808542587026952279 := by
  unfold tailWord_125241
  simp only [CollatzResearch.WordTrace]
  refine ⟨4567914539280721305007577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3045276359520480870005051 4567914539280721305007577)
  ·
    refine ⟨3425935904460540978755683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4567914539280721305007577 3425935904460540978755683)
    ·
      refine ⟨5138903856690811468133525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3425935904460540978755683 5138903856690811468133525)
      ·
        refine ⟨240886118282381787568759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5138903856690811468133525 240886118282381787568759)
        ·
          refine ⟨361329177423572681353139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240886118282381787568759 361329177423572681353139)
          ·
            refine ⟨541993766135359022029709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361329177423572681353139 541993766135359022029709)
            ·
              refine ⟨203247662300759633261141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 541993766135359022029709 203247662300759633261141)
              ·
                refine ⟨2381808542587026952279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 203247662300759633261141 2381808542587026952279)
                ·
                  rfl

theorem cell23_125241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 8].length) (baseStart_125241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125241 prefixEnd_125241 := by exact prefixLift 125241
  have htrace : WordTrace (prefixWord ++ tailWord_125241) baseStart_125241 baseEnd_125241 := by
    simpa [prefixWord, tailWord_125241, baseEnd_125241] using wordTrace_append hprefix tailTrace_125241
  have hstable : (prefixWord ++ tailWord_125241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125241).length < 2 ^ (prefixWord ++ tailWord_125241).sum := by decide
  have hdescent : baseEnd_125241 < baseStart_125241 := by decide
  rcases family_descends (prefixWord ++ tailWord_125241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125251 : List Nat := [1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 3]
def baseStart_125251 : Nat := 118140960795 + 125251 * 2 ^ 59
def prefixEnd_125251 : Nat := 4983230072969 + 3 ^ 40 * 125251 * 2
def baseEnd_125251 : Nat := 64313965456394688586487

theorem tailTrace_125251 : CollatzResearch.WordTrace tailWord_125251 prefixEnd_125251 64313965456394688586487 := by
  unfold tailWord_125251
  simp only [CollatzResearch.WordTrace]
  refine ⟨4568279269244493012871607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3045519512829662008581071 4568279269244493012871607)
  ·
    refine ⟨6852418903866739519307411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4568279269244493012871607 6852418903866739519307411)
    ·
      refine ⟨10278628355800109278961117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6852418903866739519307411 10278628355800109278961117)
      ·
        refine ⟨3854485633425040979610419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10278628355800109278961117 3854485633425040979610419)
        ·
          refine ⟨5781728450137561469415629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3854485633425040979610419 5781728450137561469415629)
          ·
            refine ⟨2168148168801585551030861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5781728450137561469415629 2168148168801585551030861)
            ·
              refine ⟨813055563300594581636573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2168148168801585551030861 813055563300594581636573)
              ·
                refine ⟨304895836237722968113715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 813055563300594581636573 304895836237722968113715)
                ·
                  refine ⟨457343754356584452170573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304895836237722968113715 457343754356584452170573)
                  ·
                    refine ⟨171503907883719169563965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 457343754356584452170573 171503907883719169563965)
                    ·
                      refine ⟨64313965456394688586487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 171503907883719169563965 64313965456394688586487)
                      ·
                        rfl

theorem cell23_125251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_125251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125251 prefixEnd_125251 := by exact prefixLift 125251
  have htrace : WordTrace (prefixWord ++ tailWord_125251) baseStart_125251 baseEnd_125251 := by
    simpa [prefixWord, tailWord_125251, baseEnd_125251] using wordTrace_append hprefix tailTrace_125251
  have hstable : (prefixWord ++ tailWord_125251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125251).length < 2 ^ (prefixWord ++ tailWord_125251).sum := by decide
  have hdescent : baseEnd_125251 < baseStart_125251 := by decide
  rcases family_descends (prefixWord ++ tailWord_125251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125268 : List Nat := [2, 4, 1, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_125268 : Nat := 118140960795 + 125268 * 2 ^ 59
def prefixEnd_125268 : Nat := 4983230072969 + 3 ^ 40 * 125268 * 2
def baseEnd_125268 : Nat := 64322694627521122073909

theorem tailTrace_125268 : CollatzResearch.WordTrace tailWord_125268 prefixEnd_125268 64322694627521122073909 := by
  unfold tailWord_125268
  simp only [CollatzResearch.WordTrace]
  refine ⟨2284449655091452458120229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3045932873455269944160305 2284449655091452458120229)
  ·
    refine ⟨428334310329647335897543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2284449655091452458120229 428334310329647335897543)
    ·
      refine ⟨642501465494471003846315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428334310329647335897543 642501465494471003846315)
      ·
        refine ⟨963752198241706505769473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642501465494471003846315 963752198241706505769473)
        ·
          refine ⟨722814148681279879327105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 963752198241706505769473 722814148681279879327105)
          ·
            refine ⟨542110611510959909495329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722814148681279879327105 542110611510959909495329)
            ·
              refine ⟨406582958633219932121497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542110611510959909495329 406582958633219932121497)
              ·
                refine ⟨304937218974914949091123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406582958633219932121497 304937218974914949091123)
                ·
                  refine ⟨457405828462372423636685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304937218974914949091123 457405828462372423636685)
                  ·
                    refine ⟨171527185673389658863757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 457405828462372423636685 171527185673389658863757)
                    ·
                      refine ⟨64322694627521122073909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 171527185673389658863757 64322694627521122073909)
                      ·
                        rfl

theorem cell23_125268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_125268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125268 prefixEnd_125268 := by exact prefixLift 125268
  have htrace : WordTrace (prefixWord ++ tailWord_125268) baseStart_125268 baseEnd_125268 := by
    simpa [prefixWord, tailWord_125268, baseEnd_125268] using wordTrace_append hprefix tailTrace_125268
  have hstable : (prefixWord ++ tailWord_125268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125268).length < 2 ^ (prefixWord ++ tailWord_125268).sum := by decide
  have hdescent : baseEnd_125268 < baseStart_125268 := by decide
  rcases family_descends (prefixWord ++ tailWord_125268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125269 : List Nat := [1, 3, 2, 2, 4, 1, 2, 3, 1, 2, 2]
def baseStart_125269 : Nat := 118140960795 + 125269 * 2 ^ 59
def prefixEnd_125269 : Nat := 4983230072969 + 3 ^ 40 * 125269 * 2
def baseEnd_125269 : Nat := 64323208108175618161405

theorem tailTrace_125269 : CollatzResearch.WordTrace tailWord_125269 prefixEnd_125269 64323208108175618161405 := by
  unfold tailWord_125269
  simp only [CollatzResearch.WordTrace]
  refine ⟨4568935783179282087026861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3045957188786188058017907 4568935783179282087026861)
  ·
    refine ⟨1713350918692230782635073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4568935783179282087026861 1713350918692230782635073)
    ·
      refine ⟨1285013189019173086976305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1713350918692230782635073 1285013189019173086976305)
      ·
        refine ⟨963759891764379815232229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1285013189019173086976305 963759891764379815232229)
        ·
          refine ⟨180704979705821215356043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 963759891764379815232229 180704979705821215356043)
          ·
            refine ⟨271057469558731823034065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180704979705821215356043 271057469558731823034065)
            ·
              refine ⟨203293102169048867275549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271057469558731823034065 203293102169048867275549)
              ·
                refine ⟨76234913313393325228331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203293102169048867275549 76234913313393325228331)
                ·
                  refine ⟨114352369970089987842497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76234913313393325228331 114352369970089987842497)
                  ·
                    refine ⟨85764277477567490881873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114352369970089987842497 85764277477567490881873)
                    ·
                      refine ⟨64323208108175618161405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 85764277477567490881873 64323208108175618161405)
                      ·
                        rfl

theorem cell23_125269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_125269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125269 prefixEnd_125269 := by exact prefixLift 125269
  have htrace : WordTrace (prefixWord ++ tailWord_125269) baseStart_125269 baseEnd_125269 := by
    simpa [prefixWord, tailWord_125269, baseEnd_125269] using wordTrace_append hprefix tailTrace_125269
  have hstable : (prefixWord ++ tailWord_125269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125269).length < 2 ^ (prefixWord ++ tailWord_125269).sum := by decide
  have hdescent : baseEnd_125269 < baseStart_125269 := by decide
  rcases family_descends (prefixWord ++ tailWord_125269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125285 : List Nat := [1, 3, 1, 3, 1, 3, 3, 2, 2, 1, 3]
def baseStart_125285 : Nat := 118140960795 + 125285 * 2 ^ 59
def prefixEnd_125285 : Nat := 4983230072969 + 3 ^ 40 * 125285 * 2
def baseEnd_125285 : Nat := 64331423798647555561331

theorem tailTrace_125285 : CollatzResearch.WordTrace tailWord_125285 prefixEnd_125285 64331423798647555561331 := by
  unfold tailWord_125285
  simp only [CollatzResearch.WordTrace]
  refine ⟨4569519351121316819609309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3046346234080877879739539 4569519351121316819609309)
  ·
    refine ⟨1713569756670493807353491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4569519351121316819609309 1713569756670493807353491)
    ·
      refine ⟨2570354635005740711030237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1713569756670493807353491 2570354635005740711030237)
      ·
        refine ⟨963882988127152766636339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2570354635005740711030237 963882988127152766636339)
        ·
          refine ⟨1445824482190729149954509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963882988127152766636339 1445824482190729149954509)
          ·
            refine ⟨542184180821523431232941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1445824482190729149954509 542184180821523431232941)
            ·
              refine ⟨203319067808071286712353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 542184180821523431232941 203319067808071286712353)
              ·
                refine ⟨152489300856053465034265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203319067808071286712353 152489300856053465034265)
                ·
                  refine ⟨114366975642040098775699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152489300856053465034265 114366975642040098775699)
                  ·
                    refine ⟨171550463463060148163549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114366975642040098775699 171550463463060148163549)
                    ·
                      refine ⟨64331423798647555561331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 171550463463060148163549 64331423798647555561331)
                      ·
                        rfl

theorem cell23_125285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_125285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125285 prefixEnd_125285 := by exact prefixLift 125285
  have htrace : WordTrace (prefixWord ++ tailWord_125285) baseStart_125285 baseEnd_125285 := by
    simpa [prefixWord, tailWord_125285, baseEnd_125285] using wordTrace_append hprefix tailTrace_125285
  have hstable : (prefixWord ++ tailWord_125285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125285).length < 2 ^ (prefixWord ++ tailWord_125285).sum := by decide
  have hdescent : baseEnd_125285 < baseStart_125285 := by decide
  rcases family_descends (prefixWord ++ tailWord_125285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125304 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 1, 2, 10]
def baseStart_125304 : Nat := 118140960795 + 125304 * 2 ^ 59
def prefixEnd_125304 : Nat := 4983230072969 + 3 ^ 40 * 125304 * 2
def baseEnd_125304 : Nat := 64341179931082981223743

theorem tailTrace_125304 : CollatzResearch.WordTrace tailWord_125304 prefixEnd_125304 64341179931082981223743 := by
  unfold tailWord_125304
  simp only [CollatzResearch.WordTrace]
  refine ⟨2285106169026241532275483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3046808225368322043033977 2285106169026241532275483)
  ·
    refine ⟨3427659253539362298413225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2285106169026241532275483 3427659253539362298413225)
    ·
      refine ⟨2570744440154521723809919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3427659253539362298413225 2570744440154521723809919)
      ·
        refine ⟨3856116660231782585714879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2570744440154521723809919 3856116660231782585714879)
        ·
          refine ⟨5784174990347673878572319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3856116660231782585714879 5784174990347673878572319)
          ·
            refine ⟨8676262485521510817858479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5784174990347673878572319 8676262485521510817858479)
            ·
              refine ⟨13014393728282266226787719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8676262485521510817858479 13014393728282266226787719)
              ·
                refine ⟨19521590592423399340181579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13014393728282266226787719 19521590592423399340181579)
                ·
                  refine ⟨29282385888635099010272369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19521590592423399340181579 29282385888635099010272369)
                  ·
                    refine ⟨21961789416476324257704277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29282385888635099010272369 21961789416476324257704277)
                    ·
                      refine ⟨64341179931082981223743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 21961789416476324257704277 64341179931082981223743)
                      ·
                        rfl

theorem cell23_125304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_125304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125304 prefixEnd_125304 := by exact prefixLift 125304
  have htrace : WordTrace (prefixWord ++ tailWord_125304) baseStart_125304 baseEnd_125304 := by
    simpa [prefixWord, tailWord_125304, baseEnd_125304] using wordTrace_append hprefix tailTrace_125304
  have hstable : (prefixWord ++ tailWord_125304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125304).length < 2 ^ (prefixWord ++ tailWord_125304).sum := by decide
  have hdescent : baseEnd_125304 < baseStart_125304 := by decide
  rcases family_descends (prefixWord ++ tailWord_125304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125308 : List Nat := [2, 2, 2, 1, 1, 1, 2, 5, 1, 4, 2]
def baseStart_125308 : Nat := 118140960795 + 125308 * 2 ^ 59
def prefixEnd_125308 : Nat := 4983230072969 + 3 ^ 40 * 125308 * 2
def baseEnd_125308 : Nat := 64343233853700965573725

theorem tailTrace_125308 : CollatzResearch.WordTrace tailWord_125308 prefixEnd_125308 64343233853700965573725 := by
  unfold tailWord_125308
  simp only [CollatzResearch.WordTrace]
  refine ⟨2285179115018995873848289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3046905486691994498464385 2285179115018995873848289)
  ·
    refine ⟨1713884336264246905386217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2285179115018995873848289 1713884336264246905386217)
    ·
      refine ⟨1285413252198185179039663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1713884336264246905386217 1285413252198185179039663)
      ·
        refine ⟨1928119878297277768559495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1285413252198185179039663 1928119878297277768559495)
        ·
          refine ⟨2892179817445916652839243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1928119878297277768559495 2892179817445916652839243)
          ·
            refine ⟨4338269726168874979258865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2892179817445916652839243 4338269726168874979258865)
            ·
              refine ⟨3253702294626656234444149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4338269726168874979258865 3253702294626656234444149)
              ·
                refine ⟨305034590121249021979139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3253702294626656234444149 305034590121249021979139)
                ·
                  refine ⟨457551885181873532968709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305034590121249021979139 457551885181873532968709)
                  ·
                    refine ⟨85790978471601287431633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 457551885181873532968709 85790978471601287431633)
                    ·
                      refine ⟨64343233853700965573725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 85790978471601287431633 64343233853700965573725)
                      ·
                        rfl

theorem cell23_125308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_125308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125308 prefixEnd_125308 := by exact prefixLift 125308
  have htrace : WordTrace (prefixWord ++ tailWord_125308) baseStart_125308 baseEnd_125308 := by
    simpa [prefixWord, tailWord_125308, baseEnd_125308] using wordTrace_append hprefix tailTrace_125308
  have hstable : (prefixWord ++ tailWord_125308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125308).length < 2 ^ (prefixWord ++ tailWord_125308).sum := by decide
  have hdescent : baseEnd_125308 < baseStart_125308 := by decide
  rcases family_descends (prefixWord ++ tailWord_125308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125348 : List Nat := [2, 3, 1, 2, 1, 1, 2, 6, 5]
def baseStart_125348 : Nat := 118140960795 + 125348 * 2 ^ 59
def prefixEnd_125348 : Nat := 4983230072969 + 3 ^ 40 * 125348 * 2
def baseEnd_125348 : Nat := 7151530342208978785949

theorem tailTrace_125348 : CollatzResearch.WordTrace tailWord_125348 prefixEnd_125348 7151530342208978785949 := by
  unfold tailWord_125348
  simp only [CollatzResearch.WordTrace]
  refine ⟨2285908574946539289576349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3047878099928719052768465 2285908574946539289576349)
  ·
    refine ⟨857215715604952233591131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2285908574946539289576349 857215715604952233591131)
    ·
      refine ⟨1285823573407428350386697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 857215715604952233591131 1285823573407428350386697)
      ·
        refine ⟨964367680055571262790023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1285823573407428350386697 964367680055571262790023)
        ·
          refine ⟨1446551520083356894185035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 964367680055571262790023 1446551520083356894185035)
          ·
            refine ⟨2169827280125035341277553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446551520083356894185035 2169827280125035341277553)
            ·
              refine ⟨1627370460093776505958165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2169827280125035341277553 1627370460093776505958165)
              ·
                refine ⟨76282990316895773716789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1627370460093776505958165 76282990316895773716789)
                ·
                  refine ⟨7151530342208978785949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76282990316895773716789 7151530342208978785949)
                  ·
                    rfl

theorem cell23_125348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_125348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125348 prefixEnd_125348 := by exact prefixLift 125348
  have htrace : WordTrace (prefixWord ++ tailWord_125348) baseStart_125348 baseEnd_125348 := by
    simpa [prefixWord, tailWord_125348, baseEnd_125348] using wordTrace_append hprefix tailTrace_125348
  have hstable : (prefixWord ++ tailWord_125348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125348).length < 2 ^ (prefixWord ++ tailWord_125348).sum := by decide
  have hdescent : baseEnd_125348 < baseStart_125348 := by decide
  rcases family_descends (prefixWord ++ tailWord_125348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125401 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 2, 3, 5]
def baseStart_125401 : Nat := 118140960795 + 125401 * 2 ^ 59
def prefixEnd_125401 : Nat := 4983230072969 + 3 ^ 40 * 125401 * 2
def baseEnd_125401 : Nat := 64390987554569101710797

theorem tailTrace_125401 : CollatzResearch.WordTrace tailWord_125401 prefixEnd_125401 64390987554569101710797 := by
  unfold tailWord_125401
  simp only [CollatzResearch.WordTrace]
  refine ⟨4573750218701068630832057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3049166812467379087221371 4573750218701068630832057)
  ·
    refine ⟨3430312664025801473124043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4573750218701068630832057 3430312664025801473124043)
    ·
      refine ⟨5145468996038702209686065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3430312664025801473124043 5145468996038702209686065)
      ·
        refine ⟨3859101747029026657264549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5145468996038702209686065 3859101747029026657264549)
        ·
          refine ⟨723581577567942498237103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3859101747029026657264549 723581577567942498237103)
          ·
            refine ⟨1085372366351913747355655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723581577567942498237103 1085372366351913747355655)
            ·
              refine ⟨1628058549527870621033483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1085372366351913747355655 1628058549527870621033483)
              ·
                refine ⟨2442087824291805931550225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1628058549527870621033483 2442087824291805931550225)
                ·
                  refine ⟨1831565868218854448662669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2442087824291805931550225 1831565868218854448662669)
                  ·
                    refine ⟨686837200582070418248501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1831565868218854448662669 686837200582070418248501)
                    ·
                      refine ⟨64390987554569101710797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 686837200582070418248501 64390987554569101710797)
                      ·
                        rfl

theorem cell23_125401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_125401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125401 prefixEnd_125401 := by exact prefixLift 125401
  have htrace : WordTrace (prefixWord ++ tailWord_125401) baseStart_125401 baseEnd_125401 := by
    simpa [prefixWord, tailWord_125401, baseEnd_125401] using wordTrace_append hprefix tailTrace_125401
  have hstable : (prefixWord ++ tailWord_125401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125401).length < 2 ^ (prefixWord ++ tailWord_125401).sum := by decide
  have hdescent : baseEnd_125401 < baseStart_125401 := by decide
  rcases family_descends (prefixWord ++ tailWord_125401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125408 : List Nat := [2, 1, 1, 3, 1, 1, 4, 3, 3, 4]
def baseStart_125408 : Nat := 118140960795 + 125408 * 2 ^ 59
def prefixEnd_125408 : Nat := 4983230072969 + 3 ^ 40 * 125408 * 2
def baseEnd_125408 : Nat := 21464860639716858107755

theorem tailTrace_125408 : CollatzResearch.WordTrace tailWord_125408 prefixEnd_125408 21464860639716858107755 := by
  unfold tailWord_125408
  simp only [CollatzResearch.WordTrace]
  refine ⟨2287002764837854413168439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3049337019783805884224585 2287002764837854413168439)
  ·
    refine ⟨3430504147256781619752659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2287002764837854413168439 3430504147256781619752659)
    ·
      refine ⟨5145756220885172429628989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3430504147256781619752659 5145756220885172429628989)
      ·
        refine ⟨1929658582831939661110871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5145756220885172429628989 1929658582831939661110871)
        ·
          refine ⟨2894487874247909491666307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1929658582831939661110871 2894487874247909491666307)
          ·
            refine ⟨4341731811371864237499461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2894487874247909491666307 4341731811371864237499461)
            ·
              refine ⟨814074714632224544531149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4341731811371864237499461 814074714632224544531149)
              ·
                refine ⟨305278017987084204199181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 814074714632224544531149 305278017987084204199181)
                ·
                  refine ⟨114479256745156576574693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305278017987084204199181 114479256745156576574693)
                  ·
                    refine ⟨21464860639716858107755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114479256745156576574693 21464860639716858107755)
                    ·
                      rfl

theorem cell23_125408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 3, 4].length) (baseStart_125408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125408 prefixEnd_125408 := by exact prefixLift 125408
  have htrace : WordTrace (prefixWord ++ tailWord_125408) baseStart_125408 baseEnd_125408 := by
    simpa [prefixWord, tailWord_125408, baseEnd_125408] using wordTrace_append hprefix tailTrace_125408
  have hstable : (prefixWord ++ tailWord_125408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125408).length < 2 ^ (prefixWord ++ tailWord_125408).sum := by decide
  have hdescent : baseEnd_125408 < baseStart_125408 := by decide
  rcases family_descends (prefixWord ++ tailWord_125408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125415 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 2, 4, 2]
def baseStart_125415 : Nat := 118140960795 + 125415 * 2 ^ 59
def prefixEnd_125415 : Nat := 4983230072969 + 3 ^ 40 * 125415 * 2
def baseEnd_125415 : Nat := 64398176283732046935733

theorem tailTrace_125415 : CollatzResearch.WordTrace tailWord_125415 prefixEnd_125415 64398176283732046935733 := by
  unfold tailWord_125415
  simp only [CollatzResearch.WordTrace]
  refine ⟨4574260840650349021841699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3049507227100232681227799 4574260840650349021841699)
  ·
    refine ⟨6861391260975523532762549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4574260840650349021841699 6861391260975523532762549)
    ·
      refine ⟨643255430716455331196489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6861391260975523532762549 643255430716455331196489)
      ·
        refine ⟨482441573037341498397367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 643255430716455331196489 482441573037341498397367)
        ·
          refine ⟨723662359556012247596051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482441573037341498397367 723662359556012247596051)
          ·
            refine ⟨1085493539334018371394077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723662359556012247596051 1085493539334018371394077)
            ·
              refine ⟨407060077250256889272779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1085493539334018371394077 407060077250256889272779)
              ·
                refine ⟨610590115875385333909169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407060077250256889272779 610590115875385333909169)
                ·
                  refine ⟨457942586906539000431877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610590115875385333909169 457942586906539000431877)
                  ·
                    refine ⟨85864235044976062580977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 457942586906539000431877 85864235044976062580977)
                    ·
                      refine ⟨64398176283732046935733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 85864235044976062580977 64398176283732046935733)
                      ·
                        rfl

theorem cell23_125415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_125415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125415 prefixEnd_125415 := by exact prefixLift 125415
  have htrace : WordTrace (prefixWord ++ tailWord_125415) baseStart_125415 baseEnd_125415 := by
    simpa [prefixWord, tailWord_125415, baseEnd_125415] using wordTrace_append hprefix tailTrace_125415
  have hstable : (prefixWord ++ tailWord_125415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125415).length < 2 ^ (prefixWord ++ tailWord_125415).sum := by decide
  have hdescent : baseEnd_125415 < baseStart_125415 := by decide
  rcases family_descends (prefixWord ++ tailWord_125415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125429 : List Nat := [1, 3, 5, 1, 3, 1, 1, 1, 2, 5]
def baseStart_125429 : Nat := 118140960795 + 125429 * 2 ^ 59
def prefixEnd_125429 : Nat := 4983230072969 + 3 ^ 40 * 125429 * 2
def baseEnd_125429 : Nat := 21468455004298330720223

theorem tailTrace_125429 : CollatzResearch.WordTrace tailWord_125429 prefixEnd_125429 21468455004298330720223 := by
  unfold tailWord_125429
  simp only [CollatzResearch.WordTrace]
  refine ⟨4574771462599629412851341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3049847641733086275234227 4574771462599629412851341)
  ·
    refine ⟨1715539298474861029819253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4574771462599629412851341 1715539298474861029819253)
    ·
      refine ⟨160831809232018221545555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1715539298474861029819253 160831809232018221545555)
      ·
        refine ⟨241247713848027332318333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160831809232018221545555 241247713848027332318333)
        ·
          refine ⟨90467892693010249619375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241247713848027332318333 90467892693010249619375)
          ·
            refine ⟨135701839039515374429063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90467892693010249619375 135701839039515374429063)
            ·
              refine ⟨203552758559273061643595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135701839039515374429063 203552758559273061643595)
              ·
                refine ⟨305329137838909592465393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203552758559273061643595 305329137838909592465393)
                ·
                  refine ⟨228996853379182194349045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305329137838909592465393 228996853379182194349045)
                  ·
                    refine ⟨21468455004298330720223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 228996853379182194349045 21468455004298330720223)
                    ·
                      rfl

theorem cell23_125429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_125429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125429 prefixEnd_125429 := by exact prefixLift 125429
  have htrace : WordTrace (prefixWord ++ tailWord_125429) baseStart_125429 baseEnd_125429 := by
    simpa [prefixWord, tailWord_125429, baseEnd_125429] using wordTrace_append hprefix tailTrace_125429
  have hstable : (prefixWord ++ tailWord_125429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125429).length < 2 ^ (prefixWord ++ tailWord_125429).sum := by decide
  have hdescent : baseEnd_125429 < baseStart_125429 := by decide
  rcases family_descends (prefixWord ++ tailWord_125429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125472 : List Nat := [2, 1, 1, 6, 2, 1, 3, 1, 6]
def baseStart_125472 : Nat := 118140960795 + 125472 * 2 ^ 59
def prefixEnd_125472 : Nat := 4983230072969 + 3 ^ 40 * 125472 * 2
def baseEnd_125472 : Nat := 7158604964559813769219

theorem tailTrace_125472 : CollatzResearch.WordTrace tailWord_125472 prefixEnd_125472 7158604964559813769219 := by
  unfold tailWord_125472
  simp only [CollatzResearch.WordTrace]
  refine ⟨2288169900721923878333335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3050893200962565171111113 2288169900721923878333335)
  ·
    refine ⟨3432254851082885817500003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2288169900721923878333335 3432254851082885817500003)
    ·
      refine ⟨5148382276624328726250005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3432254851082885817500003 5148382276624328726250005)
      ·
        refine ⟨241330419216765409042969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5148382276624328726250005 241330419216765409042969)
        ·
          refine ⟨180997814412574056782227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241330419216765409042969 180997814412574056782227)
          ·
            refine ⟨271496721618861085173341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180997814412574056782227 271496721618861085173341)
            ·
              refine ⟨101811270607072906940003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271496721618861085173341 101811270607072906940003)
              ·
                refine ⟨152716905910609360410005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101811270607072906940003 152716905910609360410005)
                ·
                  refine ⟨7158604964559813769219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152716905910609360410005 7158604964559813769219)
                  ·
                    rfl

theorem cell23_125472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 6].length) (baseStart_125472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125472 prefixEnd_125472 := by exact prefixLift 125472
  have htrace : WordTrace (prefixWord ++ tailWord_125472) baseStart_125472 baseEnd_125472 := by
    simpa [prefixWord, tailWord_125472, baseEnd_125472] using wordTrace_append hprefix tailTrace_125472
  have hstable : (prefixWord ++ tailWord_125472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125472).length < 2 ^ (prefixWord ++ tailWord_125472).sum := by decide
  have hdescent : baseEnd_125472 < baseStart_125472 := by decide
  rcases family_descends (prefixWord ++ tailWord_125472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125475 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 1, 5, 2]
def baseStart_125475 : Nat := 118140960795 + 125475 * 2 ^ 59
def prefixEnd_125475 : Nat := 4983230072969 + 3 ^ 40 * 125475 * 2
def baseEnd_125475 : Nat := 64428985123001812185457

theorem tailTrace_125475 : CollatzResearch.WordTrace tailWord_125475 prefixEnd_125475 64428985123001812185457 := by
  unfold tailWord_125475
  simp only [CollatzResearch.WordTrace]
  refine ⟨4576449220432979269025879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3050966146955319512683919 4576449220432979269025879)
  ·
    refine ⟨6864673830649468903538819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4576449220432979269025879 6864673830649468903538819)
    ·
      refine ⟨10297010745974203355308229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6864673830649468903538819 10297010745974203355308229)
      ·
        refine ⟨1930689514870163129120293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10297010745974203355308229 1930689514870163129120293)
        ·
          refine ⟨362004284038155586710055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1930689514870163129120293 362004284038155586710055)
          ·
            refine ⟨543006426057233380065083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362004284038155586710055 543006426057233380065083)
            ·
              refine ⟨814509639085850070097625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543006426057233380065083 814509639085850070097625)
              ·
                refine ⟨610882229314387552573219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 814509639085850070097625 610882229314387552573219)
                ·
                  refine ⟨916323343971581328859829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610882229314387552573219 916323343971581328859829)
                  ·
                    refine ⟨85905313497335749580609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 916323343971581328859829 85905313497335749580609)
                    ·
                      refine ⟨64428985123001812185457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 85905313497335749580609 64428985123001812185457)
                      ·
                        rfl

theorem cell23_125475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_125475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125475 prefixEnd_125475 := by exact prefixLift 125475
  have htrace : WordTrace (prefixWord ++ tailWord_125475) baseStart_125475 baseEnd_125475 := by
    simpa [prefixWord, tailWord_125475, baseEnd_125475] using wordTrace_append hprefix tailTrace_125475
  have hstable : (prefixWord ++ tailWord_125475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125475).length < 2 ^ (prefixWord ++ tailWord_125475).sum := by decide
  have hdescent : baseEnd_125475 < baseStart_125475 := by decide
  rcases family_descends (prefixWord ++ tailWord_125475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125482 : List Nat := [3, 1, 4, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_125482 : Nat := 118140960795 + 125482 * 2 ^ 59
def prefixEnd_125482 : Nat := 4983230072969 + 3 ^ 40 * 125482 * 2
def baseEnd_125482 : Nat := 64432579487583284797925

theorem tailTrace_125482 : CollatzResearch.WordTrace tailWord_125482 prefixEnd_125482 64432579487583284797925 := by
  unfold tailWord_125482
  simp only [CollatzResearch.WordTrace]
  refine ⟨1144176132851904866132675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3051136354271746309687133 1144176132851904866132675)
  ·
    refine ⟨1716264199277857299199013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1144176132851904866132675 1716264199277857299199013)
    ·
      refine ⟨321799537364598243599815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1716264199277857299199013 321799537364598243599815)
      ·
        refine ⟨482699306046897365399723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321799537364598243599815 482699306046897365399723)
        ·
          refine ⟨724048959070346048099585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482699306046897365399723 724048959070346048099585)
          ·
            refine ⟨543036719302759536074689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724048959070346048099585 543036719302759536074689)
            ·
              refine ⟨407277539477069652056017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543036719302759536074689 407277539477069652056017)
              ·
                refine ⟨305458154607802239042013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407277539477069652056017 305458154607802239042013)
                ·
                  refine ⟨114546807977925839640755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305458154607802239042013 114546807977925839640755)
                  ·
                    refine ⟨171820211966888759461133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114546807977925839640755 171820211966888759461133)
                    ·
                      refine ⟨64432579487583284797925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 171820211966888759461133 64432579487583284797925)
                      ·
                        rfl

theorem cell23_125482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_125482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125482 prefixEnd_125482 := by exact prefixLift 125482
  have htrace : WordTrace (prefixWord ++ tailWord_125482) baseStart_125482 baseEnd_125482 := by
    simpa [prefixWord, tailWord_125482, baseEnd_125482] using wordTrace_append hprefix tailTrace_125482
  have hstable : (prefixWord ++ tailWord_125482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125482).length < 2 ^ (prefixWord ++ tailWord_125482).sum := by decide
  have hdescent : baseEnd_125482 < baseStart_125482 := by decide
  rcases family_descends (prefixWord ++ tailWord_125482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125488 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 4]
def baseStart_125488 : Nat := 118140960795 + 125488 * 2 ^ 59
def prefixEnd_125488 : Nat := 4983230072969 + 3 ^ 40 * 125488 * 2
def baseEnd_125488 : Nat := 64435660371510261322897

theorem tailTrace_125488 : CollatzResearch.WordTrace tailWord_125488 prefixEnd_125488 64435660371510261322897 := by
  unfold tailWord_125488
  simp only [CollatzResearch.WordTrace]
  refine ⟨2288461684692941244624559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3051282246257254992832745 2288461684692941244624559)
  ·
    refine ⟨3432692527039411866936839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2288461684692941244624559 3432692527039411866936839)
    ·
      refine ⟨5149038790559117800405259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3432692527039411866936839 5149038790559117800405259)
      ·
        refine ⟨7723558185838676700607889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5149038790559117800405259 7723558185838676700607889)
        ·
          refine ⟨5792668639379007525455917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7723558185838676700607889 5792668639379007525455917)
          ·
            refine ⟨2172250739767127822045969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5792668639379007525455917 2172250739767127822045969)
            ·
              refine ⟨1629188054825345866534477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2172250739767127822045969 1629188054825345866534477)
              ·
                refine ⟨610945520559504699950429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1629188054825345866534477 610945520559504699950429)
                ·
                  refine ⟨229104570209814262481411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 610945520559504699950429 229104570209814262481411)
                  ·
                    refine ⟨343656855314721393722117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 229104570209814262481411 343656855314721393722117)
                    ·
                      refine ⟨64435660371510261322897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 343656855314721393722117 64435660371510261322897)
                      ·
                        rfl

theorem cell23_125488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 4].length) (baseStart_125488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125488 prefixEnd_125488 := by exact prefixLift 125488
  have htrace : WordTrace (prefixWord ++ tailWord_125488) baseStart_125488 baseEnd_125488 := by
    simpa [prefixWord, tailWord_125488, baseEnd_125488] using wordTrace_append hprefix tailTrace_125488
  have hstable : (prefixWord ++ tailWord_125488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125488).length < 2 ^ (prefixWord ++ tailWord_125488).sum := by decide
  have hdescent : baseEnd_125488 < baseStart_125488 := by decide
  rcases family_descends (prefixWord ++ tailWord_125488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125518 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_125518 : Nat := 118140960795 + 125518 * 2 ^ 59
def prefixEnd_125518 : Nat := 4983230072969 + 3 ^ 40 * 125518 * 2
def baseEnd_125518 : Nat := 64451064791145143947759

theorem tailTrace_125518 : CollatzResearch.WordTrace tailWord_125518 prefixEnd_125518 64451064791145143947759 := by
  unfold tailWord_125518
  simp only [CollatzResearch.WordTrace]
  refine ⟨572252194909649701605151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3052011706184798408560805 572252194909649701605151)
  ·
    refine ⟨858378292364474552407727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 572252194909649701605151 858378292364474552407727)
    ·
      refine ⟨1287567438546711828611591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 858378292364474552407727 1287567438546711828611591)
      ·
        refine ⟨1931351157820067742917387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287567438546711828611591 1931351157820067742917387)
        ·
          refine ⟨2897026736730101614376081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1931351157820067742917387 2897026736730101614376081)
          ·
            refine ⟨2172770052547576210782061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2897026736730101614376081 2172770052547576210782061)
            ·
              refine ⟨814788769705341079043273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2172770052547576210782061 814788769705341079043273)
              ·
                refine ⟨611091577279005809282455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 814788769705341079043273 611091577279005809282455)
                ·
                  refine ⟨916637365918508713923683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 611091577279005809282455 916637365918508713923683)
                  ·
                    refine ⟨1374956048877763070885525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 916637365918508713923683 1374956048877763070885525)
                    ·
                      refine ⟨64451064791145143947759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1374956048877763070885525 64451064791145143947759)
                      ·
                        rfl

theorem cell23_125518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_125518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125518 prefixEnd_125518 := by exact prefixLift 125518
  have htrace : WordTrace (prefixWord ++ tailWord_125518) baseStart_125518 baseEnd_125518 := by
    simpa [prefixWord, tailWord_125518, baseEnd_125518] using wordTrace_append hprefix tailTrace_125518
  have hstable : (prefixWord ++ tailWord_125518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125518).length < 2 ^ (prefixWord ++ tailWord_125518).sum := by decide
  have hdescent : baseEnd_125518 < baseStart_125518 := by decide
  rcases family_descends (prefixWord ++ tailWord_125518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125555 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 4, 1, 3]
def baseStart_125555 : Nat := 118140960795 + 125555 * 2 ^ 59
def prefixEnd_125555 : Nat := 4983230072969 + 3 ^ 40 * 125555 * 2
def baseEnd_125555 : Nat := 64470063575361499185089

theorem tailTrace_125555 : CollatzResearch.WordTrace tailWord_125555 prefixEnd_125555 64470063575361499185089 := by
  unfold tailWord_125555
  simp only [CollatzResearch.WordTrace]
  refine ⟨4579367060143152931938119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3052911373428768621292079 4579367060143152931938119)
  ·
    refine ⟨6869050590214729397907179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4579367060143152931938119 6869050590214729397907179)
    ·
      refine ⟨10303575885322094096860769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6869050590214729397907179 10303575885322094096860769)
      ·
        refine ⟨7727681913991570572645577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10303575885322094096860769 7727681913991570572645577)
        ·
          refine ⟨5795761435493677929484183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7727681913991570572645577 5795761435493677929484183)
          ·
            refine ⟨8693642153240516894226275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5795761435493677929484183 8693642153240516894226275)
            ·
              refine ⟨13040463229860775341339413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8693642153240516894226275 13040463229860775341339413)
              ·
                refine ⟨611271713899723844125285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13040463229860775341339413 611271713899723844125285)
                ·
                  refine ⟨114613446356198220773491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 611271713899723844125285 114613446356198220773491)
                  ·
                    refine ⟨171920169534297331160237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114613446356198220773491 171920169534297331160237)
                    ·
                      refine ⟨64470063575361499185089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 171920169534297331160237 64470063575361499185089)
                      ·
                        rfl

theorem cell23_125555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 1, 3].length) (baseStart_125555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125555 prefixEnd_125555 := by exact prefixLift 125555
  have htrace : WordTrace (prefixWord ++ tailWord_125555) baseStart_125555 baseEnd_125555 := by
    simpa [prefixWord, tailWord_125555, baseEnd_125555] using wordTrace_append hprefix tailTrace_125555
  have hstable : (prefixWord ++ tailWord_125555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125555).length < 2 ^ (prefixWord ++ tailWord_125555).sum := by decide
  have hdescent : baseEnd_125555 < baseStart_125555 := by decide
  rcases family_descends (prefixWord ++ tailWord_125555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125573 : List Nat := [1, 3, 1, 1, 4, 4, 2, 2, 1, 2, 2]
def baseStart_125573 : Nat := 118140960795 + 125573 * 2 ^ 59
def prefixEnd_125573 : Nat := 4983230072969 + 3 ^ 40 * 125573 * 2
def baseEnd_125573 : Nat := 64479306227142428760007

theorem tailTrace_125573 : CollatzResearch.WordTrace tailWord_125573 prefixEnd_125573 64479306227142428760007 := by
  unfold tailWord_125573
  simp only [CollatzResearch.WordTrace]
  refine ⟨4580023574077942006093373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3053349049385294670728915 4580023574077942006093373)
  ·
    refine ⟨1717508840279228252285015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4580023574077942006093373 1717508840279228252285015)
    ·
      refine ⟨2576263260418842378427523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1717508840279228252285015 2576263260418842378427523)
      ·
        refine ⟨3864394890628263567641285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2576263260418842378427523 3864394890628263567641285)
        ·
          refine ⟨724574041992799418932741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3864394890628263567641285 724574041992799418932741)
          ·
            refine ⟨135857632873649891049889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 724574041992799418932741 135857632873649891049889)
            ·
              refine ⟨101893224655237418287417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135857632873649891049889 101893224655237418287417)
              ·
                refine ⟨76419918491428063715563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101893224655237418287417 76419918491428063715563)
                ·
                  refine ⟨114629877737142095573345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76419918491428063715563 114629877737142095573345)
                  ·
                    refine ⟨85972408302856571680009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114629877737142095573345 85972408302856571680009)
                    ·
                      refine ⟨64479306227142428760007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 85972408302856571680009 64479306227142428760007)
                      ·
                        rfl

theorem cell23_125573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 1, 2, 2].length) (baseStart_125573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125573 prefixEnd_125573 := by exact prefixLift 125573
  have htrace : WordTrace (prefixWord ++ tailWord_125573) baseStart_125573 baseEnd_125573 := by
    simpa [prefixWord, tailWord_125573, baseEnd_125573] using wordTrace_append hprefix tailTrace_125573
  have hstable : (prefixWord ++ tailWord_125573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125573).length < 2 ^ (prefixWord ++ tailWord_125573).sum := by decide
  have hdescent : baseEnd_125573 < baseStart_125573 := by decide
  rcases family_descends (prefixWord ++ tailWord_125573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125582 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2]
def baseStart_125582 : Nat := 118140960795 + 125582 * 2 ^ 59
def prefixEnd_125582 : Nat := 4983230072969 + 3 ^ 40 * 125582 * 2
def baseEnd_125582 : Nat := 64483927553032893547465

theorem tailTrace_125582 : CollatzResearch.WordTrace tailWord_125582 prefixEnd_125582 64483927553032893547465 := by
  unfold tailWord_125582
  simp only [CollatzResearch.WordTrace]
  refine ⟨572543978880667067896375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3053567887363557695447333 572543978880667067896375)
  ·
    refine ⟨858815968321000601844563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 572543978880667067896375 858815968321000601844563)
    ·
      refine ⟨1288223952481500902766845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 858815968321000601844563 1288223952481500902766845)
      ·
        refine ⟨483083982180562838537567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1288223952481500902766845 483083982180562838537567)
        ·
          refine ⟨724625973270844257806351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483083982180562838537567 724625973270844257806351)
          ·
            refine ⟨1086938959906266386709527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724625973270844257806351 1086938959906266386709527)
            ·
              refine ⟨1630408439859399580064291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086938959906266386709527 1630408439859399580064291)
              ·
                refine ⟨2445612659789099370096437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1630408439859399580064291 2445612659789099370096437)
                ·
                  refine ⟨229276186855228065946541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2445612659789099370096437 229276186855228065946541)
                  ·
                    refine ⟨85978570070710524729953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 229276186855228065946541 85978570070710524729953)
                    ·
                      refine ⟨64483927553032893547465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 85978570070710524729953 64483927553032893547465)
                      ·
                        rfl

theorem cell23_125582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_125582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125582 prefixEnd_125582 := by exact prefixLift 125582
  have htrace : WordTrace (prefixWord ++ tailWord_125582) baseStart_125582 baseEnd_125582 := by
    simpa [prefixWord, tailWord_125582, baseEnd_125582] using wordTrace_append hprefix tailTrace_125582
  have hstable : (prefixWord ++ tailWord_125582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125582).length < 2 ^ (prefixWord ++ tailWord_125582).sum := by decide
  have hdescent : baseEnd_125582 < baseStart_125582 := by decide
  rcases family_descends (prefixWord ++ tailWord_125582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125610 : List Nat := [3, 1, 5, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_125610 : Nat := 118140960795 + 125610 * 2 ^ 59
def prefixEnd_125610 : Nat := 4983230072969 + 3 ^ 40 * 125610 * 2
def baseEnd_125610 : Nat := 64498305011358783997337

theorem tailTrace_125610 : CollatzResearch.WordTrace tailWord_125610 prefixEnd_125610 64498305011358783997337 := by
  unfold tailWord_125610
  simp only [CollatzResearch.WordTrace]
  refine ⟨1145343268735974331297571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3054248716629264883460189 1145343268735974331297571)
  ·
    refine ⟨1718014903103961496946357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1145343268735974331297571 1718014903103961496946357)
    ·
      refine ⟨161063897165996390338721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1718014903103961496946357 161063897165996390338721)
      ·
        refine ⟨120797922874497292754041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161063897165996390338721 120797922874497292754041)
        ·
          refine ⟨90598442155872969565531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120797922874497292754041 90598442155872969565531)
          ·
            refine ⟨135897663233809454348297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90598442155872969565531 135897663233809454348297)
            ·
              refine ⟨101923247425357090761223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135897663233809454348297 101923247425357090761223)
              ·
                refine ⟨152884871138035636141835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101923247425357090761223 152884871138035636141835)
                ·
                  refine ⟨229327306707053454212753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152884871138035636141835 229327306707053454212753)
                  ·
                    refine ⟨171995480030290090659565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 229327306707053454212753 171995480030290090659565)
                    ·
                      refine ⟨64498305011358783997337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 171995480030290090659565 64498305011358783997337)
                      ·
                        rfl

theorem cell23_125610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_125610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125610 prefixEnd_125610 := by exact prefixLift 125610
  have htrace : WordTrace (prefixWord ++ tailWord_125610) baseStart_125610 baseEnd_125610 := by
    simpa [prefixWord, tailWord_125610, baseEnd_125610] using wordTrace_append hprefix tailTrace_125610
  have hstable : (prefixWord ++ tailWord_125610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125610).length < 2 ^ (prefixWord ++ tailWord_125610).sum := by decide
  have hdescent : baseEnd_125610 < baseStart_125610 := by decide
  rcases family_descends (prefixWord ++ tailWord_125610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125618 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 11]
def baseStart_125618 : Nat := 118140960795 + 125618 * 2 ^ 59
def prefixEnd_125618 : Nat := 4983230072969 + 3 ^ 40 * 125618 * 2
def baseEnd_125618 : Nat := 7166934761843861410811

theorem tailTrace_125618 : CollatzResearch.WordTrace tailWord_125618 prefixEnd_125618 7166934761843861410811 := by
  unfold tailWord_125618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1145416214728728672870377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3054443239276609794321005 1145416214728728672870377)
  ·
    refine ⟨859062161046546504652783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1145416214728728672870377 859062161046546504652783)
    ·
      refine ⟨1288593241569819756979175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 859062161046546504652783 1288593241569819756979175)
      ·
        refine ⟨1932889862354729635468763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288593241569819756979175 1932889862354729635468763)
        ·
          refine ⟨2899334793532094453203145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1932889862354729635468763 2899334793532094453203145)
          ·
            refine ⟨2174501095149070839902359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2899334793532094453203145 2174501095149070839902359)
            ·
              refine ⟨3261751642723606259853539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174501095149070839902359 3261751642723606259853539)
              ·
                refine ⟨4892627464085409389780309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3261751642723606259853539 4892627464085409389780309)
                ·
                  refine ⟨7166934761843861410811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 4892627464085409389780309 7166934761843861410811)
                  ·
                    rfl

theorem cell23_125618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_125618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125618 prefixEnd_125618 := by exact prefixLift 125618
  have htrace : WordTrace (prefixWord ++ tailWord_125618) baseStart_125618 baseEnd_125618 := by
    simpa [prefixWord, tailWord_125618, baseEnd_125618] using wordTrace_append hprefix tailTrace_125618
  have hstable : (prefixWord ++ tailWord_125618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125618).length < 2 ^ (prefixWord ++ tailWord_125618).sum := by decide
  have hdescent : baseEnd_125618 < baseStart_125618 := by decide
  rcases family_descends (prefixWord ++ tailWord_125618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125629 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 4, 2, 2]
def baseStart_125629 : Nat := 118140960795 + 125629 * 2 ^ 59
def prefixEnd_125629 : Nat := 4983230072969 + 3 ^ 40 * 125629 * 2
def baseEnd_125629 : Nat := 64508061143794209659749

theorem tailTrace_125629 : CollatzResearch.WordTrace tailWord_125629 prefixEnd_125629 64508061143794209659749 := by
  unfold tailWord_125629
  simp only [CollatzResearch.WordTrace]
  refine ⟨4582066061875063570131941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3054710707916709046754627 4582066061875063570131941)
  ·
    refine ⟨859137386601574419399739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4582066061875063570131941 859137386601574419399739)
    ·
      refine ⟨1288706079902361629099609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 859137386601574419399739 1288706079902361629099609)
      ·
        refine ⟨966529559926771221824707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1288706079902361629099609 966529559926771221824707)
        ·
          refine ⟨1449794339890156832737061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966529559926771221824707 1449794339890156832737061)
          ·
            refine ⟨271836438729404406138199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1449794339890156832737061 271836438729404406138199)
            ·
              refine ⟨407754658094106609207299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271836438729404406138199 407754658094106609207299)
              ·
                refine ⟨611631987141159913810949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407754658094106609207299 611631987141159913810949)
                ·
                  refine ⟨114680997588967483839553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 611631987141159913810949 114680997588967483839553)
                  ·
                    refine ⟨86010748191725612879665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114680997588967483839553 86010748191725612879665)
                    ·
                      refine ⟨64508061143794209659749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 86010748191725612879665 64508061143794209659749)
                      ·
                        rfl

theorem cell23_125629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_125629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125629 prefixEnd_125629 := by exact prefixLift 125629
  have htrace : WordTrace (prefixWord ++ tailWord_125629) baseStart_125629 baseEnd_125629 := by
    simpa [prefixWord, tailWord_125629, baseEnd_125629] using wordTrace_append hprefix tailTrace_125629
  have hstable : (prefixWord ++ tailWord_125629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125629).length < 2 ^ (prefixWord ++ tailWord_125629).sum := by decide
  have hdescent : baseEnd_125629 < baseStart_125629 := by decide
  rcases family_descends (prefixWord ++ tailWord_125629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125665 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 1, 7]
def baseStart_125665 : Nat := 118140960795 + 125665 * 2 ^ 59
def prefixEnd_125665 : Nat := 4983230072969 + 3 ^ 40 * 125665 * 2
def baseEnd_125665 : Nat := 21508848815785356269861

theorem tailTrace_125665 : CollatzResearch.WordTrace tailWord_125665 prefixEnd_125665 21508848815785356269861 := by
  unfold tailWord_125665
  simp only [CollatzResearch.WordTrace]
  refine ⟨4583379089744641718442449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3055586059829761145628299 4583379089744641718442449)
  ·
    refine ⟨3437534317308481288831837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4583379089744641718442449 3437534317308481288831837)
    ·
      refine ⟨1289075368990680483311939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3437534317308481288831837 1289075368990680483311939)
      ·
        refine ⟨1933613053486020724967909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1289075368990680483311939 1933613053486020724967909)
        ·
          refine ⟨362552447528628885931483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1933613053486020724967909 362552447528628885931483)
          ·
            refine ⟨543828671292943328897225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362552447528628885931483 543828671292943328897225)
            ·
              refine ⟨407871503469707496672919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543828671292943328897225 407871503469707496672919)
              ·
                refine ⟨611807255204561245009379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407871503469707496672919 611807255204561245009379)
                ·
                  refine ⟨917710882806841867514069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 611807255204561245009379 917710882806841867514069)
                  ·
                    refine ⟨21508848815785356269861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 917710882806841867514069 21508848815785356269861)
                    ·
                      rfl

theorem cell23_125665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_125665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125665 prefixEnd_125665 := by exact prefixLift 125665
  have htrace : WordTrace (prefixWord ++ tailWord_125665) baseStart_125665 baseEnd_125665 := by
    simpa [prefixWord, tailWord_125665, baseEnd_125665] using wordTrace_append hprefix tailTrace_125665
  have hstable : (prefixWord ++ tailWord_125665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125665).length < 2 ^ (prefixWord ++ tailWord_125665).sum := by decide
  have hdescent : baseEnd_125665 < baseStart_125665 := by decide
  rcases family_descends (prefixWord ++ tailWord_125665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125669 : List Nat := [1, 3, 1, 4, 1, 4, 1, 3, 5]
def baseStart_125669 : Nat := 118140960795 + 125669 * 2 ^ 59
def prefixEnd_125669 : Nat := 4983230072969 + 3 ^ 40 * 125669 * 2
def baseEnd_125669 : Nat := 7169844485552672573285

theorem tailTrace_125669 : CollatzResearch.WordTrace tailWord_125669 prefixEnd_125669 7169844485552672573285 := by
  unfold tailWord_125669
  simp only [CollatzResearch.WordTrace]
  refine ⟨4583524981730150401588061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3055683321153433601058707 4583524981730150401588061)
  ·
    refine ⟨1718821868148806400595523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4583524981730150401588061 1718821868148806400595523)
    ·
      refine ⟨2578232802223209600893285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1718821868148806400595523 2578232802223209600893285)
      ·
        refine ⟨483418650416851800167491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2578232802223209600893285 483418650416851800167491)
        ·
          refine ⟨725127975625277700251237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483418650416851800167491 725127975625277700251237)
          ·
            refine ⟨135961495429739568797107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 725127975625277700251237 135961495429739568797107)
            ·
              refine ⟨203942243144609353195661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135961495429739568797107 203942243144609353195661)
              ·
                refine ⟨76478341179228507448373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203942243144609353195661 76478341179228507448373)
                ·
                  refine ⟨7169844485552672573285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76478341179228507448373 7169844485552672573285)
                  ·
                    rfl

theorem cell23_125669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 5].length) (baseStart_125669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125669 prefixEnd_125669 := by exact prefixLift 125669
  have htrace : WordTrace (prefixWord ++ tailWord_125669) baseStart_125669 baseEnd_125669 := by
    simpa [prefixWord, tailWord_125669, baseEnd_125669] using wordTrace_append hprefix tailTrace_125669
  have hstable : (prefixWord ++ tailWord_125669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125669).length < 2 ^ (prefixWord ++ tailWord_125669).sum := by decide
  have hdescent : baseEnd_125669 < baseStart_125669 := by decide
  rcases family_descends (prefixWord ++ tailWord_125669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125682 : List Nat := [3, 2, 1, 3, 1, 3, 1, 2, 2, 5]
def baseStart_125682 : Nat := 118140960795 + 125682 * 2 ^ 59
def prefixEnd_125682 : Nat := 4983230072969 + 3 ^ 40 * 125682 * 2
def baseEnd_125682 : Nat := 21511758539494167432335

theorem tailTrace_125682 : CollatzResearch.WordTrace tailWord_125682 prefixEnd_125682 21511758539494167432335 := by
  unfold tailWord_125682
  simp only [CollatzResearch.WordTrace]
  refine ⟨1145999782670763405452825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3055999420455369081207533 1145999782670763405452825)
  ·
    refine ⟨859499837003072554089619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1145999782670763405452825 859499837003072554089619)
    ·
      refine ⟨1289249755504608831134429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 859499837003072554089619 1289249755504608831134429)
      ·
        refine ⟨483468658314228311675411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1289249755504608831134429 483468658314228311675411)
        ·
          refine ⟨725202987471342467513117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483468658314228311675411 725202987471342467513117)
          ·
            refine ⟨271951120301753425317419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 725202987471342467513117 271951120301753425317419)
            ·
              refine ⟨407926680452630137976129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271951120301753425317419 407926680452630137976129)
              ·
                refine ⟨305945010339472603482097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407926680452630137976129 305945010339472603482097)
                ·
                  refine ⟨229458757754604452611573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305945010339472603482097 229458757754604452611573)
                  ·
                    refine ⟨21511758539494167432335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 229458757754604452611573 21511758539494167432335)
                    ·
                      rfl

theorem cell23_125682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_125682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125682 prefixEnd_125682 := by exact prefixLift 125682
  have htrace : WordTrace (prefixWord ++ tailWord_125682) baseStart_125682 baseEnd_125682 := by
    simpa [prefixWord, tailWord_125682, baseEnd_125682] using wordTrace_append hprefix tailTrace_125682
  have hstable : (prefixWord ++ tailWord_125682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125682).length < 2 ^ (prefixWord ++ tailWord_125682).sum := by decide
  have hdescent : baseEnd_125682 < baseStart_125682 := by decide
  rcases family_descends (prefixWord ++ tailWord_125682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125705 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 3, 4, 3]
def baseStart_125705 : Nat := 118140960795 + 125705 * 2 ^ 59
def prefixEnd_125705 : Nat := 4983230072969 + 3 ^ 40 * 125705 * 2
def baseEnd_125705 : Nat := 64547085673535912309399

theorem tailTrace_125705 : CollatzResearch.WordTrace tailWord_125705 prefixEnd_125705 64547085673535912309399 := by
  unfold tailWord_125705
  simp only [CollatzResearch.WordTrace]
  refine ⟨4584838009599728549898569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3056558673066485699932379 4584838009599728549898569)
  ·
    refine ⟨3438628507199796412423927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4584838009599728549898569 3438628507199796412423927)
    ·
      refine ⟨5157942760799694618635891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3438628507199796412423927 5157942760799694618635891)
      ·
        refine ⟨7736914141199541927953837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5157942760799694618635891 7736914141199541927953837)
        ·
          refine ⟨2901342802949828222982689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7736914141199541927953837 2901342802949828222982689)
          ·
            refine ⟨2176007102212371167237017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2901342802949828222982689 2176007102212371167237017)
            ·
              refine ⟨1632005326659278375427763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2176007102212371167237017 1632005326659278375427763)
              ·
                refine ⟨2448007989988917563141645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1632005326659278375427763 2448007989988917563141645)
                ·
                  refine ⟨918002996245844086178117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2448007989988917563141645 918002996245844086178117)
                  ·
                    refine ⟨172125561796095766158397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 918002996245844086178117 172125561796095766158397)
                    ·
                      refine ⟨64547085673535912309399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 172125561796095766158397 64547085673535912309399)
                      ·
                        rfl

theorem cell23_125705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 4, 3].length) (baseStart_125705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125705 prefixEnd_125705 := by exact prefixLift 125705
  have htrace : WordTrace (prefixWord ++ tailWord_125705) baseStart_125705 baseEnd_125705 := by
    simpa [prefixWord, tailWord_125705, baseEnd_125705] using wordTrace_append hprefix tailTrace_125705
  have hstable : (prefixWord ++ tailWord_125705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125705).length < 2 ^ (prefixWord ++ tailWord_125705).sum := by decide
  have hdescent : baseEnd_125705 < baseStart_125705 := by decide
  rcases family_descends (prefixWord ++ tailWord_125705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125719 : List Nat := [1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 4]
def baseStart_125719 : Nat := 118140960795 + 125719 * 2 ^ 59
def prefixEnd_125719 : Nat := 4983230072969 + 3 ^ 40 * 125719 * 2
def baseEnd_125719 : Nat := 64554274402698857534335

theorem tailTrace_125719 : CollatzResearch.WordTrace tailWord_125719 prefixEnd_125719 64554274402698857534335 := by
  unfold tailWord_125719
  simp only [CollatzResearch.WordTrace]
  refine ⟨4585348631549008940908211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3056899087699339293938807 4585348631549008940908211)
  ·
    refine ⟨6878022947323513411362317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4585348631549008940908211 6878022947323513411362317)
    ·
      refine ⟨2579258605246317529260869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6878022947323513411362317 2579258605246317529260869)
      ·
        refine ⟨483610988483684536736413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2579258605246317529260869 483610988483684536736413)
        ·
          refine ⟨181354120681381701276155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 483610988483684536736413 181354120681381701276155)
          ·
            refine ⟨272031181022072551914233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181354120681381701276155 272031181022072551914233)
            ·
              refine ⟨204023385766554413935675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272031181022072551914233 204023385766554413935675)
              ·
                refine ⟨306035078649831620903513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204023385766554413935675 306035078649831620903513)
                ·
                  refine ⟨229526308987373715677635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306035078649831620903513 229526308987373715677635)
                  ·
                    refine ⟨344289463481060573516453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 229526308987373715677635 344289463481060573516453)
                    ·
                      refine ⟨64554274402698857534335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 344289463481060573516453 64554274402698857534335)
                      ·
                        rfl

theorem cell23_125719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_125719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125719 prefixEnd_125719 := by exact prefixLift 125719
  have htrace : WordTrace (prefixWord ++ tailWord_125719) baseStart_125719 baseEnd_125719 := by
    simpa [prefixWord, tailWord_125719, baseEnd_125719] using wordTrace_append hprefix tailTrace_125719
  have hstable : (prefixWord ++ tailWord_125719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125719).length < 2 ^ (prefixWord ++ tailWord_125719).sum := by decide
  have hdescent : baseEnd_125719 < baseStart_125719 := by decide
  rcases family_descends (prefixWord ++ tailWord_125719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125729 : List Nat := [1, 2, 3, 2, 1, 2, 2, 5, 1, 4]
def baseStart_125729 : Nat := 118140960795 + 125729 * 2 ^ 59
def prefixEnd_125729 : Nat := 4983230072969 + 3 ^ 40 * 125729 * 2
def baseEnd_125729 : Nat := 21519803069747939469763

theorem tailTrace_125729 : CollatzResearch.WordTrace tailWord_125729 prefixEnd_125729 21519803069747939469763 := by
  unfold tailWord_125729
  simp only [CollatzResearch.WordTrace]
  refine ⟨4585713361512780648772241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3057142241008520432514827 4585713361512780648772241)
  ·
    refine ⟨3439285021134585486579181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4585713361512780648772241 3439285021134585486579181)
    ·
      refine ⟨1289731882925469557467193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3439285021134585486579181 1289731882925469557467193)
      ·
        refine ⟨967298912194102168100395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1289731882925469557467193 967298912194102168100395)
        ·
          refine ⟨1450948368291153252150593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 967298912194102168100395 1450948368291153252150593)
          ·
            refine ⟨1088211276218364939112945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1450948368291153252150593 1088211276218364939112945)
            ·
              refine ⟨816158457163773704334709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1088211276218364939112945 816158457163773704334709)
              ·
                refine ⟨76514855359103784781379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 816158457163773704334709 76514855359103784781379)
                ·
                  refine ⟨114772283038655677172069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76514855359103784781379 114772283038655677172069)
                  ·
                    refine ⟨21519803069747939469763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114772283038655677172069 21519803069747939469763)
                    ·
                      rfl

theorem cell23_125729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_125729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125729 prefixEnd_125729 := by exact prefixLift 125729
  have htrace : WordTrace (prefixWord ++ tailWord_125729) baseStart_125729 baseEnd_125729 := by
    simpa [prefixWord, tailWord_125729, baseEnd_125729] using wordTrace_append hprefix tailTrace_125729
  have hstable : (prefixWord ++ tailWord_125729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125729).length < 2 ^ (prefixWord ++ tailWord_125729).sum := by decide
  have hdescent : baseEnd_125729 < baseStart_125729 := by decide
  rcases family_descends (prefixWord ++ tailWord_125729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125745 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 1, 2, 6]
def baseStart_125745 : Nat := 118140960795 + 125745 * 2 ^ 59
def prefixEnd_125745 : Nat := 4983230072969 + 3 ^ 40 * 125745 * 2
def baseEnd_125745 : Nat := 64567624899715755809215

theorem tailTrace_125745 : CollatzResearch.WordTrace tailWord_125745 prefixEnd_125745 64567624899715755809215 := by
  unfold tailWord_125745
  simp only [CollatzResearch.WordTrace]
  refine ⟨4586296929454815381354689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3057531286303210254236459 4586296929454815381354689)
  ·
    refine ⟨3439722697091111536016017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4586296929454815381354689 3439722697091111536016017)
    ·
      refine ⟨2579792022818333652012013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3439722697091111536016017 2579792022818333652012013)
      ·
        refine ⟨967422008556875119504505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2579792022818333652012013 967422008556875119504505)
        ·
          refine ⟨725566506417656339628379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 967422008556875119504505 725566506417656339628379)
          ·
            refine ⟨1088349759626484509442569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725566506417656339628379 1088349759626484509442569)
            ·
              refine ⟨816262319719863382081927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1088349759626484509442569 816262319719863382081927)
              ·
                refine ⟨1224393479579795073122891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 816262319719863382081927 1224393479579795073122891)
                ·
                  refine ⟨1836590219369692609684337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1224393479579795073122891 1836590219369692609684337)
                  ·
                    refine ⟨1377442664527269457263253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1836590219369692609684337 1377442664527269457263253)
                    ·
                      refine ⟨64567624899715755809215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1377442664527269457263253 64567624899715755809215)
                      ·
                        rfl

theorem cell23_125745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_125745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125745 prefixEnd_125745 := by exact prefixLift 125745
  have htrace : WordTrace (prefixWord ++ tailWord_125745) baseStart_125745 baseEnd_125745 := by
    simpa [prefixWord, tailWord_125745, baseEnd_125745] using wordTrace_append hprefix tailTrace_125745
  have hstable : (prefixWord ++ tailWord_125745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125745).length < 2 ^ (prefixWord ++ tailWord_125745).sum := by decide
  have hdescent : baseEnd_125745 < baseStart_125745 := by decide
  rcases family_descends (prefixWord ++ tailWord_125745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125769 : List Nat := [1, 2, 1, 1, 2, 6, 1, 2, 3, 1, 3]
def baseStart_125769 : Nat := 118140960795 + 125769 * 2 ^ 59
def prefixEnd_125769 : Nat := 4983230072969 + 3 ^ 40 * 125769 * 2
def baseEnd_125769 : Nat := 64579948435423661909105

theorem tailTrace_125769 : CollatzResearch.WordTrace tailWord_125769 prefixEnd_125769 64579948435423661909105 := by
  unfold tailWord_125769
  simp only [CollatzResearch.WordTrace]
  refine ⟨4587172281367867480228361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3058114854245244986818907 4587172281367867480228361)
  ·
    refine ⟨3440379211025900610171271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4587172281367867480228361 3440379211025900610171271)
    ·
      refine ⟨5160568816538850915256907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3440379211025900610171271 5160568816538850915256907)
      ·
        refine ⟨7740853224808276372885361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5160568816538850915256907 7740853224808276372885361)
        ·
          refine ⟨5805639918606207279664021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7740853224808276372885361 5805639918606207279664021)
          ·
            refine ⟨272139371184665966234251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5805639918606207279664021 272139371184665966234251)
            ·
              refine ⟨408209056776998949351377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272139371184665966234251 408209056776998949351377)
              ·
                refine ⟨306156792582749212013533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408209056776998949351377 306156792582749212013533)
                ·
                  refine ⟨114808797218530954505075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306156792582749212013533 114808797218530954505075)
                  ·
                    refine ⟨172213195827796431757613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114808797218530954505075 172213195827796431757613)
                    ·
                      refine ⟨64579948435423661909105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 172213195827796431757613 64579948435423661909105)
                      ·
                        rfl

theorem cell23_125769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 1, 3].length) (baseStart_125769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125769 prefixEnd_125769 := by exact prefixLift 125769
  have htrace : WordTrace (prefixWord ++ tailWord_125769) baseStart_125769 baseEnd_125769 := by
    simpa [prefixWord, tailWord_125769, baseEnd_125769] using wordTrace_append hprefix tailTrace_125769
  have hstable : (prefixWord ++ tailWord_125769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125769).length < 2 ^ (prefixWord ++ tailWord_125769).sum := by decide
  have hdescent : baseEnd_125769 < baseStart_125769 := by decide
  rcases family_descends (prefixWord ++ tailWord_125769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125772 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 3, 5]
def baseStart_125772 : Nat := 118140960795 + 125772 * 2 ^ 59
def prefixEnd_125772 : Nat := 4983230072969 + 3 ^ 40 * 125772 * 2
def baseEnd_125772 : Nat := 21527162959129050057197

theorem tailTrace_125772 : CollatzResearch.WordTrace tailWord_125772 prefixEnd_125772 21527162959129050057197 := by
  unfold tailWord_125772
  simp only [CollatzResearch.WordTrace]
  refine ⟨2293640850178499496293785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3058187800237999328391713 2293640850178499496293785)
  ·
    refine ⟨1720230637633874622220339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2293640850178499496293785 1720230637633874622220339)
    ·
      refine ⟨2580345956450811933330509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1720230637633874622220339 2580345956450811933330509)
      ·
        refine ⟨967629733669054474998941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2580345956450811933330509 967629733669054474998941)
        ·
          refine ⟨362861150125895428124603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 967629733669054474998941 362861150125895428124603)
          ·
            refine ⟨544291725188843142186905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362861150125895428124603 544291725188843142186905)
            ·
              refine ⟨408218793891632356640179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544291725188843142186905 408218793891632356640179)
              ·
                refine ⟨612328190837448534960269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408218793891632356640179 612328190837448534960269)
                ·
                  refine ⟨229623071564043200610101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612328190837448534960269 229623071564043200610101)
                  ·
                    refine ⟨21527162959129050057197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 229623071564043200610101 21527162959129050057197)
                    ·
                      rfl

theorem cell23_125772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_125772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125772 prefixEnd_125772 := by exact prefixLift 125772
  have htrace : WordTrace (prefixWord ++ tailWord_125772) baseStart_125772 baseEnd_125772 := by
    simpa [prefixWord, tailWord_125772, baseEnd_125772] using wordTrace_append hprefix tailTrace_125772
  have hstable : (prefixWord ++ tailWord_125772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125772).length < 2 ^ (prefixWord ++ tailWord_125772).sum := by decide
  have hdescent : baseEnd_125772 < baseStart_125772 := by decide
  rcases family_descends (prefixWord ++ tailWord_125772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125773 : List Nat := [1, 6, 1, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_125773 : Nat := 118140960795 + 125773 * 2 ^ 59
def prefixEnd_125773 : Nat := 4983230072969 + 3 ^ 40 * 125773 * 2
def baseEnd_125773 : Nat := 64582002358041646259087

theorem tailTrace_125773 : CollatzResearch.WordTrace tailWord_125773 prefixEnd_125773 64582002358041646259087 := by
  unfold tailWord_125773
  simp only [CollatzResearch.WordTrace]
  refine ⟨4587318173353376163373973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3058212115568917442249315 4587318173353376163373973)
  ·
    refine ⟨215030539375939507658155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4587318173353376163373973 215030539375939507658155)
    ·
      refine ⟨322545809063909261487233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215030539375939507658155 322545809063909261487233)
      ·
        refine ⟨241909356797931946115425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322545809063909261487233 241909356797931946115425)
        ·
          refine ⟨181432017598448959586569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241909356797931946115425 181432017598448959586569)
          ·
            refine ⟨136074013198836719689927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181432017598448959586569 136074013198836719689927)
            ·
              refine ⟨204111019798255079534891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136074013198836719689927 204111019798255079534891)
              ·
                refine ⟨306166529697382619302337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204111019798255079534891 306166529697382619302337)
                ·
                  refine ⟨229624897273036964476753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306166529697382619302337 229624897273036964476753)
                  ·
                    refine ⟨172218672954777723357565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 229624897273036964476753 172218672954777723357565)
                    ·
                      refine ⟨64582002358041646259087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 172218672954777723357565 64582002358041646259087)
                      ·
                        rfl

theorem cell23_125773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_125773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125773 prefixEnd_125773 := by exact prefixLift 125773
  have htrace : WordTrace (prefixWord ++ tailWord_125773) baseStart_125773 baseEnd_125773 := by
    simpa [prefixWord, tailWord_125773, baseEnd_125773] using wordTrace_append hprefix tailTrace_125773
  have hstable : (prefixWord ++ tailWord_125773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125773).length < 2 ^ (prefixWord ++ tailWord_125773).sum := by decide
  have hdescent : baseEnd_125773 < baseStart_125773 := by decide
  rcases family_descends (prefixWord ++ tailWord_125773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125786 : List Nat := [3, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3]
def baseStart_125786 : Nat := 118140960795 + 125786 * 2 ^ 59
def prefixEnd_125786 : Nat := 4983230072969 + 3 ^ 40 * 125786 * 2
def baseEnd_125786 : Nat := 64588677606550095396527

theorem tailTrace_125786 : CollatzResearch.WordTrace tailWord_125786 prefixEnd_125786 64588677606550095396527 := by
  unfold tailWord_125786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1146948080576569845899303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3058528214870852922398141 1146948080576569845899303)
  ·
    refine ⟨1720422120864854768848955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1146948080576569845899303 1720422120864854768848955)
    ·
      refine ⟨2580633181297282153273433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1720422120864854768848955 2580633181297282153273433)
      ·
        refine ⟨1935474885972961614955075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2580633181297282153273433 1935474885972961614955075)
        ·
          refine ⟨2903212328959442422432613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1935474885972961614955075 2903212328959442422432613)
          ·
            refine ⟨544352311679895454206115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2903212328959442422432613 544352311679895454206115)
            ·
              refine ⟨816528467519843181309173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544352311679895454206115 816528467519843181309173)
              ·
                refine ⟨76549543829985298247735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 816528467519843181309173 76549543829985298247735)
                ·
                  refine ⟨114824315744977947371603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76549543829985298247735 114824315744977947371603)
                  ·
                    refine ⟨172236473617466921057405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114824315744977947371603 172236473617466921057405)
                    ·
                      refine ⟨64588677606550095396527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 172236473617466921057405 64588677606550095396527)
                      ·
                        rfl

theorem cell23_125786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3].length) (baseStart_125786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125786 prefixEnd_125786 := by exact prefixLift 125786
  have htrace : WordTrace (prefixWord ++ tailWord_125786) baseStart_125786 baseEnd_125786 := by
    simpa [prefixWord, tailWord_125786, baseEnd_125786] using wordTrace_append hprefix tailTrace_125786
  have hstable : (prefixWord ++ tailWord_125786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125786).length < 2 ^ (prefixWord ++ tailWord_125786).sum := by decide
  have hdescent : baseEnd_125786 < baseStart_125786 := by decide
  rcases family_descends (prefixWord ++ tailWord_125786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125829 : List Nat := [1, 3, 1, 1, 3, 3, 1, 4, 1, 2, 3]
def baseStart_125829 : Nat := 118140960795 + 125829 * 2 ^ 59
def prefixEnd_125829 : Nat := 4983230072969 + 3 ^ 40 * 125829 * 2
def baseEnd_125829 : Nat := 64610757274693427158829

theorem tailTrace_125829 : CollatzResearch.WordTrace tailWord_125829 prefixEnd_125829 64610757274693427158829 := by
  unfold tailWord_125829
  simp only [CollatzResearch.WordTrace]
  refine ⟨4589360661150497727412541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3059573774100331818275027 4589360661150497727412541)
  ·
    refine ⟨1721010247931436647779703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4589360661150497727412541 1721010247931436647779703)
    ·
      refine ⟨2581515371897154971669555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1721010247931436647779703 2581515371897154971669555)
      ·
        refine ⟨3872273057845732457504333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2581515371897154971669555 3872273057845732457504333)
        ·
          refine ⟨1452102396692149671564125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3872273057845732457504333 1452102396692149671564125)
          ·
            refine ⟨544538398759556126836547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1452102396692149671564125 544538398759556126836547)
            ·
              refine ⟨816807598139334190254821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544538398759556126836547 816807598139334190254821)
              ·
                refine ⟨153151424651125160672779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 816807598139334190254821 153151424651125160672779)
                ·
                  refine ⟨229727136976687741009169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153151424651125160672779 229727136976687741009169)
                  ·
                    refine ⟨172295352732515805756877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 229727136976687741009169 172295352732515805756877)
                    ·
                      refine ⟨64610757274693427158829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 172295352732515805756877 64610757274693427158829)
                      ·
                        rfl

theorem cell23_125829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 2, 3].length) (baseStart_125829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125829 prefixEnd_125829 := by exact prefixLift 125829
  have htrace : WordTrace (prefixWord ++ tailWord_125829) baseStart_125829 baseEnd_125829 := by
    simpa [prefixWord, tailWord_125829, baseEnd_125829] using wordTrace_append hprefix tailTrace_125829
  have hstable : (prefixWord ++ tailWord_125829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125829).length < 2 ^ (prefixWord ++ tailWord_125829).sum := by decide
  have hdescent : baseEnd_125829 < baseStart_125829 := by decide
  rcases family_descends (prefixWord ++ tailWord_125829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125832 : List Nat := [2, 1, 3, 3, 2, 2, 1, 9]
def baseStart_125832 : Nat := 118140960795 + 125832 * 2 ^ 59
def prefixEnd_125832 : Nat := 4983230072969 + 3 ^ 40 * 125832 * 2
def baseEnd_125832 : Nat := 2393048063579885756345

theorem tailTrace_125832 : CollatzResearch.WordTrace tailWord_125832 prefixEnd_125832 2393048063579885756345 := by
  unfold tailWord_125832
  simp only [CollatzResearch.WordTrace]
  refine ⟨2294735040069814619885875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3059646720093086159847833 2294735040069814619885875)
  ·
    refine ⟨3442102560104721929828813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2294735040069814619885875 3442102560104721929828813)
    ·
      refine ⟨1290788460039270723685805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3442102560104721929828813 1290788460039270723685805)
      ·
        refine ⟨484045672514726521382177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1290788460039270723685805 484045672514726521382177)
        ·
          refine ⟨363034254386044891036633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484045672514726521382177 363034254386044891036633)
          ·
            refine ⟨272275690789533668277475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363034254386044891036633 272275690789533668277475)
            ·
              refine ⟨408413536184300502416213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272275690789533668277475 408413536184300502416213)
              ·
                refine ⟨2393048063579885756345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 408413536184300502416213 2393048063579885756345)
                ·
                  rfl

theorem cell23_125832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 9].length) (baseStart_125832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125832 prefixEnd_125832 := by exact prefixLift 125832
  have htrace : WordTrace (prefixWord ++ tailWord_125832) baseStart_125832 baseEnd_125832 := by
    simpa [prefixWord, tailWord_125832, baseEnd_125832] using wordTrace_append hprefix tailTrace_125832
  have hstable : (prefixWord ++ tailWord_125832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125832).length < 2 ^ (prefixWord ++ tailWord_125832).sum := by decide
  have hdescent : baseEnd_125832 < baseStart_125832 := by decide
  rcases family_descends (prefixWord ++ tailWord_125832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125859 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 4, 1, 3]
def baseStart_125859 : Nat := 118140960795 + 125859 * 2 ^ 59
def prefixEnd_125859 : Nat := 4983230072969 + 3 ^ 40 * 125859 * 2
def baseEnd_125859 : Nat := 64626161694328309783691

theorem tailTrace_125859 : CollatzResearch.WordTrace tailWord_125859 prefixEnd_125859 64626161694328309783691 := by
  unfold tailWord_125859
  simp only [CollatzResearch.WordTrace]
  refine ⟨4590454851041812851004631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3060303234027875234003087 4590454851041812851004631)
  ·
    refine ⟨6885682276562719276506947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4590454851041812851004631 6885682276562719276506947)
    ·
      refine ⟨10328523414844078914760421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6885682276562719276506947 10328523414844078914760421)
      ·
        refine ⟨1936598140283264796517579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10328523414844078914760421 1936598140283264796517579)
        ·
          refine ⟨2904897210424897194776369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1936598140283264796517579 2904897210424897194776369)
          ·
            refine ⟨2178672907818672896082277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2904897210424897194776369 2178672907818672896082277)
            ·
              refine ⟨408501170216001168015427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2178672907818672896082277 408501170216001168015427)
              ·
                refine ⟨612751755324001752023141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408501170216001168015427 612751755324001752023141)
                ·
                  refine ⟨114890954123250328504339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 612751755324001752023141 114890954123250328504339)
                  ·
                    refine ⟨172336431184875492756509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114890954123250328504339 172336431184875492756509)
                    ·
                      refine ⟨64626161694328309783691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 172336431184875492756509 64626161694328309783691)
                      ·
                        rfl

theorem cell23_125859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_125859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125859 prefixEnd_125859 := by exact prefixLift 125859
  have htrace : WordTrace (prefixWord ++ tailWord_125859) baseStart_125859 baseEnd_125859 := by
    simpa [prefixWord, tailWord_125859, baseEnd_125859] using wordTrace_append hprefix tailTrace_125859
  have hstable : (prefixWord ++ tailWord_125859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125859).length < 2 ^ (prefixWord ++ tailWord_125859).sum := by decide
  have hdescent : baseEnd_125859 < baseStart_125859 := by decide
  rcases family_descends (prefixWord ++ tailWord_125859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125860 : List Nat := [2, 3, 1, 2, 1, 2, 5, 2, 1, 2, 2]
def baseStart_125860 : Nat := 118140960795 + 125860 * 2 ^ 59
def prefixEnd_125860 : Nat := 4983230072969 + 3 ^ 40 * 125860 * 2
def baseEnd_125860 : Nat := 64626675174982805871187

theorem tailTrace_125860 : CollatzResearch.WordTrace tailWord_125860 prefixEnd_125860 64626675174982805871187 := by
  unfold tailWord_125860
  simp only [CollatzResearch.WordTrace]
  refine ⟨2295245662019095010895517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3060327549358793347860689 2295245662019095010895517)
  ·
    refine ⟨860717123257160629085819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2295245662019095010895517 860717123257160629085819)
    ·
      refine ⟨1291075684885740943628729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 860717123257160629085819 1291075684885740943628729)
      ·
        refine ⟨968306763664305707721547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1291075684885740943628729 968306763664305707721547)
        ·
          refine ⟨1452460145496458561582321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968306763664305707721547 1452460145496458561582321)
          ·
            refine ⟨1089345109122343921186741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1452460145496458561582321 1089345109122343921186741)
            ·
              refine ⟨102126103980219742611257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1089345109122343921186741 102126103980219742611257)
              ·
                refine ⟨76594577985164806958443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102126103980219742611257 76594577985164806958443)
                ·
                  refine ⟨114891866977747210437665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76594577985164806958443 114891866977747210437665)
                  ·
                    refine ⟨86168900233310407828249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114891866977747210437665 86168900233310407828249)
                    ·
                      refine ⟨64626675174982805871187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 86168900233310407828249 64626675174982805871187)
                      ·
                        rfl

theorem cell23_125860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_125860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125860 prefixEnd_125860 := by exact prefixLift 125860
  have htrace : WordTrace (prefixWord ++ tailWord_125860) baseStart_125860 baseEnd_125860 := by
    simpa [prefixWord, tailWord_125860, baseEnd_125860] using wordTrace_append hprefix tailTrace_125860
  have hstable : (prefixWord ++ tailWord_125860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125860).length < 2 ^ (prefixWord ++ tailWord_125860).sum := by decide
  have hdescent : baseEnd_125860 < baseStart_125860 := by decide
  rcases family_descends (prefixWord ++ tailWord_125860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125886 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2]
def baseStart_125886 : Nat := 118140960795 + 125886 * 2 ^ 59
def prefixEnd_125886 : Nat := 4983230072969 + 3 ^ 40 * 125886 * 2
def baseEnd_125886 : Nat := 64640025671999704146067

theorem tailTrace_125886 : CollatzResearch.WordTrace tailWord_125886 prefixEnd_125886 64640025671999704146067 := by
  unfold tailWord_125886
  simp only [CollatzResearch.WordTrace]
  refine ⟨573929952742999557779689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3060959747962664308158341 573929952742999557779689)
  ·
    refine ⟨430447464557249668334767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 573929952742999557779689 430447464557249668334767)
    ·
      refine ⟨645671196835874502502151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430447464557249668334767 645671196835874502502151)
      ·
        refine ⟨968506795253811753753227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645671196835874502502151 968506795253811753753227)
        ·
          refine ⟨1452760192880717630629841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968506795253811753753227 1452760192880717630629841)
          ·
            refine ⟨1089570144660538222972381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1452760192880717630629841 1089570144660538222972381)
            ·
              refine ⟨408588804247701833614643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1089570144660538222972381 408588804247701833614643)
              ·
                refine ⟨612883206371552750421965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408588804247701833614643 612883206371552750421965)
                ·
                  refine ⟨229831202389332281408237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 612883206371552750421965 229831202389332281408237)
                  ·
                    refine ⟨86186700895999605528089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 229831202389332281408237 86186700895999605528089)
                    ·
                      refine ⟨64640025671999704146067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 86186700895999605528089 64640025671999704146067)
                      ·
                        rfl

theorem cell23_125886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_125886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125886 prefixEnd_125886 := by exact prefixLift 125886
  have htrace : WordTrace (prefixWord ++ tailWord_125886) baseStart_125886 baseEnd_125886 := by
    simpa [prefixWord, tailWord_125886, baseEnd_125886] using wordTrace_append hprefix tailTrace_125886
  have hstable : (prefixWord ++ tailWord_125886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125886).length < 2 ^ (prefixWord ++ tailWord_125886).sum := by decide
  have hdescent : baseEnd_125886 < baseStart_125886 := by decide
  rcases family_descends (prefixWord ++ tailWord_125886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125894 : List Nat := [6, 1, 3, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_125894 : Nat := 118140960795 + 125894 * 2 ^ 59
def prefixEnd_125894 : Nat := 4983230072969 + 3 ^ 40 * 125894 * 2
def baseEnd_125894 : Nat := 64644133517235672846031

theorem tailTrace_125894 : CollatzResearch.WordTrace tailWord_125894 prefixEnd_125894 64644133517235672846031 := by
  unfold tailWord_125894
  simp only [CollatzResearch.WordTrace]
  refine ⟨143491606434844182141523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3061154270610009219019157 143491606434844182141523)
  ·
    refine ⟨215237409652266273212285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143491606434844182141523 215237409652266273212285)
    ·
      refine ⟨80714028619599852454607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215237409652266273212285 80714028619599852454607)
      ·
        refine ⟨121071042929399778681911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80714028619599852454607 121071042929399778681911)
        ·
          refine ⟨181606564394099668022867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121071042929399778681911 181606564394099668022867)
          ·
            refine ⟨272409846591149502034301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181606564394099668022867 272409846591149502034301)
            ·
              refine ⟨102153692471681063262863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272409846591149502034301 102153692471681063262863)
              ·
                refine ⟨153230538707521594894295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102153692471681063262863 153230538707521594894295)
                ·
                  refine ⟨229845808061282392341443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153230538707521594894295 229845808061282392341443)
                  ·
                    refine ⟨344768712091923588512165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 229845808061282392341443 344768712091923588512165)
                    ·
                      refine ⟨64644133517235672846031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 344768712091923588512165 64644133517235672846031)
                      ·
                        rfl

theorem cell23_125894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_125894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125894 prefixEnd_125894 := by exact prefixLift 125894
  have htrace : WordTrace (prefixWord ++ tailWord_125894) baseStart_125894 baseEnd_125894 := by
    simpa [prefixWord, tailWord_125894, baseEnd_125894] using wordTrace_append hprefix tailTrace_125894
  have hstable : (prefixWord ++ tailWord_125894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125894).length < 2 ^ (prefixWord ++ tailWord_125894).sum := by decide
  have hdescent : baseEnd_125894 < baseStart_125894 := by decide
  rcases family_descends (prefixWord ++ tailWord_125894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125899 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 3, 4, 2]
def baseStart_125899 : Nat := 118140960795 + 125899 * 2 ^ 59
def prefixEnd_125899 : Nat := 4983230072969 + 3 ^ 40 * 125899 * 2
def baseEnd_125899 : Nat := 64646700920508153283507

theorem tailTrace_125899 : CollatzResearch.WordTrace tailWord_125899 prefixEnd_125899 64646700920508153283507 := by
  unfold tailWord_125899
  simp only [CollatzResearch.WordTrace]
  refine ⟨4591913770896899682460751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3061275847264599788307167 4591913770896899682460751)
  ·
    refine ⟨6887870656345349523691127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4591913770896899682460751 6887870656345349523691127)
    ·
      refine ⟨10331805984518024285536691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6887870656345349523691127 10331805984518024285536691)
      ·
        refine ⟨15497708976777036428305037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10331805984518024285536691 15497708976777036428305037)
        ·
          refine ⟨5811640866291388660614389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15497708976777036428305037 5811640866291388660614389)
          ·
            refine ⟨544841331214817686932599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5811640866291388660614389 544841331214817686932599)
            ·
              refine ⟨817261996822226530398899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544841331214817686932599 817261996822226530398899)
              ·
                refine ⟨1225892995233339795598349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817261996822226530398899 1225892995233339795598349)
                ·
                  refine ⟨459709873212502423349381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225892995233339795598349 459709873212502423349381)
                  ·
                    refine ⟨86195601227344204378009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 459709873212502423349381 86195601227344204378009)
                    ·
                      refine ⟨64646700920508153283507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 86195601227344204378009 64646700920508153283507)
                      ·
                        rfl

theorem cell23_125899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 4, 2].length) (baseStart_125899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125899 prefixEnd_125899 := by exact prefixLift 125899
  have htrace : WordTrace (prefixWord ++ tailWord_125899) baseStart_125899 baseEnd_125899 := by
    simpa [prefixWord, tailWord_125899, baseEnd_125899] using wordTrace_append hprefix tailTrace_125899
  have hstable : (prefixWord ++ tailWord_125899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125899).length < 2 ^ (prefixWord ++ tailWord_125899).sum := by decide
  have hdescent : baseEnd_125899 < baseStart_125899 := by decide
  rcases family_descends (prefixWord ++ tailWord_125899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125903 : List Nat := [1, 1, 2, 1, 1, 7, 3, 1, 1, 3, 2]
def baseStart_125903 : Nat := 118140960795 + 125903 * 2 ^ 59
def prefixEnd_125903 : Nat := 4983230072969 + 3 ^ 40 * 125903 * 2
def baseEnd_125903 : Nat := 64648754843126137633489

theorem tailTrace_125903 : CollatzResearch.WordTrace tailWord_125903 prefixEnd_125903 64648754843126137633489 := by
  unfold tailWord_125903
  simp only [CollatzResearch.WordTrace]
  refine ⟨4592059662882408365606363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3061373108588272243737575 4592059662882408365606363)
  ·
    refine ⟨6888089494323612548409545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4592059662882408365606363 6888089494323612548409545)
    ·
      refine ⟨5166067120742709411307159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6888089494323612548409545 5166067120742709411307159)
      ·
        refine ⟨7749100681114064116960739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5166067120742709411307159 7749100681114064116960739)
        ·
          refine ⟨11623651021671096175441109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7749100681114064116960739 11623651021671096175441109)
          ·
            refine ⟨272429320820416316611901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 11623651021671096175441109 272429320820416316611901)
            ·
              refine ⟨102160995307656118729463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272429320820416316611901 102160995307656118729463)
              ·
                refine ⟨153241492961484178094195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102160995307656118729463 153241492961484178094195)
                ·
                  refine ⟨229862239442226267141293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153241492961484178094195 229862239442226267141293)
                  ·
                    refine ⟨86198339790834850177985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 229862239442226267141293 86198339790834850177985)
                    ·
                      refine ⟨64648754843126137633489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 86198339790834850177985 64648754843126137633489)
                      ·
                        rfl

theorem cell23_125903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 1, 3, 2].length) (baseStart_125903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125903 prefixEnd_125903 := by exact prefixLift 125903
  have htrace : WordTrace (prefixWord ++ tailWord_125903) baseStart_125903 baseEnd_125903 := by
    simpa [prefixWord, tailWord_125903, baseEnd_125903] using wordTrace_append hprefix tailTrace_125903
  have hstable : (prefixWord ++ tailWord_125903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125903).length < 2 ^ (prefixWord ++ tailWord_125903).sum := by decide
  have hdescent : baseEnd_125903 < baseStart_125903 := by decide
  rcases family_descends (prefixWord ++ tailWord_125903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125910 : List Nat := [5, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_125910 : Nat := 118140960795 + 125910 * 2 ^ 59
def prefixEnd_125910 : Nat := 4983230072969 + 3 ^ 40 * 125910 * 2
def baseEnd_125910 : Nat := 64652349207707610245957

theorem tailTrace_125910 : CollatzResearch.WordTrace tailWord_125910 prefixEnd_125910 64652349207707610245957 := by
  unfold tailWord_125910
  simp only [CollatzResearch.WordTrace]
  refine ⟨287019685866065535069449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3061543315904699040740789 287019685866065535069449)
  ·
    refine ⟨215264764399549151302087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287019685866065535069449 215264764399549151302087)
    ·
      refine ⟨322897146599323726953131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215264764399549151302087 322897146599323726953131)
      ·
        refine ⟨484345719898985590429697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322897146599323726953131 484345719898985590429697)
        ·
          refine ⟨363259289924239192822273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 484345719898985590429697 363259289924239192822273)
          ·
            refine ⟨272444467443179394616705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363259289924239192822273 272444467443179394616705)
            ·
              refine ⟨204333350582384545962529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272444467443179394616705 204333350582384545962529)
              ·
                refine ⟨153250012936788409471897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204333350582384545962529 153250012936788409471897)
                ·
                  refine ⟨114937509702591307103923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153250012936788409471897 114937509702591307103923)
                  ·
                    refine ⟨172406264553886960655885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114937509702591307103923 172406264553886960655885)
                    ·
                      refine ⟨64652349207707610245957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 172406264553886960655885 64652349207707610245957)
                      ·
                        rfl

theorem cell23_125910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_125910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125910 prefixEnd_125910 := by exact prefixLift 125910
  have htrace : WordTrace (prefixWord ++ tailWord_125910) baseStart_125910 baseEnd_125910 := by
    simpa [prefixWord, tailWord_125910, baseEnd_125910] using wordTrace_append hprefix tailTrace_125910
  have hstable : (prefixWord ++ tailWord_125910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125910).length < 2 ^ (prefixWord ++ tailWord_125910).sum := by decide
  have hdescent : baseEnd_125910 < baseStart_125910 := by decide
  rcases family_descends (prefixWord ++ tailWord_125910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_125954 : List Nat := [3, 4, 1, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_125954 : Nat := 118140960795 + 125954 * 2 ^ 59
def prefixEnd_125954 : Nat := 4983230072969 + 3 ^ 40 * 125954 * 2
def baseEnd_125954 : Nat := 64674942356505438095755

theorem tailTrace_125954 : CollatzResearch.WordTrace tailWord_125954 prefixEnd_125954 64674942356505438095755 := by
  unfold tailWord_125954
  simp only [CollatzResearch.WordTrace]
  refine ⟨1148479946424411018928229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3062613190465096050475277 1148479946424411018928229)
  ·
    refine ⟨215339989954577066049043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1148479946424411018928229 215339989954577066049043)
    ·
      refine ⟨323009984931865599073565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215339989954577066049043 323009984931865599073565)
      ·
        refine ⟨121128744349449599652587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323009984931865599073565 121128744349449599652587)
        ·
          refine ⟨181693116524174399478881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121128744349449599652587 181693116524174399478881)
          ·
            refine ⟨136269837393130799609161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181693116524174399478881 136269837393130799609161)
            ·
              refine ⟨102202378044848099706871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136269837393130799609161 102202378044848099706871)
              ·
                refine ⟨153303567067272149560307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102202378044848099706871 153303567067272149560307)
                ·
                  refine ⟨229955350600908224340461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153303567067272149560307 229955350600908224340461)
                  ·
                    refine ⟨86233256475340584127673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 229955350600908224340461 86233256475340584127673)
                    ·
                      refine ⟨64674942356505438095755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 86233256475340584127673 64674942356505438095755)
                      ·
                        rfl

theorem cell23_125954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_125954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_125954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_125954 prefixEnd_125954 := by exact prefixLift 125954
  have htrace : WordTrace (prefixWord ++ tailWord_125954) baseStart_125954 baseEnd_125954 := by
    simpa [prefixWord, tailWord_125954, baseEnd_125954] using wordTrace_append hprefix tailTrace_125954
  have hstable : (prefixWord ++ tailWord_125954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_125954).length < 2 ^ (prefixWord ++ tailWord_125954).sum := by decide
  have hdescent : baseEnd_125954 < baseStart_125954 := by decide
  rcases family_descends (prefixWord ++ tailWord_125954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126006 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_126006 : Nat := 118140960795 + 126006 * 2 ^ 59
def prefixEnd_126006 : Nat := 4983230072969 + 3 ^ 40 * 126006 * 2
def baseEnd_126006 : Nat := 64701643350539234645515

theorem tailTrace_126006 : CollatzResearch.WordTrace tailWord_126006 prefixEnd_126006 64701643350539234645515 := by
  unfold tailWord_126006
  simp only [CollatzResearch.WordTrace]
  refine ⟨287238523844328559787867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3063877587672837971070581 287238523844328559787867)
  ·
    refine ⟨430857785766492839681801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287238523844328559787867 430857785766492839681801)
    ·
      refine ⟨323143339324869629761351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430857785766492839681801 323143339324869629761351)
      ·
        refine ⟨484715008987304444642027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323143339324869629761351 484715008987304444642027)
        ·
          refine ⟨727072513480956666963041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484715008987304444642027 727072513480956666963041)
          ·
            refine ⟨545304385110717500222281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 727072513480956666963041 545304385110717500222281)
            ·
              refine ⟨408978288833038125166711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545304385110717500222281 408978288833038125166711)
              ·
                refine ⟨613467433249557187750067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408978288833038125166711 613467433249557187750067)
                ·
                  refine ⟨920201149874335781625101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 613467433249557187750067 920201149874335781625101)
                  ·
                    refine ⟨345075431202875918109413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 920201149874335781625101 345075431202875918109413)
                    ·
                      refine ⟨64701643350539234645515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 345075431202875918109413 64701643350539234645515)
                      ·
                        rfl

theorem cell23_126006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_126006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126006 prefixEnd_126006 := by exact prefixLift 126006
  have htrace : WordTrace (prefixWord ++ tailWord_126006) baseStart_126006 baseEnd_126006 := by
    simpa [prefixWord, tailWord_126006, baseEnd_126006] using wordTrace_append hprefix tailTrace_126006
  have hstable : (prefixWord ++ tailWord_126006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126006).length < 2 ^ (prefixWord ++ tailWord_126006).sum := by decide
  have hdescent : baseEnd_126006 < baseStart_126006 := by decide
  rcases family_descends (prefixWord ++ tailWord_126006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126032 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 8]
def baseStart_126032 : Nat := 118140960795 + 126032 * 2 ^ 59
def prefixEnd_126032 : Nat := 4983230072969 + 3 ^ 40 * 126032 * 2
def baseEnd_126032 : Nat := 64714993847556132920395

theorem tailTrace_126032 : CollatzResearch.WordTrace tailWord_126032 prefixEnd_126032 64714993847556132920395 := by
  unfold tailWord_126032
  simp only [CollatzResearch.WordTrace]
  refine ⟨2298382339707531698526175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3064509786276708931368233 2298382339707531698526175)
  ·
    refine ⟨3447573509561297547789263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2298382339707531698526175 3447573509561297547789263)
    ·
      refine ⟨5171360264341946321683895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3447573509561297547789263 5171360264341946321683895)
      ·
        refine ⟨7757040396512919482525843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5171360264341946321683895 7757040396512919482525843)
        ·
          refine ⟨11635560594769379223788765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7757040396512919482525843 11635560594769379223788765)
          ·
            refine ⟨4363335223038517208920787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11635560594769379223788765 4363335223038517208920787)
            ·
              refine ⟨6545002834557775813381181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4363335223038517208920787 6545002834557775813381181)
              ·
                refine ⟨2454376062959165930017943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6545002834557775813381181 2454376062959165930017943)
                ·
                  refine ⟨3681564094438748895026915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2454376062959165930017943 3681564094438748895026915)
                  ·
                    refine ⟨5522346141658123342540373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3681564094438748895026915 5522346141658123342540373)
                    ·
                      refine ⟨64714993847556132920395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 5522346141658123342540373 64714993847556132920395)
                      ·
                        rfl

theorem cell23_126032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_126032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126032 prefixEnd_126032 := by exact prefixLift 126032
  have htrace : WordTrace (prefixWord ++ tailWord_126032) baseStart_126032 baseEnd_126032 := by
    simpa [prefixWord, tailWord_126032, baseEnd_126032] using wordTrace_append hprefix tailTrace_126032
  have hstable : (prefixWord ++ tailWord_126032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126032).length < 2 ^ (prefixWord ++ tailWord_126032).sum := by decide
  have hdescent : baseEnd_126032 < baseStart_126032 := by decide
  rcases family_descends (prefixWord ++ tailWord_126032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126090 : List Nat := [3, 1, 2, 3, 1, 1, 3, 4, 1, 1, 3]
def baseStart_126090 : Nat := 118140960795 + 126090 * 2 ^ 59
def prefixEnd_126090 : Nat := 4983230072969 + 3 ^ 40 * 126090 * 2
def baseEnd_126090 : Nat := 64744775725516905995129

theorem tailTrace_126090 : CollatzResearch.WordTrace tailWord_126090 prefixEnd_126090 64744775725516905995129 := by
  unfold tailWord_126090
  simp only [CollatzResearch.WordTrace]
  refine ⟨1149720028301234825665931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3065920075469959535109149 1149720028301234825665931)
  ·
    refine ⟨1724580042451852238498897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1149720028301234825665931 1724580042451852238498897)
    ·
      refine ⟨1293435031838889178874173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1724580042451852238498897 1293435031838889178874173)
      ·
        refine ⟨485038136939583442077815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1293435031838889178874173 485038136939583442077815)
        ·
          refine ⟨727557205409375163116723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485038136939583442077815 727557205409375163116723)
          ·
            refine ⟨1091335808114062744675085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727557205409375163116723 1091335808114062744675085)
            ·
              refine ⟨409250928042773529253157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1091335808114062744675085 409250928042773529253157)
              ·
                refine ⟨76734549008020036734967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 409250928042773529253157 76734549008020036734967)
                ·
                  refine ⟨115101823512030055102451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76734549008020036734967 115101823512030055102451)
                  ·
                    refine ⟨172652735268045082653677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115101823512030055102451 172652735268045082653677)
                    ·
                      refine ⟨64744775725516905995129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 172652735268045082653677 64744775725516905995129)
                      ·
                        rfl

theorem cell23_126090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_126090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126090 prefixEnd_126090 := by exact prefixLift 126090
  have htrace : WordTrace (prefixWord ++ tailWord_126090) baseStart_126090 baseEnd_126090 := by
    simpa [prefixWord, tailWord_126090, baseEnd_126090] using wordTrace_append hprefix tailTrace_126090
  have hstable : (prefixWord ++ tailWord_126090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126090).length < 2 ^ (prefixWord ++ tailWord_126090).sum := by decide
  have hdescent : baseEnd_126090 < baseStart_126090 := by decide
  rcases family_descends (prefixWord ++ tailWord_126090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126099 : List Nat := [1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 5]
def baseStart_126099 : Nat := 118140960795 + 126099 * 2 ^ 59
def prefixEnd_126099 : Nat := 4983230072969 + 3 ^ 40 * 126099 * 2
def baseEnd_126099 : Nat := 64749397051407370782587

theorem tailTrace_126099 : CollatzResearch.WordTrace tailWord_126099 prefixEnd_126099 64749397051407370782587 := by
  unfold tailWord_126099
  simp only [CollatzResearch.WordTrace]
  refine ⟨4599208370172333839741351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3066138913448222559827567 4599208370172333839741351)
  ·
    refine ⟨6898812555258500759612027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4599208370172333839741351 6898812555258500759612027)
    ·
      refine ⟨10348218832887751139418041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6898812555258500759612027 10348218832887751139418041)
      ·
        refine ⟨7761164124665813354563531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10348218832887751139418041 7761164124665813354563531)
        ·
          refine ⟨11641746186998720031845297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7761164124665813354563531 11641746186998720031845297)
          ·
            refine ⟨8731309640249040023883973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11641746186998720031845297 8731309640249040023883973)
            ·
              refine ⟨1637120557546695004478245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8731309640249040023883973 1637120557546695004478245)
              ·
                refine ⟨306960104540005313339671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1637120557546695004478245 306960104540005313339671)
                ·
                  refine ⟨460440156810007970009507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306960104540005313339671 460440156810007970009507)
                  ·
                    refine ⟨690660235215011955014261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 460440156810007970009507 690660235215011955014261)
                    ·
                      refine ⟨64749397051407370782587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 690660235215011955014261 64749397051407370782587)
                      ·
                        rfl

theorem cell23_126099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 5].length) (baseStart_126099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126099 prefixEnd_126099 := by exact prefixLift 126099
  have htrace : WordTrace (prefixWord ++ tailWord_126099) baseStart_126099 baseEnd_126099 := by
    simpa [prefixWord, tailWord_126099, baseEnd_126099] using wordTrace_append hprefix tailTrace_126099
  have hstable : (prefixWord ++ tailWord_126099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126099).length < 2 ^ (prefixWord ++ tailWord_126099).sum := by decide
  have hdescent : baseEnd_126099 < baseStart_126099 := by decide
  rcases family_descends (prefixWord ++ tailWord_126099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126106 : List Nat := [3, 1, 1, 5, 1, 1, 1, 3, 1, 6]
def baseStart_126106 : Nat := 118140960795 + 126106 * 2 ^ 59
def prefixEnd_126106 : Nat := 4983230072969 + 3 ^ 40 * 126106 * 2
def baseEnd_126106 : Nat := 21584330471996281131685

theorem tailTrace_126106 : CollatzResearch.WordTrace tailWord_126106 prefixEnd_126106 21584330471996281131685 := by
  unfold tailWord_126106
  simp only [CollatzResearch.WordTrace]
  refine ⟨1149865920286743508811543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3066309120764649356830781 1149865920286743508811543)
  ·
    refine ⟨1724798880430115263217315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1149865920286743508811543 1724798880430115263217315)
    ·
      refine ⟨2587198320645172894825973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1724798880430115263217315 2587198320645172894825973)
      ·
        refine ⟨242549842560484958889935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2587198320645172894825973 242549842560484958889935)
        ·
          refine ⟨363824763840727438334903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242549842560484958889935 363824763840727438334903)
          ·
            refine ⟨545737145761091157502355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363824763840727438334903 545737145761091157502355)
            ·
              refine ⟨818605718641636736253533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545737145761091157502355 818605718641636736253533)
              ·
                refine ⟨306977144490613776095075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 818605718641636736253533 306977144490613776095075)
                ·
                  refine ⟨460465716735920664142613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306977144490613776095075 460465716735920664142613)
                  ·
                    refine ⟨21584330471996281131685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 460465716735920664142613 21584330471996281131685)
                    ·
                      rfl

theorem cell23_126106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_126106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126106 prefixEnd_126106 := by exact prefixLift 126106
  have htrace : WordTrace (prefixWord ++ tailWord_126106) baseStart_126106 baseEnd_126106 := by
    simpa [prefixWord, tailWord_126106, baseEnd_126106] using wordTrace_append hprefix tailTrace_126106
  have hstable : (prefixWord ++ tailWord_126106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126106).length < 2 ^ (prefixWord ++ tailWord_126106).sum := by decide
  have hdescent : baseEnd_126106 < baseStart_126106 := by decide
  rcases family_descends (prefixWord ++ tailWord_126106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126130 : List Nat := [3, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4]
def baseStart_126130 : Nat := 118140960795 + 126130 * 2 ^ 59
def prefixEnd_126130 : Nat := 4983230072969 + 3 ^ 40 * 126130 * 2
def baseEnd_126130 : Nat := 64765314951696749494945

theorem tailTrace_126130 : CollatzResearch.WordTrace tailWord_126130 prefixEnd_126130 64765314951696749494945 := by
  unfold tailWord_126130
  simp only [CollatzResearch.WordTrace]
  refine ⟨1150084758265006533529961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3066892688706684089413229 1150084758265006533529961)
  ·
    refine ⟨862563568698754900147471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1150084758265006533529961 862563568698754900147471)
    ·
      refine ⟨1293845353048132350221207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 862563568698754900147471 1293845353048132350221207)
      ·
        refine ⟨1940768029572198525331811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1293845353048132350221207 1940768029572198525331811)
        ·
          refine ⟨2911152044358297787997717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1940768029572198525331811 2911152044358297787997717)
          ·
            refine ⟨136460252079295208812393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2911152044358297787997717 136460252079295208812393)
            ·
              refine ⟨102345189059471406609295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136460252079295208812393 102345189059471406609295)
              ·
                refine ⟨153517783589207109913943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102345189059471406609295 153517783589207109913943)
                ·
                  refine ⟨230276675383810664870915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153517783589207109913943 230276675383810664870915)
                  ·
                    refine ⟨345415013075715997306373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 230276675383810664870915 345415013075715997306373)
                    ·
                      refine ⟨64765314951696749494945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 345415013075715997306373 64765314951696749494945)
                      ·
                        rfl

theorem cell23_126130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_126130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126130 prefixEnd_126130 := by exact prefixLift 126130
  have htrace : WordTrace (prefixWord ++ tailWord_126130) baseStart_126130 baseEnd_126130 := by
    simpa [prefixWord, tailWord_126130, baseEnd_126130] using wordTrace_append hprefix tailTrace_126130
  have hstable : (prefixWord ++ tailWord_126130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126130).length < 2 ^ (prefixWord ++ tailWord_126130).sum := by decide
  have hdescent : baseEnd_126130 < baseStart_126130 := by decide
  rcases family_descends (prefixWord ++ tailWord_126130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126140 : List Nat := [2, 2, 2, 3, 2, 3, 1, 2, 2, 4]
def baseStart_126140 : Nat := 118140960795 + 126140 * 2 ^ 59
def prefixEnd_126140 : Nat := 4983230072969 + 3 ^ 40 * 126140 * 2
def baseEnd_126140 : Nat := 21590149919413903456633

theorem tailTrace_126140 : CollatzResearch.WordTrace tailWord_126140 prefixEnd_126140 21590149919413903456633 := by
  unfold tailWord_126140
  simp only [CollatzResearch.WordTrace]
  refine ⟨2300351881511898920991937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3067135842015865227989249 2300351881511898920991937)
  ·
    refine ⟨1725263911133924190743953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2300351881511898920991937 1725263911133924190743953)
    ·
      refine ⟨1293947933350443143057965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1725263911133924190743953 1293947933350443143057965)
      ·
        refine ⟨485230475006416178646737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1293947933350443143057965 485230475006416178646737)
        ·
          refine ⟨363922856254812133985053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485230475006416178646737 363922856254812133985053)
          ·
            refine ⟨136471071095554550244395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 363922856254812133985053 136471071095554550244395)
            ·
              refine ⟨204706606643331825366593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136471071095554550244395 204706606643331825366593)
              ·
                refine ⟨153529954982498869024945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204706606643331825366593 153529954982498869024945)
                ·
                  refine ⟨115147466236874151768709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153529954982498869024945 115147466236874151768709)
                  ·
                    refine ⟨21590149919413903456633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115147466236874151768709 21590149919413903456633)
                    ·
                      rfl

theorem cell23_126140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_126140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126140 prefixEnd_126140 := by exact prefixLift 126140
  have htrace : WordTrace (prefixWord ++ tailWord_126140) baseStart_126140 baseEnd_126140 := by
    simpa [prefixWord, tailWord_126140, baseEnd_126140] using wordTrace_append hprefix tailTrace_126140
  have hstable : (prefixWord ++ tailWord_126140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126140).length < 2 ^ (prefixWord ++ tailWord_126140).sum := by decide
  have hdescent : baseEnd_126140 < baseStart_126140 := by decide
  rcases family_descends (prefixWord ++ tailWord_126140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126157 : List Nat := [1, 6, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_126157 : Nat := 118140960795 + 126157 * 2 ^ 59
def prefixEnd_126157 : Nat := 4983230072969 + 3 ^ 40 * 126157 * 2
def baseEnd_126157 : Nat := 21593059643122714619107

theorem tailTrace_126157 : CollatzResearch.WordTrace tailWord_126157 prefixEnd_126157 21593059643122714619107 := by
  unfold tailWord_126157
  simp only [CollatzResearch.WordTrace]
  refine ⟨4601323803962209745352725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3067549202641473163568483 4601323803962209745352725)
  ·
    refine ⟨215687053310728581813409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4601323803962209745352725 215687053310728581813409)
    ·
      refine ⟨161765289983046436360057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215687053310728581813409 161765289983046436360057)
      ·
        refine ⟨121323967487284827270043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161765289983046436360057 121323967487284827270043)
        ·
          refine ⟨181985951230927240905065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121323967487284827270043 181985951230927240905065)
          ·
            refine ⟨136489463423195430678799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181985951230927240905065 136489463423195430678799)
            ·
              refine ⟨204734195134793146018199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136489463423195430678799 204734195134793146018199)
              ·
                refine ⟨307101292702189719027299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204734195134793146018199 307101292702189719027299)
                ·
                  refine ⟨460651939053284578540949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307101292702189719027299 460651939053284578540949)
                  ·
                    refine ⟨21593059643122714619107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 460651939053284578540949 21593059643122714619107)
                    ·
                      rfl

theorem cell23_126157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_126157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126157 prefixEnd_126157 := by exact prefixLift 126157
  have htrace : WordTrace (prefixWord ++ tailWord_126157) baseStart_126157 baseEnd_126157 := by
    simpa [prefixWord, tailWord_126157, baseEnd_126157] using wordTrace_append hprefix tailTrace_126157
  have hstable : (prefixWord ++ tailWord_126157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126157).length < 2 ^ (prefixWord ++ tailWord_126157).sum := by decide
  have hdescent : baseEnd_126157 < baseStart_126157 := by decide
  rcases family_descends (prefixWord ++ tailWord_126157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126181 : List Nat := [1, 3, 1, 4, 4, 1, 1, 3, 1, 2, 2]
def baseStart_126181 : Nat := 118140960795 + 126181 * 2 ^ 59
def prefixEnd_126181 : Nat := 4983230072969 + 3 ^ 40 * 126181 * 2
def baseEnd_126181 : Nat := 64791502465076049957211

theorem tailTrace_126181 : CollatzResearch.WordTrace tailWord_126181 prefixEnd_126181 64791502465076049957211 := by
  unfold tailWord_126181
  simp only [CollatzResearch.WordTrace]
  refine ⟨4602199155875261844226397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3068132770583507896150931 4602199155875261844226397)
  ·
    refine ⟨1725824683453223191584899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4602199155875261844226397 1725824683453223191584899)
    ·
      refine ⟨2588737025179834787377349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1725824683453223191584899 2588737025179834787377349)
      ·
        refine ⟨485388192221219022633253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2588737025179834787377349 485388192221219022633253)
        ·
          refine ⟨91010286041478566743735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 485388192221219022633253 91010286041478566743735)
          ·
            refine ⟨136515429062217850115603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91010286041478566743735 136515429062217850115603)
            ·
              refine ⟨204773143593326775173405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136515429062217850115603 204773143593326775173405)
              ·
                refine ⟨76789928847497540690027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204773143593326775173405 76789928847497540690027)
                ·
                  refine ⟨115184893271246311035041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76789928847497540690027 115184893271246311035041)
                  ·
                    refine ⟨86388669953434733276281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115184893271246311035041 86388669953434733276281)
                    ·
                      refine ⟨64791502465076049957211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 86388669953434733276281 64791502465076049957211)
                      ·
                        rfl

theorem cell23_126181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_126181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126181 prefixEnd_126181 := by exact prefixLift 126181
  have htrace : WordTrace (prefixWord ++ tailWord_126181) baseStart_126181 baseEnd_126181 := by
    simpa [prefixWord, tailWord_126181, baseEnd_126181] using wordTrace_append hprefix tailTrace_126181
  have hstable : (prefixWord ++ tailWord_126181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126181).length < 2 ^ (prefixWord ++ tailWord_126181).sum := by decide
  have hdescent : baseEnd_126181 < baseStart_126181 := by decide
  rcases family_descends (prefixWord ++ tailWord_126181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126190 : List Nat := [4, 1, 2, 1, 1, 1, 4, 3, 1, 3, 2]
def baseStart_126190 : Nat := 118140960795 + 126190 * 2 ^ 59
def prefixEnd_126190 : Nat := 4983230072969 + 3 ^ 40 * 126190 * 2
def baseEnd_126190 : Nat := 64796123790966514744669

theorem tailTrace_126190 : CollatzResearch.WordTrace tailWord_126190 prefixEnd_126190 64796123790966514744669 := by
  unfold tailWord_126190
  simp only [CollatzResearch.WordTrace]
  refine ⟨575315926605332047663003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3068351608561770920869349 575315926605332047663003)
  ·
    refine ⟨862973889907998071494505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 575315926605332047663003 862973889907998071494505)
    ·
      refine ⟨647230417430998553620879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 862973889907998071494505 647230417430998553620879)
      ·
        refine ⟨970845626146497830431319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647230417430998553620879 970845626146497830431319)
        ·
          refine ⟨1456268439219746745646979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970845626146497830431319 1456268439219746745646979)
          ·
            refine ⟨2184402658829620118470469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1456268439219746745646979 2184402658829620118470469)
            ·
              refine ⟨409575498530553772213213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2184402658829620118470469 409575498530553772213213)
              ·
                refine ⟨153590811948957664579955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 409575498530553772213213 153590811948957664579955)
                ·
                  refine ⟨230386217923436496869933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153590811948957664579955 230386217923436496869933)
                  ·
                    refine ⟨86394831721288686326225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 230386217923436496869933 86394831721288686326225)
                    ·
                      refine ⟨64796123790966514744669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 86394831721288686326225 64796123790966514744669)
                      ·
                        rfl

theorem cell23_126190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_126190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126190 prefixEnd_126190 := by exact prefixLift 126190
  have htrace : WordTrace (prefixWord ++ tailWord_126190) baseStart_126190 baseEnd_126190 := by
    simpa [prefixWord, tailWord_126190, baseEnd_126190] using wordTrace_append hprefix tailTrace_126190
  have hstable : (prefixWord ++ tailWord_126190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126190).length < 2 ^ (prefixWord ++ tailWord_126190).sum := by decide
  have hdescent : baseEnd_126190 < baseStart_126190 := by decide
  rcases family_descends (prefixWord ++ tailWord_126190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126256 : List Nat := [2, 1, 1, 1, 2, 2, 3, 4, 2, 5]
def baseStart_126256 : Nat := 118140960795 + 126256 * 2 ^ 59
def prefixEnd_126256 : Nat := 4983230072969 + 3 ^ 40 * 126256 * 2
def baseEnd_126256 : Nat := 21610004504721085506455

theorem tailTrace_126256 : CollatzResearch.WordTrace tailWord_126256 prefixEnd_126256 21610004504721085506455 := by
  unfold tailWord_126256
  simp only [CollatzResearch.WordTrace]
  refine ⟨2302467315301774826603311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3069956420402366435471081 2302467315301774826603311)
  ·
    refine ⟨3453700972952662239904967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2302467315301774826603311 3453700972952662239904967)
    ·
      refine ⟨5180551459428993359857451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3453700972952662239904967 5180551459428993359857451)
      ·
        refine ⟨7770827189143490039786177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5180551459428993359857451 7770827189143490039786177)
        ·
          refine ⟨5828120391857617529839633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7770827189143490039786177 5828120391857617529839633)
          ·
            refine ⟨4371090293893213147379725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5828120391857617529839633 4371090293893213147379725)
            ·
              refine ⟨1639158860209954930267397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4371090293893213147379725 1639158860209954930267397)
              ·
                refine ⟨307342286289366549425137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1639158860209954930267397 307342286289366549425137)
                ·
                  refine ⟨230506714717024912068853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307342286289366549425137 230506714717024912068853)
                  ·
                    refine ⟨21610004504721085506455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 230506714717024912068853 21610004504721085506455)
                    ·
                      rfl

theorem cell23_126256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 2, 5].length) (baseStart_126256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126256 prefixEnd_126256 := by exact prefixLift 126256
  have htrace : WordTrace (prefixWord ++ tailWord_126256) baseStart_126256 baseEnd_126256 := by
    simpa [prefixWord, tailWord_126256, baseEnd_126256] using wordTrace_append hprefix tailTrace_126256
  have hstable : (prefixWord ++ tailWord_126256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126256).length < 2 ^ (prefixWord ++ tailWord_126256).sum := by decide
  have hdescent : baseEnd_126256 < baseStart_126256 := by decide
  rcases family_descends (prefixWord ++ tailWord_126256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126260 : List Nat := [2, 5, 1, 1, 1, 1, 3, 4, 5]
def baseStart_126260 : Nat := 118140960795 + 126260 * 2 ^ 59
def prefixEnd_126260 : Nat := 4983230072969 + 3 ^ 40 * 126260 * 2
def baseEnd_126260 : Nat := 7203563048531248985483

theorem tailTrace_126260 : CollatzResearch.WordTrace tailWord_126260 prefixEnd_126260 7203563048531248985483 := by
  unfold tailWord_126260
  simp only [CollatzResearch.WordTrace]
  refine ⟨2302540261294529168176117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3070053681726038890901489 2302540261294529168176117)
  ·
    refine ⟨215863149496362109516511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2302540261294529168176117 215863149496362109516511)
    ·
      refine ⟨323794724244543164274767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215863149496362109516511 323794724244543164274767)
      ·
        refine ⟨485692086366814746412151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323794724244543164274767 485692086366814746412151)
        ·
          refine ⟨728538129550222119618227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485692086366814746412151 728538129550222119618227)
          ·
            refine ⟨1092807194325333179427341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728538129550222119618227 1092807194325333179427341)
            ·
              refine ⟨409802697871999942285253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1092807194325333179427341 409802697871999942285253)
              ·
                refine ⟨76838005850999989178485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 409802697871999942285253 76838005850999989178485)
                ·
                  refine ⟨7203563048531248985483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76838005850999989178485 7203563048531248985483)
                  ·
                    rfl

theorem cell23_126260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_126260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126260 prefixEnd_126260 := by exact prefixLift 126260
  have htrace : WordTrace (prefixWord ++ tailWord_126260) baseStart_126260 baseEnd_126260 := by
    simpa [prefixWord, tailWord_126260, baseEnd_126260] using wordTrace_append hprefix tailTrace_126260
  have hstable : (prefixWord ++ tailWord_126260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126260).length < 2 ^ (prefixWord ++ tailWord_126260).sum := by decide
  have hdescent : baseEnd_126260 < baseStart_126260 := by decide
  rcases family_descends (prefixWord ++ tailWord_126260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126266 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5]
def baseStart_126266 : Nat := 118140960795 + 126266 * 2 ^ 59
def prefixEnd_126266 : Nat := 4983230072969 + 3 ^ 40 * 126266 * 2
def baseEnd_126266 : Nat := 64835148320708217394319

theorem tailTrace_126266 : CollatzResearch.WordTrace tailWord_126266 prefixEnd_126266 64835148320708217394319 := by
  unfold tailWord_126266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1151324840141830340267663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3070199573711547574047101 1151324840141830340267663)
  ·
    refine ⟨1726987260212745510401495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1151324840141830340267663 1726987260212745510401495)
    ·
      refine ⟨2590480890319118265602243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1726987260212745510401495 2590480890319118265602243)
      ·
        refine ⟨3885721335478677398403365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2590480890319118265602243 3885721335478677398403365)
        ·
          refine ⟨728572750402252012200631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3885721335478677398403365 728572750402252012200631)
          ·
            refine ⟨1092859125603378018300947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728572750402252012200631 1092859125603378018300947)
            ·
              refine ⟨1639288688405067027451421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092859125603378018300947 1639288688405067027451421)
              ·
                refine ⟨614733258151900135294283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1639288688405067027451421 614733258151900135294283)
                ·
                  refine ⟨922099887227850202941425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 614733258151900135294283 922099887227850202941425)
                  ·
                    refine ⟨691574915420887652206069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 922099887227850202941425 691574915420887652206069)
                    ·
                      refine ⟨64835148320708217394319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 691574915420887652206069 64835148320708217394319)
                      ·
                        rfl

theorem cell23_126266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_126266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126266 prefixEnd_126266 := by exact prefixLift 126266
  have htrace : WordTrace (prefixWord ++ tailWord_126266) baseStart_126266 baseEnd_126266 := by
    simpa [prefixWord, tailWord_126266, baseEnd_126266] using wordTrace_append hprefix tailTrace_126266
  have hstable : (prefixWord ++ tailWord_126266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126266).length < 2 ^ (prefixWord ++ tailWord_126266).sum := by decide
  have hdescent : baseEnd_126266 < baseStart_126266 := by decide
  rcases family_descends (prefixWord ++ tailWord_126266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126293 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_126293 : Nat := 118140960795 + 126293 * 2 ^ 59
def prefixEnd_126293 : Nat := 4983230072969 + 3 ^ 40 * 126293 * 2
def baseEnd_126293 : Nat := 64849012298379611756695

theorem tailTrace_126293 : CollatzResearch.WordTrace tailWord_126293 prefixEnd_126293 64849012298379611756695 := by
  unfold tailWord_126293
  simp only [CollatzResearch.WordTrace]
  refine ⟨4606284131469504972303533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3070856087646336648202355 4606284131469504972303533)
  ·
    refine ⟨1727356549301064364613825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4606284131469504972303533 1727356549301064364613825)
    ·
      refine ⟨1295517411975798273460369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1727356549301064364613825 1295517411975798273460369)
      ·
        refine ⟨971638058981848705095277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1295517411975798273460369 971638058981848705095277)
        ·
          refine ⟨364364272118193264410729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 971638058981848705095277 364364272118193264410729)
          ·
            refine ⟨273273204088644948308047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364364272118193264410729 273273204088644948308047)
            ·
              refine ⟨409909806132967422462071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273273204088644948308047 409909806132967422462071)
              ·
                refine ⟨614864709199451133693107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409909806132967422462071 614864709199451133693107)
                ·
                  refine ⟨922297063799176700539661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 614864709199451133693107 922297063799176700539661)
                  ·
                    refine ⟨345861398924691262702373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 922297063799176700539661 345861398924691262702373)
                    ·
                      refine ⟨64849012298379611756695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 345861398924691262702373 64849012298379611756695)
                      ·
                        rfl

theorem cell23_126293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_126293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126293 prefixEnd_126293 := by exact prefixLift 126293
  have htrace : WordTrace (prefixWord ++ tailWord_126293) baseStart_126293 baseEnd_126293 := by
    simpa [prefixWord, tailWord_126293, baseEnd_126293] using wordTrace_append hprefix tailTrace_126293
  have hstable : (prefixWord ++ tailWord_126293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126293).length < 2 ^ (prefixWord ++ tailWord_126293).sum := by decide
  have hdescent : baseEnd_126293 < baseStart_126293 := by decide
  rcases family_descends (prefixWord ++ tailWord_126293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126320 : List Nat := [2, 1, 1, 1, 4, 2, 1, 6, 1, 4]
def baseStart_126320 : Nat := 118140960795 + 126320 * 2 ^ 59
def prefixEnd_126320 : Nat := 4983230072969 + 3 ^ 40 * 126320 * 2
def baseEnd_126320 : Nat := 21620958758683668706357

theorem tailTrace_126320 : CollatzResearch.WordTrace tailWord_126320 prefixEnd_126320 21620958758683668706357 := by
  unfold tailWord_126320
  simp only [CollatzResearch.WordTrace]
  refine ⟨2303634451185844291768207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3071512601581125722357609 2303634451185844291768207)
  ·
    refine ⟨3455451676778766437652311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2303634451185844291768207 3455451676778766437652311)
    ·
      refine ⟨5183177515168149656478467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3455451676778766437652311 5183177515168149656478467)
      ·
        refine ⟨7774766272752224484717701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5183177515168149656478467 7774766272752224484717701)
        ·
          refine ⟨1457768676141042090884569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7774766272752224484717701 1457768676141042090884569)
          ·
            refine ⟨1093326507105781568163427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1457768676141042090884569 1093326507105781568163427)
            ·
              refine ⟨1639989760658672352245141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093326507105781568163427 1639989760658672352245141)
              ·
                refine ⟨76874520030875266511491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1639989760658672352245141 76874520030875266511491)
                ·
                  refine ⟨115311780046312899767237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76874520030875266511491 115311780046312899767237)
                  ·
                    refine ⟨21620958758683668706357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 115311780046312899767237 21620958758683668706357)
                    ·
                      rfl

theorem cell23_126320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 1, 4].length) (baseStart_126320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126320 prefixEnd_126320 := by exact prefixLift 126320
  have htrace : WordTrace (prefixWord ++ tailWord_126320) baseStart_126320 baseEnd_126320 := by
    simpa [prefixWord, tailWord_126320, baseEnd_126320] using wordTrace_append hprefix tailTrace_126320
  have hstable : (prefixWord ++ tailWord_126320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126320).length < 2 ^ (prefixWord ++ tailWord_126320).sum := by decide
  have hdescent : baseEnd_126320 < baseStart_126320 := by decide
  rcases family_descends (prefixWord ++ tailWord_126320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126400 : List Nat := [2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 4]
def baseStart_126400 : Nat := 118140960795 + 126400 * 2 ^ 59
def prefixEnd_126400 : Nat := 4983230072969 + 3 ^ 40 * 126400 * 2
def baseEnd_126400 : Nat := 64903954728410693118703

theorem tailTrace_126400 : CollatzResearch.WordTrace tailWord_126400 prefixEnd_126400 64903954728410693118703 := by
  unfold tailWord_126400
  simp only [CollatzResearch.WordTrace]
  refine ⟨2305093371040931123224327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3073457828054574830965769 2305093371040931123224327)
  ·
    refine ⟨3457640056561396684836491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2305093371040931123224327 3457640056561396684836491)
    ·
      refine ⟨5186460084842095027254737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3457640056561396684836491 5186460084842095027254737)
      ·
        refine ⟨3889845063631571270441053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5186460084842095027254737 3889845063631571270441053)
        ·
          refine ⟨1458691898861839226415395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3889845063631571270441053 1458691898861839226415395)
          ·
            refine ⟨2188037848292758839623093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1458691898861839226415395 2188037848292758839623093)
            ·
              refine ⟨205128548277446141214665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2188037848292758839623093 205128548277446141214665)
              ·
                refine ⟨153846411208084605910999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205128548277446141214665 153846411208084605910999)
                ·
                  refine ⟨230769616812126908866499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153846411208084605910999 230769616812126908866499)
                  ·
                    refine ⟨346154425218190363299749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 230769616812126908866499 346154425218190363299749)
                    ·
                      refine ⟨64903954728410693118703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 346154425218190363299749 64903954728410693118703)
                      ·
                        rfl

theorem cell23_126400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 4].length) (baseStart_126400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126400 prefixEnd_126400 := by exact prefixLift 126400
  have htrace : WordTrace (prefixWord ++ tailWord_126400) baseStart_126400 baseEnd_126400 := by
    simpa [prefixWord, tailWord_126400, baseEnd_126400] using wordTrace_append hprefix tailTrace_126400
  have hstable : (prefixWord ++ tailWord_126400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126400).length < 2 ^ (prefixWord ++ tailWord_126400).sum := by decide
  have hdescent : baseEnd_126400 < baseStart_126400 := by decide
  rcases family_descends (prefixWord ++ tailWord_126400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126404 : List Nat := [2, 3, 3, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_126404 : Nat := 118140960795 + 126404 * 2 ^ 59
def prefixEnd_126404 : Nat := 4983230072969 + 3 ^ 40 * 126404 * 2
def baseEnd_126404 : Nat := 64906008651028677468685

theorem tailTrace_126404 : CollatzResearch.WordTrace tailWord_126404 prefixEnd_126404 64906008651028677468685 := by
  unfold tailWord_126404
  simp only [CollatzResearch.WordTrace]
  refine ⟨2305166317033685464797133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3073555089378247286396177 2305166317033685464797133)
  ·
    refine ⟨864437368887632049298925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2305166317033685464797133 864437368887632049298925)
    ·
      refine ⟨324164013332862018487097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 864437368887632049298925 324164013332862018487097)
      ·
        refine ⟨243123009999646513865323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 324164013332862018487097 243123009999646513865323)
        ·
          refine ⟨364684514999469770797985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243123009999646513865323 364684514999469770797985)
          ·
            refine ⟨273513386249602328098489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364684514999469770797985 273513386249602328098489)
            ·
              refine ⟨205135039687201746073867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273513386249602328098489 205135039687201746073867)
              ·
                refine ⟨307702559530802619110801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205135039687201746073867 307702559530802619110801)
                ·
                  refine ⟨230776919648101964333101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307702559530802619110801 230776919648101964333101)
                  ·
                    refine ⟨86541344868038236624913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 230776919648101964333101 86541344868038236624913)
                    ·
                      refine ⟨64906008651028677468685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 86541344868038236624913 64906008651028677468685)
                      ·
                        rfl

theorem cell23_126404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_126404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126404 prefixEnd_126404 := by exact prefixLift 126404
  have htrace : WordTrace (prefixWord ++ tailWord_126404) baseStart_126404 baseEnd_126404 := by
    simpa [prefixWord, tailWord_126404, baseEnd_126404] using wordTrace_append hprefix tailTrace_126404
  have hstable : (prefixWord ++ tailWord_126404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126404).length < 2 ^ (prefixWord ++ tailWord_126404).sum := by decide
  have hdescent : baseEnd_126404 < baseStart_126404 := by decide
  rcases family_descends (prefixWord ++ tailWord_126404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126468 : List Nat := [2, 3, 2, 3, 2, 1, 2, 3, 1, 2, 2]
def baseStart_126468 : Nat := 118140960795 + 126468 * 2 ^ 59
def prefixEnd_126468 : Nat := 4983230072969 + 3 ^ 40 * 126468 * 2
def baseEnd_126468 : Nat := 64938871412916427068391

theorem tailTrace_126468 : CollatzResearch.WordTrace tailWord_126468 prefixEnd_126468 64938871412916427068391 := by
  unfold tailWord_126468
  simp only [CollatzResearch.WordTrace]
  refine ⟨2306333452917754929962029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3075111270557006573282705 2306333452917754929962029)
  ·
    refine ⟨864875044844158098735761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2306333452917754929962029 864875044844158098735761)
    ·
      refine ⟨648656283633118574051821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 864875044844158098735761 648656283633118574051821)
      ·
        refine ⟨243246106362419465269433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 648656283633118574051821 243246106362419465269433)
        ·
          refine ⟨182434579771814598952075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243246106362419465269433 182434579771814598952075)
          ·
            refine ⟨273651869657721898428113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182434579771814598952075 273651869657721898428113)
            ·
              refine ⟨205238902243291423821085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273651869657721898428113 205238902243291423821085)
              ·
                refine ⟨76964588341234283932907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205238902243291423821085 76964588341234283932907)
                ·
                  refine ⟨115446882511851425899361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76964588341234283932907 115446882511851425899361)
                  ·
                    refine ⟨86585161883888569424521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115446882511851425899361 86585161883888569424521)
                    ·
                      refine ⟨64938871412916427068391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 86585161883888569424521 64938871412916427068391)
                      ·
                        rfl

theorem cell23_126468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_126468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126468 prefixEnd_126468 := by exact prefixLift 126468
  have htrace : WordTrace (prefixWord ++ tailWord_126468) baseStart_126468 baseEnd_126468 := by
    simpa [prefixWord, tailWord_126468, baseEnd_126468] using wordTrace_append hprefix tailTrace_126468
  have hstable : (prefixWord ++ tailWord_126468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126468).length < 2 ^ (prefixWord ++ tailWord_126468).sum := by decide
  have hdescent : baseEnd_126468 < baseStart_126468 := by decide
  rcases family_descends (prefixWord ++ tailWord_126468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126483 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 2, 6]
def baseStart_126483 : Nat := 118140960795 + 126483 * 2 ^ 59
def prefixEnd_126483 : Nat := 4983230072969 + 3 ^ 40 * 126483 * 2
def baseEnd_126483 : Nat := 21648857874244622793607

theorem tailTrace_126483 : CollatzResearch.WordTrace tailWord_126483 prefixEnd_126483 21648857874244622793607 := by
  unfold tailWord_126483
  simp only [CollatzResearch.WordTrace]
  refine ⟨4613214000781167421720103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3075476000520778281146735 4613214000781167421720103)
  ·
    refine ⟨6919821001171751132580155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4613214000781167421720103 6919821001171751132580155)
    ·
      refine ⟨10379731501757626698870233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6919821001171751132580155 10379731501757626698870233)
      ·
        refine ⟨7784798626318220024152675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10379731501757626698870233 7784798626318220024152675)
        ·
          refine ⟨11677197939477330036229013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7784798626318220024152675 11677197939477330036229013)
          ·
            refine ⟨547368653412999845448235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11677197939477330036229013 547368653412999845448235)
            ·
              refine ⟨821052980119499768172353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547368653412999845448235 821052980119499768172353)
              ·
                refine ⟨615789735089624826129265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 821052980119499768172353 615789735089624826129265)
                ·
                  refine ⟨461842301317218619596949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615789735089624826129265 461842301317218619596949)
                  ·
                    refine ⟨21648857874244622793607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 461842301317218619596949 21648857874244622793607)
                    ·
                      rfl

theorem cell23_126483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 6].length) (baseStart_126483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126483 prefixEnd_126483 := by exact prefixLift 126483
  have htrace : WordTrace (prefixWord ++ tailWord_126483) baseStart_126483 baseEnd_126483 := by
    simpa [prefixWord, tailWord_126483, baseEnd_126483] using wordTrace_append hprefix tailTrace_126483
  have hstable : (prefixWord ++ tailWord_126483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126483).length < 2 ^ (prefixWord ++ tailWord_126483).sum := by decide
  have hdescent : baseEnd_126483 < baseStart_126483 := by decide
  rcases family_descends (prefixWord ++ tailWord_126483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126597 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 2, 4, 2]
def baseStart_126597 : Nat := 118140960795 + 126597 * 2 ^ 59
def prefixEnd_126597 : Nat := 4983230072969 + 3 ^ 40 * 126597 * 2
def baseEnd_126597 : Nat := 65005110417346422355297

theorem tailTrace_126597 : CollatzResearch.WordTrace tailWord_126597 prefixEnd_126597 65005110417346422355297 := by
  unfold tailWord_126597
  simp only [CollatzResearch.WordTrace]
  refine ⟨4617371922368164891370045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3078247948245443260913363 4617371922368164891370045)
  ·
    refine ⟨1731514470888061834263767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4617371922368164891370045 1731514470888061834263767)
    ·
      refine ⟨2597271706332092751395651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1731514470888061834263767 2597271706332092751395651)
      ·
        refine ⟨3895907559498139127093477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2597271706332092751395651 3895907559498139127093477)
        ·
          refine ⟨730482667405901086330027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3895907559498139127093477 730482667405901086330027)
          ·
            refine ⟨1095724001108851629495041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730482667405901086330027 1095724001108851629495041)
            ·
              refine ⟨821793000831638722121281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1095724001108851629495041 821793000831638722121281)
              ·
                refine ⟨616344750623729041590961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 821793000831638722121281 616344750623729041590961)
                ·
                  refine ⟨462258562967796781193221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 616344750623729041590961 462258562967796781193221)
                  ·
                    refine ⟨86673480556461896473729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 462258562967796781193221 86673480556461896473729)
                    ·
                      refine ⟨65005110417346422355297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 86673480556461896473729 65005110417346422355297)
                      ·
                        rfl

theorem cell23_126597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 4, 2].length) (baseStart_126597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126597 prefixEnd_126597 := by exact prefixLift 126597
  have htrace : WordTrace (prefixWord ++ tailWord_126597) baseStart_126597 baseEnd_126597 := by
    simpa [prefixWord, tailWord_126597, baseEnd_126597] using wordTrace_append hprefix tailTrace_126597
  have hstable : (prefixWord ++ tailWord_126597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126597).length < 2 ^ (prefixWord ++ tailWord_126597).sum := by decide
  have hdescent : baseEnd_126597 < baseStart_126597 := by decide
  rcases family_descends (prefixWord ++ tailWord_126597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126654 : List Nat := [4, 2, 1, 1, 2, 4, 1, 2, 6]
def baseStart_126654 : Nat := 118140960795 + 126654 * 2 ^ 59
def prefixEnd_126654 : Nat := 4983230072969 + 3 ^ 40 * 126654 * 2
def baseEnd_126654 : Nat := 7226042090516966593615

theorem tailTrace_126654 : CollatzResearch.WordTrace tailWord_126654 prefixEnd_126654 7226042090516966593615 := by
  unfold tailWord_126654
  simp only [CollatzResearch.WordTrace]
  refine ⟨577431360395207953274377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3079633922107775750796677 577431360395207953274377)
  ·
    refine ⟨433073520296405964955783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 577431360395207953274377 433073520296405964955783)
    ·
      refine ⟨649610280444608947433675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433073520296405964955783 649610280444608947433675)
      ·
        refine ⟨974415420666913421150513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649610280444608947433675 974415420666913421150513)
        ·
          refine ⟨730811565500185065862885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 974415420666913421150513 730811565500185065862885)
          ·
            refine ⟨137027168531284699849291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 730811565500185065862885 137027168531284699849291)
            ·
              refine ⟨205540752796927049773937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137027168531284699849291 205540752796927049773937)
              ·
                refine ⟨154155564597695287330453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205540752796927049773937 154155564597695287330453)
                ·
                  refine ⟨7226042090516966593615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154155564597695287330453 7226042090516966593615)
                  ·
                    rfl

theorem cell23_126654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_126654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126654 prefixEnd_126654 := by exact prefixLift 126654
  have htrace : WordTrace (prefixWord ++ tailWord_126654) baseStart_126654 baseEnd_126654 := by
    simpa [prefixWord, tailWord_126654, baseEnd_126654] using wordTrace_append hprefix tailTrace_126654
  have hstable : (prefixWord ++ tailWord_126654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126654).length < 2 ^ (prefixWord ++ tailWord_126654).sum := by decide
  have hdescent : baseEnd_126654 < baseStart_126654 := by decide
  rcases family_descends (prefixWord ++ tailWord_126654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126664 : List Nat := [2, 1, 3, 1, 2, 2, 4, 1, 3, 1, 3]
def baseStart_126664 : Nat := 118140960795 + 126664 * 2 ^ 59
def prefixEnd_126664 : Nat := 4983230072969 + 3 ^ 40 * 126664 * 2
def baseEnd_126664 : Nat := 65039513621197660217489

theorem tailTrace_126664 : CollatzResearch.WordTrace tailWord_126664 prefixEnd_126664 65039513621197660217489 := by
  unfold tailWord_126664
  simp only [CollatzResearch.WordTrace]
  refine ⟨2309907806562717667029523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3079877075416956889372697 2309907806562717667029523)
  ·
    refine ⟨3464861709844076500544285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2309907806562717667029523 3464861709844076500544285)
    ·
      refine ⟨1299323141191528687704107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3464861709844076500544285 1299323141191528687704107)
      ·
        refine ⟨1948984711787293031556161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1299323141191528687704107 1948984711787293031556161)
        ·
          refine ⟨1461738533840469773667121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1948984711787293031556161 1461738533840469773667121)
          ·
            refine ⟨1096303900380352330250341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1461738533840469773667121 1096303900380352330250341)
            ·
              refine ⟨205556981321316061921939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1096303900380352330250341 205556981321316061921939)
              ·
                refine ⟨308335471981974092882909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205556981321316061921939 308335471981974092882909)
                ·
                  refine ⟨115625801993240284831091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308335471981974092882909 115625801993240284831091)
                  ·
                    refine ⟨173438702989860427246637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 115625801993240284831091 173438702989860427246637)
                    ·
                      refine ⟨65039513621197660217489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 173438702989860427246637 65039513621197660217489)
                      ·
                        rfl

theorem cell23_126664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_126664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126664 prefixEnd_126664 := by exact prefixLift 126664
  have htrace : WordTrace (prefixWord ++ tailWord_126664) baseStart_126664 baseEnd_126664 := by
    simpa [prefixWord, tailWord_126664, baseEnd_126664] using wordTrace_append hprefix tailTrace_126664
  have hstable : (prefixWord ++ tailWord_126664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126664).length < 2 ^ (prefixWord ++ tailWord_126664).sum := by decide
  have hdescent : baseEnd_126664 < baseStart_126664 := by decide
  rcases family_descends (prefixWord ++ tailWord_126664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126674 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 1, 5, 2]
def baseStart_126674 : Nat := 118140960795 + 126674 * 2 ^ 59
def prefixEnd_126674 : Nat := 4983230072969 + 3 ^ 40 * 126674 * 2
def baseEnd_126674 : Nat := 65044648427742621092443

theorem tailTrace_126674 : CollatzResearch.WordTrace tailWord_126674 prefixEnd_126674 65044648427742621092443 := by
  unfold tailWord_126674
  simp only [CollatzResearch.WordTrace]
  refine ⟨1155045085772301760480769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3080120228726138027948717 1155045085772301760480769)
  ·
    refine ⟨866283814329226320360577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1155045085772301760480769 866283814329226320360577)
    ·
      refine ⟨649712860746919740270433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 866283814329226320360577 649712860746919740270433)
      ·
        refine ⟨487284645560189805202825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649712860746919740270433 487284645560189805202825)
        ·
          refine ⟨365463484170142353902119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487284645560189805202825 365463484170142353902119)
          ·
            refine ⟨548195226255213530853179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365463484170142353902119 548195226255213530853179)
            ·
              refine ⟨822292839382820296279769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548195226255213530853179 822292839382820296279769)
              ·
                refine ⟨616719629537115222209827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822292839382820296279769 616719629537115222209827)
                ·
                  refine ⟨925079444305672833314741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616719629537115222209827 925079444305672833314741)
                  ·
                    refine ⟨86726197903656828123257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 925079444305672833314741 86726197903656828123257)
                    ·
                      refine ⟨65044648427742621092443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 86726197903656828123257 65044648427742621092443)
                      ·
                        rfl

theorem cell23_126674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_126674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126674 prefixEnd_126674 := by exact prefixLift 126674
  have htrace : WordTrace (prefixWord ++ tailWord_126674) baseStart_126674 baseEnd_126674 := by
    simpa [prefixWord, tailWord_126674, baseEnd_126674] using wordTrace_append hprefix tailTrace_126674
  have hstable : (prefixWord ++ tailWord_126674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126674).length < 2 ^ (prefixWord ++ tailWord_126674).sum := by decide
  have hdescent : baseEnd_126674 < baseStart_126674 := by decide
  rcases family_descends (prefixWord ++ tailWord_126674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126687 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 2, 6, 2]
def baseStart_126687 : Nat := 118140960795 + 126687 * 2 ^ 59
def prefixEnd_126687 : Nat := 4983230072969 + 3 ^ 40 * 126687 * 2
def baseEnd_126687 : Nat := 65051323676251070229883

theorem tailTrace_126687 : CollatzResearch.WordTrace tailWord_126687 prefixEnd_126687 65051323676251070229883 := by
  unfold tailWord_126687
  simp only [CollatzResearch.WordTrace]
  refine ⟨4620654492042110262146315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3080436328028073508097543 4620654492042110262146315)
  ·
    refine ⟨6930981738063165393219473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4620654492042110262146315 6930981738063165393219473)
    ·
      refine ⟨5198236303547374044914605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6930981738063165393219473 5198236303547374044914605)
      ·
        refine ⟨1949338613830265266842977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5198236303547374044914605 1949338613830265266842977)
        ·
          refine ⟨1462003960372698950132233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1949338613830265266842977 1462003960372698950132233)
          ·
            refine ⟨1096502970279524212599175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1462003960372698950132233 1096502970279524212599175)
            ·
              refine ⟨1644754455419286318898763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096502970279524212599175 1644754455419286318898763)
              ·
                refine ⟨2467131683128929478348145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1644754455419286318898763 2467131683128929478348145)
                ·
                  refine ⟨1850348762346697108761109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2467131683128929478348145 1850348762346697108761109)
                  ·
                    refine ⟨86735098235001426973177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1850348762346697108761109 86735098235001426973177)
                    ·
                      refine ⟨65051323676251070229883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 86735098235001426973177 65051323676251070229883)
                      ·
                        rfl

theorem cell23_126687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_126687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126687 prefixEnd_126687 := by exact prefixLift 126687
  have htrace : WordTrace (prefixWord ++ tailWord_126687) baseStart_126687 baseEnd_126687 := by
    simpa [prefixWord, tailWord_126687, baseEnd_126687] using wordTrace_append hprefix tailTrace_126687
  have hstable : (prefixWord ++ tailWord_126687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126687).length < 2 ^ (prefixWord ++ tailWord_126687).sum := by decide
  have hdescent : baseEnd_126687 < baseStart_126687 := by decide
  rcases family_descends (prefixWord ++ tailWord_126687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126708 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_126708 : Nat := 118140960795 + 126708 * 2 ^ 59
def prefixEnd_126708 : Nat := 4983230072969 + 3 ^ 40 * 126708 * 2
def baseEnd_126708 : Nat := 65062106769995488067287

theorem tailTrace_126708 : CollatzResearch.WordTrace tailWord_126708 prefixEnd_126708 65062106769995488067287 := by
  unfold tailWord_126708
  simp only [CollatzResearch.WordTrace]
  refine ⟨2310710212483015424330389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3080946949977353899107185 2310710212483015424330389)
  ·
    refine ⟨108314541210141348015487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2310710212483015424330389 108314541210141348015487)
    ·
      refine ⟨162471811815212022023231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108314541210141348015487 162471811815212022023231)
      ·
        refine ⟨243707717722818033034847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162471811815212022023231 243707717722818033034847)
        ·
          refine ⟨365561576584227049552271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243707717722818033034847 365561576584227049552271)
          ·
            refine ⟨548342364876340574328407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365561576584227049552271 548342364876340574328407)
            ·
              refine ⟨822513547314510861492611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548342364876340574328407 822513547314510861492611)
              ·
                refine ⟨1233770320971766292238917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 822513547314510861492611 1233770320971766292238917)
                ·
                  refine ⟨231331935182206179794797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1233770320971766292238917 231331935182206179794797)
                  ·
                    refine ⟨86749475693327317423049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 231331935182206179794797 86749475693327317423049)
                    ·
                      refine ⟨65062106769995488067287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 86749475693327317423049 65062106769995488067287)
                      ·
                        rfl

theorem cell23_126708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_126708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126708 prefixEnd_126708 := by exact prefixLift 126708
  have htrace : WordTrace (prefixWord ++ tailWord_126708) baseStart_126708 baseEnd_126708 := by
    simpa [prefixWord, tailWord_126708, baseEnd_126708] using wordTrace_append hprefix tailTrace_126708
  have hstable : (prefixWord ++ tailWord_126708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126708).length < 2 ^ (prefixWord ++ tailWord_126708).sum := by decide
  have hdescent : baseEnd_126708 < baseStart_126708 := by decide
  rcases family_descends (prefixWord ++ tailWord_126708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126721 : List Nat := [1, 2, 4, 1, 1, 1, 5, 1, 3, 2, 2]
def baseStart_126721 : Nat := 118140960795 + 126721 * 2 ^ 59
def prefixEnd_126721 : Nat := 4983230072969 + 3 ^ 40 * 126721 * 2
def baseEnd_126721 : Nat := 65068782018503937204727

theorem tailTrace_126721 : CollatzResearch.WordTrace tailWord_126721 prefixEnd_126721 65068782018503937204727 := by
  unfold tailWord_126721
  simp only [CollatzResearch.WordTrace]
  refine ⟨4621894573918934068884017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3081263049279289379256011 4621894573918934068884017)
  ·
    refine ⟨3466420930439200551663013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4621894573918934068884017 3466420930439200551663013)
    ·
      refine ⟨649953924457350103436815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3466420930439200551663013 649953924457350103436815)
      ·
        refine ⟨974930886686025155155223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649953924457350103436815 974930886686025155155223)
        ·
          refine ⟨1462396330029037732732835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974930886686025155155223 1462396330029037732732835)
          ·
            refine ⟨2193594495043556599099253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462396330029037732732835 2193594495043556599099253)
            ·
              refine ⟨205649483910333431165555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2193594495043556599099253 205649483910333431165555)
              ·
                refine ⟨308474225865500146748333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205649483910333431165555 308474225865500146748333)
                ·
                  refine ⟨115677834699562555030625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 308474225865500146748333 115677834699562555030625)
                  ·
                    refine ⟨86758376024671916272969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115677834699562555030625 86758376024671916272969)
                    ·
                      refine ⟨65068782018503937204727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 86758376024671916272969 65068782018503937204727)
                      ·
                        rfl

theorem cell23_126721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_126721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126721 prefixEnd_126721 := by exact prefixLift 126721
  have htrace : WordTrace (prefixWord ++ tailWord_126721) baseStart_126721 baseEnd_126721 := by
    simpa [prefixWord, tailWord_126721, baseEnd_126721] using wordTrace_append hprefix tailTrace_126721
  have hstable : (prefixWord ++ tailWord_126721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126721).length < 2 ^ (prefixWord ++ tailWord_126721).sum := by decide
  have hdescent : baseEnd_126721 < baseStart_126721 := by decide
  rcases family_descends (prefixWord ++ tailWord_126721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126737 : List Nat := [1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 3]
def baseStart_126737 : Nat := 118140960795 + 126737 * 2 ^ 59
def prefixEnd_126737 : Nat := 4983230072969 + 3 ^ 40 * 126737 * 2
def baseEnd_126737 : Nat := 65076997708975874604653

theorem tailTrace_126737 : CollatzResearch.WordTrace tailWord_126737 prefixEnd_126737 65076997708975874604653 := by
  unfold tailWord_126737
  simp only [CollatzResearch.WordTrace]
  refine ⟨4622478141860968801466465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3081652094573979200977643 4622478141860968801466465)
  ·
    refine ⟨3466858606395726601099849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4622478141860968801466465 3466858606395726601099849)
    ·
      refine ⟨2600143954796794950824887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3466858606395726601099849 2600143954796794950824887)
      ·
        refine ⟨3900215932195192426237331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2600143954796794950824887 3900215932195192426237331)
        ·
          refine ⟨5850323898292788639355997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3900215932195192426237331 5850323898292788639355997)
          ·
            refine ⟨2193871461859795739758499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5850323898292788639355997 2193871461859795739758499)
            ·
              refine ⟨3290807192789693609637749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193871461859795739758499 3290807192789693609637749)
              ·
                refine ⟨308513174324033775903539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3290807192789693609637749 308513174324033775903539)
                ·
                  refine ⟨462769761486050663855309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308513174324033775903539 462769761486050663855309)
                  ·
                    refine ⟨173538660557268998945741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 462769761486050663855309 173538660557268998945741)
                    ·
                      refine ⟨65076997708975874604653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 173538660557268998945741 65076997708975874604653)
                      ·
                        rfl

theorem cell23_126737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_126737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126737 prefixEnd_126737 := by exact prefixLift 126737
  have htrace : WordTrace (prefixWord ++ tailWord_126737) baseStart_126737 baseEnd_126737 := by
    simpa [prefixWord, tailWord_126737, baseEnd_126737] using wordTrace_append hprefix tailTrace_126737
  have hstable : (prefixWord ++ tailWord_126737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126737).length < 2 ^ (prefixWord ++ tailWord_126737).sum := by decide
  have hdescent : baseEnd_126737 < baseStart_126737 := by decide
  rcases family_descends (prefixWord ++ tailWord_126737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126738 : List Nat := [3, 2, 4, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_126738 : Nat := 118140960795 + 126738 * 2 ^ 59
def prefixEnd_126738 : Nat := 4983230072969 + 3 ^ 40 * 126738 * 2
def baseEnd_126738 : Nat := 65077511189630370692149

theorem tailTrace_126738 : CollatzResearch.WordTrace tailWord_126738 prefixEnd_126738 65077511189630370692149 := by
  unfold tailWord_126738
  simp only [CollatzResearch.WordTrace]
  refine ⟨1155628653714336493063217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3081676409904897314835245 1155628653714336493063217)
  ·
    refine ⟨866721490285752369797413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1155628653714336493063217 866721490285752369797413)
    ·
      refine ⟨162510279428578569337015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 866721490285752369797413 162510279428578569337015)
      ·
        refine ⟨243765419142867854005523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162510279428578569337015 243765419142867854005523)
        ·
          refine ⟨365648128714301781008285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243765419142867854005523 365648128714301781008285)
          ·
            refine ⟨137118048267863167878107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365648128714301781008285 137118048267863167878107)
            ·
              refine ⟨205677072401794751817161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137118048267863167878107 205677072401794751817161)
              ·
                refine ⟨154257804301346063862871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205677072401794751817161 154257804301346063862871)
                ·
                  refine ⟨231386706452019095794307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154257804301346063862871 231386706452019095794307)
                  ·
                    refine ⟨347080059678028643691461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 231386706452019095794307 347080059678028643691461)
                    ·
                      refine ⟨65077511189630370692149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 347080059678028643691461 65077511189630370692149)
                      ·
                        rfl

theorem cell23_126738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_126738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126738 prefixEnd_126738 := by exact prefixLift 126738
  have htrace : WordTrace (prefixWord ++ tailWord_126738) baseStart_126738 baseEnd_126738 := by
    simpa [prefixWord, tailWord_126738, baseEnd_126738] using wordTrace_append hprefix tailTrace_126738
  have hstable : (prefixWord ++ tailWord_126738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126738).length < 2 ^ (prefixWord ++ tailWord_126738).sum := by decide
  have hdescent : baseEnd_126738 < baseStart_126738 := by decide
  rcases family_descends (prefixWord ++ tailWord_126738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126741 : List Nat := [1, 3, 2, 1, 2, 5, 1, 2, 1, 2, 3]
def baseStart_126741 : Nat := 118140960795 + 126741 * 2 ^ 59
def prefixEnd_126741 : Nat := 4983230072969 + 3 ^ 40 * 126741 * 2
def baseEnd_126741 : Nat := 65079051631593858954635

theorem tailTrace_126741 : CollatzResearch.WordTrace tailWord_126741 prefixEnd_126741 65079051631593858954635 := by
  unfold tailWord_126741
  simp only [CollatzResearch.WordTrace]
  refine ⟨4622624033846477484612077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3081749355897651656408051 4622624033846477484612077)
  ·
    refine ⟨1733484012692429056729529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4622624033846477484612077 1733484012692429056729529)
    ·
      refine ⟨1300113009519321792547147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1733484012692429056729529 1300113009519321792547147)
      ·
        refine ⟨1950169514278982688820721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1300113009519321792547147 1950169514278982688820721)
        ·
          refine ⟨1462627135709237016615541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1950169514278982688820721 1462627135709237016615541)
          ·
            refine ⟨137121293972740970307707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1462627135709237016615541 137121293972740970307707)
            ·
              refine ⟨205681940959111455461561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137121293972740970307707 205681940959111455461561)
              ·
                refine ⟨154261455719333591596171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205681940959111455461561 154261455719333591596171)
                ·
                  refine ⟨231392183579000387394257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154261455719333591596171 231392183579000387394257)
                  ·
                    refine ⟨173544137684250290545693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 231392183579000387394257 173544137684250290545693)
                    ·
                      refine ⟨65079051631593858954635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 173544137684250290545693 65079051631593858954635)
                      ·
                        rfl

theorem cell23_126741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_126741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126741 prefixEnd_126741 := by exact prefixLift 126741
  have htrace : WordTrace (prefixWord ++ tailWord_126741) baseStart_126741 baseEnd_126741 := by
    simpa [prefixWord, tailWord_126741, baseEnd_126741] using wordTrace_append hprefix tailTrace_126741
  have hstable : (prefixWord ++ tailWord_126741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126741).length < 2 ^ (prefixWord ++ tailWord_126741).sum := by decide
  have hdescent : baseEnd_126741 < baseStart_126741 := by decide
  rcases family_descends (prefixWord ++ tailWord_126741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126747 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 2, 7, 2]
def baseStart_126747 : Nat := 118140960795 + 126747 * 2 ^ 59
def prefixEnd_126747 : Nat := 4983230072969 + 3 ^ 40 * 126747 * 2
def baseEnd_126747 : Nat := 65082132515520835479607

theorem tailTrace_126747 : CollatzResearch.WordTrace tailWord_126747 prefixEnd_126747 65082132515520835479607 := by
  unfold tailWord_126747
  simp only [CollatzResearch.WordTrace]
  refine ⟨4622842871824740509330495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3081895247883160339553663 4622842871824740509330495)
  ·
    refine ⟨6934264307737110763995743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4622842871824740509330495 6934264307737110763995743)
    ·
      refine ⟨10401396461605666145993615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6934264307737110763995743 10401396461605666145993615)
      ·
        refine ⟨15602094692408499218990423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10401396461605666145993615 15602094692408499218990423)
        ·
          refine ⟨23403142038612748828485635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15602094692408499218990423 23403142038612748828485635)
          ·
            refine ⟨35104713057919123242728453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23403142038612748828485635 35104713057919123242728453)
            ·
              refine ⟨6582133698359835608011585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35104713057919123242728453 6582133698359835608011585)
              ·
                refine ⟨4936600273769876706008689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6582133698359835608011585 4936600273769876706008689)
                ·
                  refine ⟨3702450205327407529506517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4936600273769876706008689 3702450205327407529506517)
                  ·
                    refine ⟨86776176687361113972809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3702450205327407529506517 86776176687361113972809)
                    ·
                      refine ⟨65082132515520835479607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 86776176687361113972809 65082132515520835479607)
                      ·
                        rfl

theorem cell23_126747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 7, 2].length) (baseStart_126747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126747 prefixEnd_126747 := by exact prefixLift 126747
  have htrace : WordTrace (prefixWord ++ tailWord_126747) baseStart_126747 baseEnd_126747 := by
    simpa [prefixWord, tailWord_126747, baseEnd_126747] using wordTrace_append hprefix tailTrace_126747
  have hstable : (prefixWord ++ tailWord_126747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126747).length < 2 ^ (prefixWord ++ tailWord_126747).sum := by decide
  have hdescent : baseEnd_126747 < baseStart_126747 := by decide
  rcases family_descends (prefixWord ++ tailWord_126747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126754 : List Nat := [3, 3, 1, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_126754 : Nat := 118140960795 + 126754 * 2 ^ 59
def prefixEnd_126754 : Nat := 4983230072969 + 3 ^ 40 * 126754 * 2
def baseEnd_126754 : Nat := 65085726880102308092075

theorem tailTrace_126754 : CollatzResearch.WordTrace tailWord_126754 prefixEnd_126754 65085726880102308092075 := by
  unfold tailWord_126754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1155774545699845176208829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3082065455199587136556877 1155774545699845176208829)
  ·
    refine ⟨433415454637441941078311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1155774545699845176208829 433415454637441941078311)
    ·
      refine ⟨650123181956162911617467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433415454637441941078311 650123181956162911617467)
      ·
        refine ⟨975184772934244367426201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650123181956162911617467 975184772934244367426201)
        ·
          refine ⟨731388579700683275569651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 975184772934244367426201 731388579700683275569651)
          ·
            refine ⟨1097082869551024913354477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731388579700683275569651 1097082869551024913354477)
            ·
              refine ⟨411406076081634342507929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1097082869551024913354477 411406076081634342507929)
              ·
                refine ⟨308554557061225756880947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411406076081634342507929 308554557061225756880947)
                ·
                  refine ⟨462831835591838635321421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308554557061225756880947 462831835591838635321421)
                  ·
                    refine ⟨173561938346939488245533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 462831835591838635321421 173561938346939488245533)
                    ·
                      refine ⟨65085726880102308092075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 173561938346939488245533 65085726880102308092075)
                      ·
                        rfl

theorem cell23_126754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_126754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126754 prefixEnd_126754 := by exact prefixLift 126754
  have htrace : WordTrace (prefixWord ++ tailWord_126754) baseStart_126754 baseEnd_126754 := by
    simpa [prefixWord, tailWord_126754, baseEnd_126754] using wordTrace_append hprefix tailTrace_126754
  have hstable : (prefixWord ++ tailWord_126754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126754).length < 2 ^ (prefixWord ++ tailWord_126754).sum := by decide
  have hdescent : baseEnd_126754 < baseStart_126754 := by decide
  rcases family_descends (prefixWord ++ tailWord_126754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126772 : List Nat := [2, 5, 1, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_126772 : Nat := 118140960795 + 126772 * 2 ^ 59
def prefixEnd_126772 : Nat := 4983230072969 + 3 ^ 40 * 126772 * 2
def baseEnd_126772 : Nat := 65094969531883237666993

theorem tailTrace_126772 : CollatzResearch.WordTrace tailWord_126772 prefixEnd_126772 65094969531883237666993 := by
  unfold tailWord_126772
  simp only [CollatzResearch.WordTrace]
  refine ⟨2311877348367084889495285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3082503131156113185993713 2311877348367084889495285)
  ·
    refine ⟨216738501409414208390183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2311877348367084889495285 216738501409414208390183)
    ·
      refine ⟨325107752114121312585275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216738501409414208390183 325107752114121312585275)
      ·
        refine ⟨487661628171181968877913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325107752114121312585275 487661628171181968877913)
        ·
          refine ⟨365746221128386476658435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487661628171181968877913 365746221128386476658435)
          ·
            refine ⟨548619331692579714987653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365746221128386476658435 548619331692579714987653)
            ·
              refine ⟨102866124692358696560185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 548619331692579714987653 102866124692358696560185)
              ·
                refine ⟨77149593519269022420139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102866124692358696560185 77149593519269022420139)
                ·
                  refine ⟨115724390278903533630209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77149593519269022420139 115724390278903533630209)
                  ·
                    refine ⟨86793292709177650222657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115724390278903533630209 86793292709177650222657)
                    ·
                      refine ⟨65094969531883237666993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 86793292709177650222657 65094969531883237666993)
                      ·
                        rfl

theorem cell23_126772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_126772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126772 prefixEnd_126772 := by exact prefixLift 126772
  have htrace : WordTrace (prefixWord ++ tailWord_126772) baseStart_126772 baseEnd_126772 := by
    simpa [prefixWord, tailWord_126772, baseEnd_126772] using wordTrace_append hprefix tailTrace_126772
  have hstable : (prefixWord ++ tailWord_126772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126772).length < 2 ^ (prefixWord ++ tailWord_126772).sum := by decide
  have hdescent : baseEnd_126772 < baseStart_126772 := by decide
  rcases family_descends (prefixWord ++ tailWord_126772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126774 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_126774 : Nat := 118140960795 + 126774 * 2 ^ 59
def prefixEnd_126774 : Nat := 4983230072969 + 3 ^ 40 * 126774 * 2
def baseEnd_126774 : Nat := 21698665497730743280661

theorem tailTrace_126774 : CollatzResearch.WordTrace tailWord_126774 prefixEnd_126774 21698665497730743280661 := by
  unfold tailWord_126774
  simp only [CollatzResearch.WordTrace]
  refine ⟨288989227670432757535211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3082551761817949413708917 288989227670432757535211)
  ·
    refine ⟨433483841505649136302817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288989227670432757535211 433483841505649136302817)
    ·
      refine ⟨325112881129236852227113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433483841505649136302817 325112881129236852227113)
      ·
        refine ⟨243834660846927639170335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325112881129236852227113 243834660846927639170335)
        ·
          refine ⟨365751991270391458755503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243834660846927639170335 365751991270391458755503)
          ·
            refine ⟨548627986905587188133255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365751991270391458755503 548627986905587188133255)
            ·
              refine ⟨822941980358380782199883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548627986905587188133255 822941980358380782199883)
              ·
                refine ⟨1234412970537571173299825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 822941980358380782199883 1234412970537571173299825)
                ·
                  refine ⟨925809727903178379974869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1234412970537571173299825 925809727903178379974869)
                  ·
                    refine ⟨21698665497730743280661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 925809727903178379974869 21698665497730743280661)
                    ·
                      rfl

theorem cell23_126774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_126774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126774 prefixEnd_126774 := by exact prefixLift 126774
  have htrace : WordTrace (prefixWord ++ tailWord_126774) baseStart_126774 baseEnd_126774 := by
    simpa [prefixWord, tailWord_126774, baseEnd_126774] using wordTrace_append hprefix tailTrace_126774
  have hstable : (prefixWord ++ tailWord_126774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126774).length < 2 ^ (prefixWord ++ tailWord_126774).sum := by decide
  have hdescent : baseEnd_126774 < baseStart_126774 := by decide
  rcases family_descends (prefixWord ++ tailWord_126774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126781 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 3, 3, 2]
def baseStart_126781 : Nat := 118140960795 + 126781 * 2 ^ 59
def prefixEnd_126781 : Nat := 4983230072969 + 3 ^ 40 * 126781 * 2
def baseEnd_126781 : Nat := 65099590857773702454451

theorem tailTrace_126781 : CollatzResearch.WordTrace tailWord_126781 prefixEnd_126781 65099590857773702454451 := by
  unfold tailWord_126781
  simp only [CollatzResearch.WordTrace]
  refine ⟨4624082953701564316068197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3082721969134376210712131 4624082953701564316068197)
  ·
    refine ⟨867015553819043309262787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4624082953701564316068197 867015553819043309262787)
    ·
      refine ⟨1300523330728564963894181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 867015553819043309262787 1300523330728564963894181)
      ·
        refine ⟨243848124511605930730159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1300523330728564963894181 243848124511605930730159)
        ·
          refine ⟨365772186767408896095239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243848124511605930730159 365772186767408896095239)
          ·
            refine ⟨548658280151113344142859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365772186767408896095239 548658280151113344142859)
            ·
              refine ⟨822987420226670016214289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548658280151113344142859 822987420226670016214289)
              ·
                refine ⟨617240565170002512160717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822987420226670016214289 617240565170002512160717)
                ·
                  refine ⟨231465211938750942060269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 617240565170002512160717 231465211938750942060269)
                  ·
                    refine ⟨86799454477031603272601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 231465211938750942060269 86799454477031603272601)
                    ·
                      refine ⟨65099590857773702454451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 86799454477031603272601 65099590857773702454451)
                      ·
                        rfl

theorem cell23_126781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_126781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126781 prefixEnd_126781 := by exact prefixLift 126781
  have htrace : WordTrace (prefixWord ++ tailWord_126781) baseStart_126781 baseEnd_126781 := by
    simpa [prefixWord, tailWord_126781, baseEnd_126781] using wordTrace_append hprefix tailTrace_126781
  have hstable : (prefixWord ++ tailWord_126781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126781).length < 2 ^ (prefixWord ++ tailWord_126781).sum := by decide
  have hdescent : baseEnd_126781 < baseStart_126781 := by decide
  rcases family_descends (prefixWord ++ tailWord_126781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126787 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 2, 6]
def baseStart_126787 : Nat := 118140960795 + 126787 * 2 ^ 59
def prefixEnd_126787 : Nat := 4983230072969 + 3 ^ 40 * 126787 * 2
def baseEnd_126787 : Nat := 21700890580566892993141

theorem tailTrace_126787 : CollatzResearch.WordTrace tailWord_126787 prefixEnd_126787 21700890580566892993141 := by
  unfold tailWord_126787
  simp only [CollatzResearch.WordTrace]
  refine ⟨4624301791679827340786615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3082867861119884893857743 4624301791679827340786615)
  ·
    refine ⟨6936452687519741011179923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4624301791679827340786615 6936452687519741011179923)
    ·
      refine ⟨10404679031279611516769885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6936452687519741011179923 10404679031279611516769885)
      ·
        refine ⟨3901754636729854318788707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10404679031279611516769885 3901754636729854318788707)
        ·
          refine ⟨5852631955094781478183061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3901754636729854318788707 5852631955094781478183061)
          ·
            refine ⟨274342122895067881789831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5852631955094781478183061 274342122895067881789831)
            ·
              refine ⟨411513184342601822684747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274342122895067881789831 411513184342601822684747)
              ·
                refine ⟨617269776513902734027121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411513184342601822684747 617269776513902734027121)
                ·
                  refine ⟨462952332385427050520341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 617269776513902734027121 462952332385427050520341)
                  ·
                    refine ⟨21700890580566892993141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 462952332385427050520341 21700890580566892993141)
                    ·
                      rfl

theorem cell23_126787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 6].length) (baseStart_126787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126787 prefixEnd_126787 := by exact prefixLift 126787
  have htrace : WordTrace (prefixWord ++ tailWord_126787) baseStart_126787 baseEnd_126787 := by
    simpa [prefixWord, tailWord_126787, baseEnd_126787] using wordTrace_append hprefix tailTrace_126787
  have hstable : (prefixWord ++ tailWord_126787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126787).length < 2 ^ (prefixWord ++ tailWord_126787).sum := by decide
  have hdescent : baseEnd_126787 < baseStart_126787 := by decide
  rcases family_descends (prefixWord ++ tailWord_126787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126828 : List Nat := [2, 2, 1, 1, 4, 2, 3, 2, 2, 2, 2]
def baseStart_126828 : Nat := 118140960795 + 126828 * 2 ^ 59
def prefixEnd_126828 : Nat := 4983230072969 + 3 ^ 40 * 126828 * 2
def baseEnd_126828 : Nat := 65123724448535018566735

theorem tailTrace_126828 : CollatzResearch.WordTrace tailWord_126828 prefixEnd_126828 65123724448535018566735 := by
  unfold tailWord_126828
  simp only [CollatzResearch.WordTrace]
  refine ⟨2312898592265645671514569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3083864789687527562019425 2312898592265645671514569)
  ·
    refine ⟨1734673944199234253635927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2312898592265645671514569 1734673944199234253635927)
    ·
      refine ⟨2602010916298851380453891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1734673944199234253635927 2602010916298851380453891)
      ·
        refine ⟨3903016374448277070680837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2602010916298851380453891 3903016374448277070680837)
        ·
          refine ⟨731815570209051950752657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3903016374448277070680837 731815570209051950752657)
          ·
            refine ⟨548861677656788963064493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 731815570209051950752657 548861677656788963064493)
            ·
              refine ⟨205823129121295861149185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 548861677656788963064493 205823129121295861149185)
              ·
                refine ⟨154367346840971895861889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205823129121295861149185 154367346840971895861889)
                ·
                  refine ⟨115775510130728921896417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154367346840971895861889 115775510130728921896417)
                  ·
                    refine ⟨86831632598046691422313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 115775510130728921896417 86831632598046691422313)
                    ·
                      refine ⟨65123724448535018566735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 86831632598046691422313 65123724448535018566735)
                      ·
                        rfl

theorem cell23_126828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 2, 2].length) (baseStart_126828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126828 prefixEnd_126828 := by exact prefixLift 126828
  have htrace : WordTrace (prefixWord ++ tailWord_126828) baseStart_126828 baseEnd_126828 := by
    simpa [prefixWord, tailWord_126828, baseEnd_126828] using wordTrace_append hprefix tailTrace_126828
  have hstable : (prefixWord ++ tailWord_126828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126828).length < 2 ^ (prefixWord ++ tailWord_126828).sum := by decide
  have hdescent : baseEnd_126828 < baseStart_126828 := by decide
  rcases family_descends (prefixWord ++ tailWord_126828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126868 : List Nat := [2, 4, 2, 1, 1, 4, 1, 3, 5]
def baseStart_126868 : Nat := 118140960795 + 126868 * 2 ^ 59
def prefixEnd_126868 : Nat := 4983230072969 + 3 ^ 40 * 126868 * 2
def baseEnd_126868 : Nat := 7238251519412762451839

theorem tailTrace_126868 : CollatzResearch.WordTrace tailWord_126868 prefixEnd_126868 7238251519412762451839 := by
  unfold tailWord_126868
  simp only [CollatzResearch.WordTrace]
  refine ⟨2313628052193189087242629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3084837402924252116323505 2313628052193189087242629)
  ·
    refine ⟨433805259786222953857993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2313628052193189087242629 433805259786222953857993)
    ·
      refine ⟨325353944839667215393495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433805259786222953857993 325353944839667215393495)
      ·
        refine ⟨488030917259500823090243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325353944839667215393495 488030917259500823090243)
        ·
          refine ⟨732046375889251234635365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488030917259500823090243 732046375889251234635365)
          ·
            refine ⟨137258695479234606494131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 732046375889251234635365 137258695479234606494131)
            ·
              refine ⟨205888043218851909741197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137258695479234606494131 205888043218851909741197)
              ·
                refine ⟨77208016207069466152949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205888043218851909741197 77208016207069466152949)
                ·
                  refine ⟨7238251519412762451839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77208016207069466152949 7238251519412762451839)
                  ·
                    rfl

theorem cell23_126868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_126868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126868 prefixEnd_126868 := by exact prefixLift 126868
  have htrace : WordTrace (prefixWord ++ tailWord_126868) baseStart_126868 baseEnd_126868 := by
    simpa [prefixWord, tailWord_126868, baseEnd_126868] using wordTrace_append hprefix tailTrace_126868
  have hstable : (prefixWord ++ tailWord_126868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126868).length < 2 ^ (prefixWord ++ tailWord_126868).sum := by decide
  have hdescent : baseEnd_126868 < baseStart_126868 := by decide
  rcases family_descends (prefixWord ++ tailWord_126868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126881 : List Nat := [1, 2, 3, 4, 2, 1, 1, 2, 2, 5]
def baseStart_126881 : Nat := 118140960795 + 126881 * 2 ^ 59
def prefixEnd_126881 : Nat := 4983230072969 + 3 ^ 40 * 126881 * 2
def baseEnd_126881 : Nat := 21716979641074437067997

theorem tailTrace_126881 : CollatzResearch.WordTrace tailWord_126881 prefixEnd_126881 21716979641074437067997 := by
  unfold tailWord_126881
  simp only [CollatzResearch.WordTrace]
  refine ⟨4627730253339281394708497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3085153502226187596472331 4627730253339281394708497)
  ·
    refine ⟨3470797690004461046031373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4627730253339281394708497 3470797690004461046031373)
    ·
      refine ⟨1301549133751672892261765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3470797690004461046031373 1301549133751672892261765)
      ·
        refine ⟨244040462578438667299081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1301549133751672892261765 244040462578438667299081)
        ·
          refine ⟨183030346933829000474311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244040462578438667299081 183030346933829000474311)
          ·
            refine ⟨274545520400743500711467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183030346933829000474311 274545520400743500711467)
            ·
              refine ⟨411818280601115251067201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274545520400743500711467 411818280601115251067201)
              ·
                refine ⟨308863710450836438300401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411818280601115251067201 308863710450836438300401)
                ·
                  refine ⟨231647782838127328725301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308863710450836438300401 231647782838127328725301)
                  ·
                    refine ⟨21716979641074437067997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 231647782838127328725301 21716979641074437067997)
                    ·
                      rfl

theorem cell23_126881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_126881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126881 prefixEnd_126881 := by exact prefixLift 126881
  have htrace : WordTrace (prefixWord ++ tailWord_126881) baseStart_126881 baseEnd_126881 := by
    simpa [prefixWord, tailWord_126881, baseEnd_126881] using wordTrace_append hprefix tailTrace_126881
  have hstable : (prefixWord ++ tailWord_126881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126881).length < 2 ^ (prefixWord ++ tailWord_126881).sum := by decide
  have hdescent : baseEnd_126881 < baseStart_126881 := by decide
  rcases family_descends (prefixWord ++ tailWord_126881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126884 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_126884 : Nat := 118140960795 + 126884 * 2 ^ 59
def prefixEnd_126884 : Nat := 4983230072969 + 3 ^ 40 * 126884 * 2
def baseEnd_126884 : Nat := 65152479365186799466477

theorem tailTrace_126884 : CollatzResearch.WordTrace tailWord_126884 prefixEnd_126884 65152479365186799466477 := by
  unfold tailWord_126884
  simp only [CollatzResearch.WordTrace]
  refine ⟨2313919836164206453533853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3085226448218941938045137 2313919836164206453533853)
  ·
    refine ⟨867719938561577420075195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2313919836164206453533853 867719938561577420075195)
    ·
      refine ⟨1301579907842366130112793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 867719938561577420075195 1301579907842366130112793)
      ·
        refine ⟨976184930881774597584595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1301579907842366130112793 976184930881774597584595)
        ·
          refine ⟨1464277396322661896376893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976184930881774597584595 1464277396322661896376893)
          ·
            refine ⟨549104023620998211141335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1464277396322661896376893 549104023620998211141335)
            ·
              refine ⟨823656035431497316712003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549104023620998211141335 823656035431497316712003)
              ·
                refine ⟨1235484053147245975068005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823656035431497316712003 1235484053147245975068005)
                ·
                  refine ⟨231653259965108620325251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1235484053147245975068005 231653259965108620325251)
                  ·
                    refine ⟨347479889947662930487877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 231653259965108620325251 347479889947662930487877)
                    ·
                      refine ⟨65152479365186799466477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 347479889947662930487877 65152479365186799466477)
                      ·
                        rfl

theorem cell23_126884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_126884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126884 prefixEnd_126884 := by exact prefixLift 126884
  have htrace : WordTrace (prefixWord ++ tailWord_126884) baseStart_126884 baseEnd_126884 := by
    simpa [prefixWord, tailWord_126884, baseEnd_126884] using wordTrace_append hprefix tailTrace_126884
  have hstable : (prefixWord ++ tailWord_126884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126884).length < 2 ^ (prefixWord ++ tailWord_126884).sum := by decide
  have hdescent : baseEnd_126884 < baseStart_126884 := by decide
  rcases family_descends (prefixWord ++ tailWord_126884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126904 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 4, 2, 3]
def baseStart_126904 : Nat := 118140960795 + 126904 * 2 ^ 59
def prefixEnd_126904 : Nat := 4983230072969 + 3 ^ 40 * 126904 * 2
def baseEnd_126904 : Nat := 65162748978276721216385

theorem tailTrace_126904 : CollatzResearch.WordTrace tailWord_126904 prefixEnd_126904 65162748978276721216385 := by
  unfold tailWord_126904
  simp only [CollatzResearch.WordTrace]
  refine ⟨2314284566127978161397883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3085712754837304215197177 2314284566127978161397883)
  ·
    refine ⟨3471426849191967242096825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2314284566127978161397883 3471426849191967242096825)
    ·
      refine ⟨2603570136893975431572619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3471426849191967242096825 2603570136893975431572619)
      ·
        refine ⟨3905355205340963147358929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2603570136893975431572619 3905355205340963147358929)
        ·
          refine ⟨2929016404005722360519197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3905355205340963147358929 2929016404005722360519197)
          ·
            refine ⟨1098381151502145885194699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2929016404005722360519197 1098381151502145885194699)
            ·
              refine ⟨1647571727253218827792049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098381151502145885194699 1647571727253218827792049)
              ·
                refine ⟨1235678795439914120844037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1647571727253218827792049 1235678795439914120844037)
                ·
                  refine ⟨231689774144983897658257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1235678795439914120844037 231689774144983897658257)
                  ·
                    refine ⟨173767330608737923243693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 231689774144983897658257 173767330608737923243693)
                    ·
                      refine ⟨65162748978276721216385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 173767330608737923243693 65162748978276721216385)
                      ·
                        rfl

theorem cell23_126904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_126904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126904 prefixEnd_126904 := by exact prefixLift 126904
  have htrace : WordTrace (prefixWord ++ tailWord_126904) baseStart_126904 baseEnd_126904 := by
    simpa [prefixWord, tailWord_126904, baseEnd_126904] using wordTrace_append hprefix tailTrace_126904
  have hstable : (prefixWord ++ tailWord_126904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126904).length < 2 ^ (prefixWord ++ tailWord_126904).sum := by decide
  have hdescent : baseEnd_126904 < baseStart_126904 := by decide
  rcases family_descends (prefixWord ++ tailWord_126904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126954 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 5, 5]
def baseStart_126954 : Nat := 118140960795 + 126954 * 2 ^ 59
def prefixEnd_126954 : Nat := 4983230072969 + 3 ^ 40 * 126954 * 2
def baseEnd_126954 : Nat := 21729474337000508530385

theorem tailTrace_126954 : CollatzResearch.WordTrace tailWord_126954 prefixEnd_126954 21729474337000508530385 := by
  unfold tailWord_126954
  simp only [CollatzResearch.WordTrace]
  refine ⟨1157598195518703715528979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3086928521383209908077277 1157598195518703715528979)
  ·
    refine ⟨1736397293278055573293469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1157598195518703715528979 1736397293278055573293469)
    ·
      refine ⟨651148984979270839985051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1736397293278055573293469 651148984979270839985051)
      ·
        refine ⟨976723477468906259977577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651148984979270839985051 976723477468906259977577)
        ·
          refine ⟨732542608101679694983183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 976723477468906259977577 732542608101679694983183)
          ·
            refine ⟨1098813912152519542474775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732542608101679694983183 1098813912152519542474775)
            ·
              refine ⟨1648220868228779313712163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098813912152519542474775 1648220868228779313712163)
              ·
                refine ⟨2472331302343168970568245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1648220868228779313712163 2472331302343168970568245)
                ·
                  refine ⟨231781059594672090990773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2472331302343168970568245 231781059594672090990773)
                  ·
                    refine ⟨21729474337000508530385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 231781059594672090990773 21729474337000508530385)
                    ·
                      rfl

theorem cell23_126954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_126954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126954 prefixEnd_126954 := by exact prefixLift 126954
  have htrace : WordTrace (prefixWord ++ tailWord_126954) baseStart_126954 baseEnd_126954 := by
    simpa [prefixWord, tailWord_126954, baseEnd_126954] using wordTrace_append hprefix tailTrace_126954
  have hstable : (prefixWord ++ tailWord_126954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126954).length < 2 ^ (prefixWord ++ tailWord_126954).sum := by decide
  have hdescent : baseEnd_126954 < baseStart_126954 := by decide
  rcases family_descends (prefixWord ++ tailWord_126954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_126984 : List Nat := [2, 1, 3, 2, 1, 2, 1, 4, 1, 6]
def baseStart_126984 : Nat := 118140960795 + 126984 * 2 ^ 59
def prefixEnd_126984 : Nat := 4983230072969 + 3 ^ 40 * 126984 * 2
def baseEnd_126984 : Nat := 21734609143545469405339

theorem tailTrace_126984 : CollatzResearch.WordTrace tailWord_126984 prefixEnd_126984 21734609143545469405339 := by
  unfold tailWord_126984
  simp only [CollatzResearch.WordTrace]
  refine ⟨2315743485983064992854003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3087657981310753323805337 2315743485983064992854003)
  ·
    refine ⟨3473615228974597489281005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2315743485983064992854003 3473615228974597489281005)
    ·
      refine ⟨1302605710865474058480377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3473615228974597489281005 1302605710865474058480377)
      ·
        refine ⟨976954283149105543860283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1302605710865474058480377 976954283149105543860283)
        ·
          refine ⟨1465431424723658315790425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976954283149105543860283 1465431424723658315790425)
          ·
            refine ⟨1099073568542743736842819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1465431424723658315790425 1099073568542743736842819)
            ·
              refine ⟨1648610352814115605264229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099073568542743736842819 1648610352814115605264229)
              ·
                refine ⟨309114441152646675987043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1648610352814115605264229 309114441152646675987043)
                ·
                  refine ⟨463671661728970013980565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309114441152646675987043 463671661728970013980565)
                  ·
                    refine ⟨21734609143545469405339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 463671661728970013980565 21734609143545469405339)
                    ·
                      rfl

theorem cell23_126984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_126984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_126984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_126984 prefixEnd_126984 := by exact prefixLift 126984
  have htrace : WordTrace (prefixWord ++ tailWord_126984) baseStart_126984 baseEnd_126984 := by
    simpa [prefixWord, tailWord_126984, baseEnd_126984] using wordTrace_append hprefix tailTrace_126984
  have hstable : (prefixWord ++ tailWord_126984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_126984).length < 2 ^ (prefixWord ++ tailWord_126984).sum := by decide
  have hdescent : baseEnd_126984 < baseStart_126984 := by decide
  rcases family_descends (prefixWord ++ tailWord_126984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127018 : List Nat := [3, 1, 4, 1, 2, 3, 1, 1, 1, 6]
def baseStart_127018 : Nat := 118140960795 + 127018 * 2 ^ 59
def prefixEnd_127018 : Nat := 4983230072969 + 3 ^ 40 * 127018 * 2
def baseEnd_127018 : Nat := 21740428590963091730287

theorem tailTrace_127018 : CollatzResearch.WordTrace tailWord_127018 prefixEnd_127018 21740428590963091730287 := by
  unfold tailWord_127018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1158181763460738448111427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3088484702561969194963805 1158181763460738448111427)
  ·
    refine ⟨1737272645191107672167141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1158181763460738448111427 1737272645191107672167141)
    ·
      refine ⟨325738620973332688531339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1737272645191107672167141 325738620973332688531339)
      ·
        refine ⟨488607931459999032797009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325738620973332688531339 488607931459999032797009)
        ·
          refine ⟨366455948594999274597757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488607931459999032797009 366455948594999274597757)
          ·
            refine ⟨137420980723124727974159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366455948594999274597757 137420980723124727974159)
            ·
              refine ⟨206131471084687091961239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137420980723124727974159 206131471084687091961239)
              ·
                refine ⟨309197206627030637941859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206131471084687091961239 309197206627030637941859)
                ·
                  refine ⟨463795809940545956912789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309197206627030637941859 463795809940545956912789)
                  ·
                    refine ⟨21740428590963091730287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 463795809940545956912789 21740428590963091730287)
                    ·
                      rfl

theorem cell23_127018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_127018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127018 prefixEnd_127018 := by exact prefixLift 127018
  have htrace : WordTrace (prefixWord ++ tailWord_127018) baseStart_127018 baseEnd_127018 := by
    simpa [prefixWord, tailWord_127018, baseEnd_127018] using wordTrace_append hprefix tailTrace_127018
  have hstable : (prefixWord ++ tailWord_127018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127018).length < 2 ^ (prefixWord ++ tailWord_127018).sum := by decide
  have hdescent : baseEnd_127018 < baseStart_127018 := by decide
  rcases family_descends (prefixWord ++ tailWord_127018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127075 : List Nat := [1, 1, 1, 5, 1, 1, 6, 1, 2, 1, 3]
def baseStart_127075 : Nat := 118140960795 + 127075 * 2 ^ 59
def prefixEnd_127075 : Nat := 4983230072969 + 3 ^ 40 * 127075 * 2
def baseEnd_127075 : Nat := 65250554170195552178099

theorem tailTrace_127075 : CollatzResearch.WordTrace tailWord_127075 prefixEnd_127075 65250554170195552178099 := by
  unfold tailWord_127075
  simp only [CollatzResearch.WordTrace]
  refine ⟨4634806014636452527270679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3089870676424301684847119 4634806014636452527270679)
  ·
    refine ⟨6952209021954678790906019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4634806014636452527270679 6952209021954678790906019)
    ·
      refine ⟨10428313532932018186359029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6952209021954678790906019 10428313532932018186359029)
      ·
        refine ⟨977654393712376704971159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10428313532932018186359029 977654393712376704971159)
        ·
          refine ⟨1466481590568565057456739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977654393712376704971159 1466481590568565057456739)
          ·
            refine ⟨2199722385852847586185109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466481590568565057456739 2199722385852847586185109)
            ·
              refine ⟨103111986836852230602427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2199722385852847586185109 103111986836852230602427)
              ·
                refine ⟨154667980255278345903641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103111986836852230602427 154667980255278345903641)
                ·
                  refine ⟨116000985191458759427731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154667980255278345903641 116000985191458759427731)
                  ·
                    refine ⟨174001477787188139141597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116000985191458759427731 174001477787188139141597)
                    ·
                      refine ⟨65250554170195552178099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 174001477787188139141597 65250554170195552178099)
                      ·
                        rfl

theorem cell23_127075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_127075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127075 prefixEnd_127075 := by exact prefixLift 127075
  have htrace : WordTrace (prefixWord ++ tailWord_127075) baseStart_127075 baseEnd_127075 := by
    simpa [prefixWord, tailWord_127075, baseEnd_127075] using wordTrace_append hprefix tailTrace_127075
  have hstable : (prefixWord ++ tailWord_127075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127075).length < 2 ^ (prefixWord ++ tailWord_127075).sum := by decide
  have hdescent : baseEnd_127075 < baseStart_127075 := by decide
  rcases family_descends (prefixWord ++ tailWord_127075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127101 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_127101 : Nat := 118140960795 + 127101 * 2 ^ 59
def prefixEnd_127101 : Nat := 4983230072969 + 3 ^ 40 * 127101 * 2
def baseEnd_127101 : Nat := 65263904667212450452979

theorem tailTrace_127101 : CollatzResearch.WordTrace tailWord_127101 prefixEnd_127101 65263904667212450452979 := by
  unfold tailWord_127101
  simp only [CollatzResearch.WordTrace]
  refine ⟨4635754312542258967717157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3090502875028172645144771 4635754312542258967717157)
  ·
    refine ⟨869203933601673556446967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4635754312542258967717157 869203933601673556446967)
    ·
      refine ⟨1303805900402510334670451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 869203933601673556446967 1303805900402510334670451)
      ·
        refine ⟨1955708850603765502005677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1303805900402510334670451 1955708850603765502005677)
        ·
          refine ⟨733390818976412063252129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1955708850603765502005677 733390818976412063252129)
          ·
            refine ⟨550043114232309047439097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 733390818976412063252129 550043114232309047439097)
            ·
              refine ⟨412532335674231785579323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550043114232309047439097 412532335674231785579323)
              ·
                refine ⟨618798503511347678368985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412532335674231785579323 618798503511347678368985)
                ·
                  refine ⟨464098877633510758776739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618798503511347678368985 464098877633510758776739)
                  ·
                    refine ⟨696148316450266138165109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 464098877633510758776739 696148316450266138165109)
                    ·
                      refine ⟨65263904667212450452979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 696148316450266138165109 65263904667212450452979)
                      ·
                        rfl

theorem cell23_127101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_127101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127101 prefixEnd_127101 := by exact prefixLift 127101
  have htrace : WordTrace (prefixWord ++ tailWord_127101) baseStart_127101 baseEnd_127101 := by
    simpa [prefixWord, tailWord_127101, baseEnd_127101] using wordTrace_append hprefix tailTrace_127101
  have hstable : (prefixWord ++ tailWord_127101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127101).length < 2 ^ (prefixWord ++ tailWord_127101).sum := by decide
  have hdescent : baseEnd_127101 < baseStart_127101 := by decide
  rcases family_descends (prefixWord ++ tailWord_127101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127126 : List Nat := [5, 3, 2, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_127126 : Nat := 118140960795 + 127126 * 2 ^ 59
def prefixEnd_127126 : Nat := 4983230072969 + 3 ^ 40 * 127126 * 2
def baseEnd_127126 : Nat := 65276741683574852640365

theorem tailTrace_127126 : CollatzResearch.WordTrace tailWord_127126 prefixEnd_127126 65276741683574852640365 := by
  unfold tailWord_127126
  simp only [CollatzResearch.WordTrace]
  refine ⟨289791633590730514836077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3091110758301125491584821 289791633590730514836077)
  ·
    refine ⟨108671862596523943063529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289791633590730514836077 108671862596523943063529)
    ·
      refine ⟨81503896947392957297647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108671862596523943063529 81503896947392957297647)
      ·
        refine ⟨122255845421089435946471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81503896947392957297647 122255845421089435946471)
        ·
          refine ⟨183383768131634153919707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122255845421089435946471 183383768131634153919707)
          ·
            refine ⟨275075652197451230879561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183383768131634153919707 275075652197451230879561)
            ·
              refine ⟨206306739148088423159671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275075652197451230879561 206306739148088423159671)
              ·
                refine ⟨309460108722132634739507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206306739148088423159671 309460108722132634739507)
                ·
                  refine ⟨464190163083198952109261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309460108722132634739507 464190163083198952109261)
                  ·
                    refine ⟨174071311156199607040973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 464190163083198952109261 174071311156199607040973)
                    ·
                      refine ⟨65276741683574852640365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 174071311156199607040973 65276741683574852640365)
                      ·
                        rfl

theorem cell23_127126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_127126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127126 prefixEnd_127126 := by exact prefixLift 127126
  have htrace : WordTrace (prefixWord ++ tailWord_127126) baseStart_127126 baseEnd_127126 := by
    simpa [prefixWord, tailWord_127126, baseEnd_127126] using wordTrace_append hprefix tailTrace_127126
  have hstable : (prefixWord ++ tailWord_127126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127126).length < 2 ^ (prefixWord ++ tailWord_127126).sum := by decide
  have hdescent : baseEnd_127126 < baseStart_127126 := by decide
  rcases family_descends (prefixWord ++ tailWord_127126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127128 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 2, 2, 4]
def baseStart_127128 : Nat := 118140960795 + 127128 * 2 ^ 59
def prefixEnd_127128 : Nat := 4983230072969 + 3 ^ 40 * 127128 * 2
def baseEnd_127128 : Nat := 65277768644883844815355

theorem tailTrace_127128 : CollatzResearch.WordTrace tailWord_127128 prefixEnd_127128 65277768644883844815355 := by
  unfold tailWord_127128
  simp only [CollatzResearch.WordTrace]
  refine ⟨2318369541722221289475019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3091159388962961719300025 2318369541722221289475019)
  ·
    refine ⟨3477554312583331934212529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2318369541722221289475019 3477554312583331934212529)
    ·
      refine ⟨2608165734437498950659397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3477554312583331934212529 2608165734437498950659397)
      ·
        refine ⟨489031075207031053248637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2608165734437498950659397 489031075207031053248637)
        ·
          refine ⟨183386653202636644968239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 489031075207031053248637 183386653202636644968239)
          ·
            refine ⟨275079979803954967452359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183386653202636644968239 275079979803954967452359)
            ·
              refine ⟨412619969705932451178539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275079979803954967452359 412619969705932451178539)
              ·
                refine ⟨618929954558898676767809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412619969705932451178539 618929954558898676767809)
                ·
                  refine ⟨464197465919174007575857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 618929954558898676767809 464197465919174007575857)
                  ·
                    refine ⟨348148099439380505681893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 464197465919174007575857 348148099439380505681893)
                    ·
                      refine ⟨65277768644883844815355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 348148099439380505681893 65277768644883844815355)
                      ·
                        rfl

theorem cell23_127128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_127128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127128 prefixEnd_127128 := by exact prefixLift 127128
  have htrace : WordTrace (prefixWord ++ tailWord_127128) baseStart_127128 baseEnd_127128 := by
    simpa [prefixWord, tailWord_127128, baseEnd_127128] using wordTrace_append hprefix tailTrace_127128
  have hstable : (prefixWord ++ tailWord_127128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127128).length < 2 ^ (prefixWord ++ tailWord_127128).sum := by decide
  have hdescent : baseEnd_127128 < baseStart_127128 := by decide
  rcases family_descends (prefixWord ++ tailWord_127128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127138 : List Nat := [3, 3, 1, 3, 1, 2, 1, 2, 7]
def baseStart_127138 : Nat := 118140960795 + 127138 * 2 ^ 59
def prefixEnd_127138 : Nat := 4983230072969 + 3 ^ 40 * 127138 * 2
def baseEnd_127138 : Nat := 7253655939047645076701

theorem tailTrace_127138 : CollatzResearch.WordTrace tailWord_127138 prefixEnd_127138 7253655939047645076701 := by
  unfold tailWord_127138
  simp only [CollatzResearch.WordTrace]
  refine ⟨1159275953352053571703517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3091402542272142857876045 1159275953352053571703517)
  ·
    refine ⟨434728482507020089388819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1159275953352053571703517 434728482507020089388819)
    ·
      refine ⟨652092723760530134083229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434728482507020089388819 652092723760530134083229)
      ·
        refine ⟨244534771410198800281211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 652092723760530134083229 244534771410198800281211)
        ·
          refine ⟨366802157115298200421817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244534771410198800281211 366802157115298200421817)
          ·
            refine ⟨275101617836473650316363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366802157115298200421817 275101617836473650316363)
            ·
              refine ⟨412652426754710475474545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275101617836473650316363 412652426754710475474545)
              ·
                refine ⟨309489320066032856605909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412652426754710475474545 309489320066032856605909)
                ·
                  refine ⟨7253655939047645076701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 309489320066032856605909 7253655939047645076701)
                  ·
                    rfl

theorem cell23_127138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_127138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127138 prefixEnd_127138 := by exact prefixLift 127138
  have htrace : WordTrace (prefixWord ++ tailWord_127138) baseStart_127138 baseEnd_127138 := by
    simpa [prefixWord, tailWord_127138, baseEnd_127138] using wordTrace_append hprefix tailTrace_127138
  have hstable : (prefixWord ++ tailWord_127138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127138).length < 2 ^ (prefixWord ++ tailWord_127138).sum := by decide
  have hdescent : baseEnd_127138 < baseStart_127138 := by decide
  rcases family_descends (prefixWord ++ tailWord_127138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127166 : List Nat := [4, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2]
def baseStart_127166 : Nat := 118140960795 + 127166 * 2 ^ 59
def prefixEnd_127166 : Nat := 4983230072969 + 3 ^ 40 * 127166 * 2
def baseEnd_127166 : Nat := 65297280909754696140181

theorem tailTrace_127166 : CollatzResearch.WordTrace tailWord_127166 prefixEnd_127166 65297280909754696140181 := by
  unfold tailWord_127166
  simp only [CollatzResearch.WordTrace]
  refine ⟨579765632163346883604169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3092083371537850045888901 579765632163346883604169)
  ·
    refine ⟨434824224122510162703127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 579765632163346883604169 434824224122510162703127)
    ·
      refine ⟨652236336183765244054691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434824224122510162703127 652236336183765244054691)
      ·
        refine ⟨978354504275647866082037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652236336183765244054691 978354504275647866082037)
        ·
          refine ⟨91720734775841987445191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 978354504275647866082037 91720734775841987445191)
          ·
            refine ⟨137581102163762981167787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91720734775841987445191 137581102163762981167787)
            ·
              refine ⟨206371653245644471751681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137581102163762981167787 206371653245644471751681)
              ·
                refine ⟨154778739934233353813761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206371653245644471751681 154778739934233353813761)
                ·
                  refine ⟨116084054950675015360321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154778739934233353813761 116084054950675015360321)
                  ·
                    refine ⟨87063041213006261520241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116084054950675015360321 87063041213006261520241)
                    ·
                      refine ⟨65297280909754696140181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 87063041213006261520241 65297280909754696140181)
                      ·
                        rfl

theorem cell23_127166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_127166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127166 prefixEnd_127166 := by exact prefixLift 127166
  have htrace : WordTrace (prefixWord ++ tailWord_127166) baseStart_127166 baseEnd_127166 := by
    simpa [prefixWord, tailWord_127166, baseEnd_127166] using wordTrace_append hprefix tailTrace_127166
  have hstable : (prefixWord ++ tailWord_127166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127166).length < 2 ^ (prefixWord ++ tailWord_127166).sum := by decide
  have hdescent : baseEnd_127166 < baseStart_127166 := by decide
  rcases family_descends (prefixWord ++ tailWord_127166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127201 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_127201 : Nat := 118140960795 + 127201 * 2 ^ 59
def prefixEnd_127201 : Nat := 4983230072969 + 3 ^ 40 * 127201 * 2
def baseEnd_127201 : Nat := 65315252732662059202519

theorem tailTrace_127201 : CollatzResearch.WordTrace tailWord_127201 prefixEnd_127201 65315252732662059202519 := by
  unfold tailWord_127201
  simp only [CollatzResearch.WordTrace]
  refine ⟨4639401612179976046357457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3092934408119984030904971 4639401612179976046357457)
  ·
    refine ⟨3479551209134982034768093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4639401612179976046357457 3479551209134982034768093)
    ·
      refine ⟨1304831703425618263038035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3479551209134982034768093 1304831703425618263038035)
      ·
        refine ⟨1957247555138427394557053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1304831703425618263038035 1957247555138427394557053)
        ·
          refine ⟨733967833176910272958895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1957247555138427394557053 733967833176910272958895)
          ·
            refine ⟨1100951749765365409438343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733967833176910272958895 1100951749765365409438343)
            ·
              refine ⟨1651427624648048114157515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100951749765365409438343 1651427624648048114157515)
              ·
                refine ⟨2477141436972072171236273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1651427624648048114157515 2477141436972072171236273)
                ·
                  refine ⟨1857856077729054128427205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2477141436972072171236273 1857856077729054128427205)
                  ·
                    refine ⟨348348014574197649080101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1857856077729054128427205 348348014574197649080101)
                    ·
                      refine ⟨65315252732662059202519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 348348014574197649080101 65315252732662059202519)
                      ·
                        rfl

theorem cell23_127201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_127201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127201 prefixEnd_127201 := by exact prefixLift 127201
  have htrace : WordTrace (prefixWord ++ tailWord_127201) baseStart_127201 baseEnd_127201 := by
    simpa [prefixWord, tailWord_127201, baseEnd_127201] using wordTrace_append hprefix tailTrace_127201
  have hstable : (prefixWord ++ tailWord_127201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127201).length < 2 ^ (prefixWord ++ tailWord_127201).sum := by decide
  have hdescent : baseEnd_127201 < baseStart_127201 := by decide
  rcases family_descends (prefixWord ++ tailWord_127201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127208 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_127208 : Nat := 118140960795 + 127208 * 2 ^ 59
def prefixEnd_127208 : Nat := 4983230072969 + 3 ^ 40 * 127208 * 2
def baseEnd_127208 : Nat := 65318847097243531814987

theorem tailTrace_127208 : CollatzResearch.WordTrace tailWord_127208 prefixEnd_127208 65318847097243531814987 := by
  unfold tailWord_127208
  simp only [CollatzResearch.WordTrace]
  refine ⟨2319828461577308120931139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3093104615436410827908185 2319828461577308120931139)
  ·
    refine ⟨3479742692365962181396709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2319828461577308120931139 3479742692365962181396709)
    ·
      refine ⟨652451754818617909011883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3479742692365962181396709 652451754818617909011883)
      ·
        refine ⟨978677632227926863517825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652451754818617909011883 978677632227926863517825)
        ·
          refine ⟨734008224170945147638369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 978677632227926863517825 734008224170945147638369)
          ·
            refine ⟨550506168128208860728777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 734008224170945147638369 550506168128208860728777)
            ·
              refine ⟨412879626096156645546583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550506168128208860728777 412879626096156645546583)
              ·
                refine ⟨619319439144234968319875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412879626096156645546583 619319439144234968319875)
                ·
                  refine ⟨928979158716352452479813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619319439144234968319875 928979158716352452479813)
                  ·
                    refine ⟨174183592259316084839965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 928979158716352452479813 174183592259316084839965)
                    ·
                      refine ⟨65318847097243531814987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 174183592259316084839965 65318847097243531814987)
                      ·
                        rfl

theorem cell23_127208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_127208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127208 prefixEnd_127208 := by exact prefixLift 127208
  have htrace : WordTrace (prefixWord ++ tailWord_127208) baseStart_127208 baseEnd_127208 := by
    simpa [prefixWord, tailWord_127208, baseEnd_127208] using wordTrace_append hprefix tailTrace_127208
  have hstable : (prefixWord ++ tailWord_127208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127208).length < 2 ^ (prefixWord ++ tailWord_127208).sum := by decide
  have hdescent : baseEnd_127208 < baseStart_127208 := by decide
  rcases family_descends (prefixWord ++ tailWord_127208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127265 : List Nat := [1, 2, 3, 2, 1, 1, 3, 3, 2, 3, 2]
def baseStart_127265 : Nat := 118140960795 + 127265 * 2 ^ 59
def prefixEnd_127265 : Nat := 4983230072969 + 3 ^ 40 * 127265 * 2
def baseEnd_127265 : Nat := 65348115494549808802225

theorem tailTrace_127265 : CollatzResearch.WordTrace tailWord_127265 prefixEnd_127265 65348115494549808802225 := by
  unfold tailWord_127265
  simp only [CollatzResearch.WordTrace]
  refine ⟨4641735883948114976687249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3094490589298743317791499 4641735883948114976687249)
  ·
    refine ⟨3481301912961086232515437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4641735883948114976687249 3481301912961086232515437)
    ·
      refine ⟨1305488217360407337193289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3481301912961086232515437 1305488217360407337193289)
      ·
        refine ⟨979116163020305502894967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1305488217360407337193289 979116163020305502894967)
        ·
          refine ⟨1468674244530458254342451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979116163020305502894967 1468674244530458254342451)
          ·
            refine ⟨2203011366795687381513677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468674244530458254342451 2203011366795687381513677)
            ·
              refine ⟨826129262548382768067629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2203011366795687381513677 826129262548382768067629)
              ·
                refine ⟨309798473455643538025361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 826129262548382768067629 309798473455643538025361)
                ·
                  refine ⟨232348855091732653519021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309798473455643538025361 232348855091732653519021)
                  ·
                    refine ⟨87130820659399745069633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 232348855091732653519021 87130820659399745069633)
                    ·
                      refine ⟨65348115494549808802225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 87130820659399745069633 65348115494549808802225)
                      ·
                        rfl

theorem cell23_127265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_127265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127265 prefixEnd_127265 := by exact prefixLift 127265
  have htrace : WordTrace (prefixWord ++ tailWord_127265) baseStart_127265 baseEnd_127265 := by
    simpa [prefixWord, tailWord_127265, baseEnd_127265] using wordTrace_append hprefix tailTrace_127265
  have hstable : (prefixWord ++ tailWord_127265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127265).length < 2 ^ (prefixWord ++ tailWord_127265).sum := by decide
  have hdescent : baseEnd_127265 < baseStart_127265 := by decide
  rcases family_descends (prefixWord ++ tailWord_127265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127288 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 4, 4]
def baseStart_127288 : Nat := 118140960795 + 127288 * 2 ^ 59
def prefixEnd_127288 : Nat := 4983230072969 + 3 ^ 40 * 127288 * 2
def baseEnd_127288 : Nat := 21786641849867739604873

theorem tailTrace_127288 : CollatzResearch.WordTrace tailWord_127288 prefixEnd_127288 21786641849867739604873 := by
  unfold tailWord_127288
  simp only [CollatzResearch.WordTrace]
  refine ⟨2321287381432394952387259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3095049841909859936516345 2321287381432394952387259)
  ·
    refine ⟨3481931072148592428580889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2321287381432394952387259 3481931072148592428580889)
    ·
      refine ⟨2611448304111444321435667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3481931072148592428580889 2611448304111444321435667)
      ·
        refine ⟨3917172456167166482153501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2611448304111444321435667 3917172456167166482153501)
        ·
          refine ⟨1468939671062687430807563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3917172456167166482153501 1468939671062687430807563)
          ·
            refine ⟨2203409506594031146211345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468939671062687430807563 2203409506594031146211345)
            ·
              refine ⟨1652557129945523359658509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2203409506594031146211345 1652557129945523359658509)
              ·
                refine ⟨619708923729571259871941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1652557129945523359658509 619708923729571259871941)
                ·
                  refine ⟨116195423199294611225989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 619708923729571259871941 116195423199294611225989)
                  ·
                    refine ⟨21786641849867739604873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116195423199294611225989 21786641849867739604873)
                    ·
                      rfl

theorem cell23_127288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_127288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127288 prefixEnd_127288 := by exact prefixLift 127288
  have htrace : WordTrace (prefixWord ++ tailWord_127288) baseStart_127288 baseEnd_127288 := by
    simpa [prefixWord, tailWord_127288, baseEnd_127288] using wordTrace_append hprefix tailTrace_127288
  have hstable : (prefixWord ++ tailWord_127288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127288).length < 2 ^ (prefixWord ++ tailWord_127288).sum := by decide
  have hdescent : baseEnd_127288 < baseStart_127288 := by decide
  rcases family_descends (prefixWord ++ tailWord_127288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127289 : List Nat := [1, 2, 1, 6, 1, 2, 1, 4, 1, 1, 3]
def baseStart_127289 : Nat := 118140960795 + 127289 * 2 ^ 59
def prefixEnd_127289 : Nat := 4983230072969 + 3 ^ 40 * 127289 * 2
def baseEnd_127289 : Nat := 65360439030257714902115

theorem tailTrace_127289 : CollatzResearch.WordTrace tailWord_127289 prefixEnd_127289 65360439030257714902115 := by
  unfold tailWord_127289
  simp only [CollatzResearch.WordTrace]
  refine ⟨4642611235861167075560921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3095074157240778050373947 4642611235861167075560921)
  ·
    refine ⟨3481958426895875306670691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4642611235861167075560921 3481958426895875306670691)
    ·
      refine ⟨5222937640343812960006037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3481958426895875306670691 5222937640343812960006037)
      ·
        refine ⟨244825201891116232500283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5222937640343812960006037 244825201891116232500283)
        ·
          refine ⟨367237802836674348750425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244825201891116232500283 367237802836674348750425)
          ·
            refine ⟨275428352127505761562819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367237802836674348750425 275428352127505761562819)
            ·
              refine ⟨413142528191258642344229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275428352127505761562819 413142528191258642344229)
              ·
                refine ⟨77464224035860995439543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 413142528191258642344229 77464224035860995439543)
                ·
                  refine ⟨116196336053791493159315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77464224035860995439543 116196336053791493159315)
                  ·
                    refine ⟨174294504080687239738973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116196336053791493159315 174294504080687239738973)
                    ·
                      refine ⟨65360439030257714902115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 174294504080687239738973 65360439030257714902115)
                      ·
                        rfl

theorem cell23_127289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_127289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127289 prefixEnd_127289 := by exact prefixLift 127289
  have htrace : WordTrace (prefixWord ++ tailWord_127289) baseStart_127289 baseEnd_127289 := by
    simpa [prefixWord, tailWord_127289, baseEnd_127289] using wordTrace_append hprefix tailTrace_127289
  have hstable : (prefixWord ++ tailWord_127289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127289).length < 2 ^ (prefixWord ++ tailWord_127289).sum := by decide
  have hdescent : baseEnd_127289 < baseStart_127289 := by decide
  rcases family_descends (prefixWord ++ tailWord_127289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127312 : List Nat := [2, 1, 1, 1, 1, 7, 1, 2, 3, 2, 2]
def baseStart_127312 : Nat := 118140960795 + 127312 * 2 ^ 59
def prefixEnd_127312 : Nat := 4983230072969 + 3 ^ 40 * 127312 * 2
def baseEnd_127312 : Nat := 65372249085311124914509

theorem tailTrace_127312 : CollatzResearch.WordTrace tailWord_127312 prefixEnd_127312 65372249085311124914509 := by
  unfold tailWord_127312
  simp only [CollatzResearch.WordTrace]
  refine ⟨2321725057388921001824095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3095633409851894669098793 2321725057388921001824095)
  ·
    refine ⟨3482587586083381502736143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2321725057388921001824095 3482587586083381502736143)
    ·
      refine ⟨5223881379125072254104215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3482587586083381502736143 5223881379125072254104215)
      ·
        refine ⟨7835822068687608381156323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5223881379125072254104215 7835822068687608381156323)
        ·
          refine ⟨11753733103031412571734485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7835822068687608381156323 11753733103031412571734485)
          ·
            refine ⟨275478119602298732150027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 11753733103031412571734485 275478119602298732150027)
            ·
              refine ⟨413217179403448098225041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275478119602298732150027 413217179403448098225041)
              ·
                refine ⟨309912884552586073668781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413217179403448098225041 309912884552586073668781)
                ·
                  refine ⟨116217331707219777625793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309912884552586073668781 116217331707219777625793)
                  ·
                    refine ⟨87162998780414833219345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116217331707219777625793 87162998780414833219345)
                    ·
                      refine ⟨65372249085311124914509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 87162998780414833219345 65372249085311124914509)
                      ·
                        rfl

theorem cell23_127312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 3, 2, 2].length) (baseStart_127312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127312 prefixEnd_127312 := by exact prefixLift 127312
  have htrace : WordTrace (prefixWord ++ tailWord_127312) baseStart_127312 baseEnd_127312 := by
    simpa [prefixWord, tailWord_127312, baseEnd_127312] using wordTrace_append hprefix tailTrace_127312
  have hstable : (prefixWord ++ tailWord_127312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127312).length < 2 ^ (prefixWord ++ tailWord_127312).sum := by decide
  have hdescent : baseEnd_127312 < baseStart_127312 := by decide
  rcases family_descends (prefixWord ++ tailWord_127312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127372 : List Nat := [2, 2, 1, 2, 1, 4, 1, 4, 1, 3, 2]
def baseStart_127372 : Nat := 118140960795 + 127372 * 2 ^ 59
def prefixEnd_127372 : Nat := 4983230072969 + 3 ^ 40 * 127372 * 2
def baseEnd_127372 : Nat := 65403057924580890164233

theorem tailTrace_127372 : CollatzResearch.WordTrace tailWord_127372 prefixEnd_127372 65403057924580890164233 := by
  unfold tailWord_127372
  simp only [CollatzResearch.WordTrace]
  refine ⟨2322819247280236125416185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3097092329706981500554913 2322819247280236125416185)
  ·
    refine ⟨1742114435460177094062139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2322819247280236125416185 1742114435460177094062139)
    ·
      refine ⟨2613171653190265641093209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1742114435460177094062139 2613171653190265641093209)
      ·
        refine ⟨1959878739892699230819907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2613171653190265641093209 1959878739892699230819907)
        ·
          refine ⟨2939818109839048846229861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1959878739892699230819907 2939818109839048846229861)
          ·
            refine ⟨551215895594821658668099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2939818109839048846229861 551215895594821658668099)
            ·
              refine ⟨826823843392232488002149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551215895594821658668099 826823843392232488002149)
              ·
                refine ⟨155029470636043591500403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 826823843392232488002149 155029470636043591500403)
                ·
                  refine ⟨232544205954065387250605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155029470636043591500403 232544205954065387250605)
                  ·
                    refine ⟨87204077232774520218977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 232544205954065387250605 87204077232774520218977)
                    ·
                      refine ⟨65403057924580890164233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 87204077232774520218977 65403057924580890164233)
                      ·
                        rfl

theorem cell23_127372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_127372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127372 prefixEnd_127372 := by exact prefixLift 127372
  have htrace : WordTrace (prefixWord ++ tailWord_127372) baseStart_127372 baseEnd_127372 := by
    simpa [prefixWord, tailWord_127372, baseEnd_127372] using wordTrace_append hprefix tailTrace_127372
  have hstable : (prefixWord ++ tailWord_127372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127372).length < 2 ^ (prefixWord ++ tailWord_127372).sum := by decide
  have hdescent : baseEnd_127372 < baseStart_127372 := by decide
  rcases family_descends (prefixWord ++ tailWord_127372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127380 : List Nat := [2, 4, 2, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_127380 : Nat := 118140960795 + 127380 * 2 ^ 59
def prefixEnd_127380 : Nat := 4983230072969 + 3 ^ 40 * 127380 * 2
def baseEnd_127380 : Nat := 65407165769816858864197

theorem tailTrace_127380 : CollatzResearch.WordTrace tailWord_127380 prefixEnd_127380 65407165769816858864197 := by
  unfold tailWord_127380
  simp only [CollatzResearch.WordTrace]
  refine ⟨2322965139265744808561797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3097286852354326411415729 2322965139265744808561797)
  ·
    refine ⟨435555963612327151605337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2322965139265744808561797 435555963612327151605337)
    ·
      refine ⟨326666972709245363704003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435555963612327151605337 326666972709245363704003)
      ·
        refine ⟨490000459063868045556005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326666972709245363704003 490000459063868045556005)
        ·
          refine ⟨91875086074475258541751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 490000459063868045556005 91875086074475258541751)
          ·
            refine ⟨137812629111712887812627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91875086074475258541751 137812629111712887812627)
            ·
              refine ⟨206718943667569331718941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137812629111712887812627 206718943667569331718941)
              ·
                refine ⟨77519603875338499394603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206718943667569331718941 77519603875338499394603)
                ·
                  refine ⟨116279405813007749091905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77519603875338499394603 116279405813007749091905)
                  ·
                    refine ⟨87209554359755811818929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116279405813007749091905 87209554359755811818929)
                    ·
                      refine ⟨65407165769816858864197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 87209554359755811818929 65407165769816858864197)
                      ·
                        rfl

theorem cell23_127380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_127380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127380 prefixEnd_127380 := by exact prefixLift 127380
  have htrace : WordTrace (prefixWord ++ tailWord_127380) baseStart_127380 baseEnd_127380 := by
    simpa [prefixWord, tailWord_127380, baseEnd_127380] using wordTrace_append hprefix tailTrace_127380
  have hstable : (prefixWord ++ tailWord_127380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127380).length < 2 ^ (prefixWord ++ tailWord_127380).sum := by decide
  have hdescent : baseEnd_127380 < baseStart_127380 := by decide
  rcases family_descends (prefixWord ++ tailWord_127380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127385 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 3, 4, 2]
def baseStart_127385 : Nat := 118140960795 + 127385 * 2 ^ 59
def prefixEnd_127385 : Nat := 4983230072969 + 3 ^ 40 * 127385 * 2
def baseEnd_127385 : Nat := 65409733173089339301673

theorem tailTrace_127385 : CollatzResearch.WordTrace tailWord_127385 prefixEnd_127385 65409733173089339301673 := by
  unfold tailWord_127385
  simp only [CollatzResearch.WordTrace]
  refine ⟨4646112643513375471055609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3097408429008916980703739 4646112643513375471055609)
  ·
    refine ⟨3484584482635031603291707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4646112643513375471055609 3484584482635031603291707)
    ·
      refine ⟨5226876723952547404937561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3484584482635031603291707 5226876723952547404937561)
      ·
        refine ⟨3920157542964410553703171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5226876723952547404937561 3920157542964410553703171)
        ·
          refine ⟨5880236314446615830554757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3920157542964410553703171 5880236314446615830554757)
          ·
            refine ⟨1102544308958740468229017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5880236314446615830554757 1102544308958740468229017)
            ·
              refine ⟨826908231719055351171763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1102544308958740468229017 826908231719055351171763)
              ·
                refine ⟨1240362347578583026757645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826908231719055351171763 1240362347578583026757645)
                ·
                  refine ⟨465135880341968635034117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1240362347578583026757645 465135880341968635034117)
                  ·
                    refine ⟨87212977564119119068897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 465135880341968635034117 87212977564119119068897)
                    ·
                      refine ⟨65409733173089339301673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 87212977564119119068897 65409733173089339301673)
                      ·
                        rfl

theorem cell23_127385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 4, 2].length) (baseStart_127385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127385 prefixEnd_127385 := by exact prefixLift 127385
  have htrace : WordTrace (prefixWord ++ tailWord_127385) baseStart_127385 baseEnd_127385 := by
    simpa [prefixWord, tailWord_127385, baseEnd_127385] using wordTrace_append hprefix tailTrace_127385
  have hstable : (prefixWord ++ tailWord_127385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127385).length < 2 ^ (prefixWord ++ tailWord_127385).sum := by decide
  have hdescent : baseEnd_127385 < baseStart_127385 := by decide
  rcases family_descends (prefixWord ++ tailWord_127385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127413 : List Nat := [1, 3, 3, 2, 4, 1, 2, 1, 2, 1, 3]
def baseStart_127413 : Nat := 118140960795 + 127413 * 2 ^ 59
def prefixEnd_127413 : Nat := 4983230072969 + 3 ^ 40 * 127413 * 2
def baseEnd_127413 : Nat := 65424110631415229751545

theorem tailTrace_127413 : CollatzResearch.WordTrace tailWord_127413 prefixEnd_127413 65424110631415229751545 := by
  unfold tailWord_127413
  simp only [CollatzResearch.WordTrace]
  refine ⟨4647133887411936253074893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3098089258274624168716595 4647133887411936253074893)
  ·
    refine ⟨1742675207779476094903085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4647133887411936253074893 1742675207779476094903085)
    ·
      refine ⟨653503202917303535588657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1742675207779476094903085 653503202917303535588657)
      ·
        refine ⟨490127402187977651691493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653503202917303535588657 490127402187977651691493)
        ·
          refine ⟨91898887910245809692155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 490127402187977651691493 91898887910245809692155)
          ·
            refine ⟨137848331865368714538233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91898887910245809692155 137848331865368714538233)
            ·
              refine ⟨103386248899026535903675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137848331865368714538233 103386248899026535903675)
              ·
                refine ⟨155079373348539803855513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103386248899026535903675 155079373348539803855513)
                ·
                  refine ⟨116309530011404852891635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155079373348539803855513 116309530011404852891635)
                  ·
                    refine ⟨174464295017107279337453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116309530011404852891635 174464295017107279337453)
                    ·
                      refine ⟨65424110631415229751545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 174464295017107279337453 65424110631415229751545)
                      ·
                        rfl

theorem cell23_127413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_127413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127413 prefixEnd_127413 := by exact prefixLift 127413
  have htrace : WordTrace (prefixWord ++ tailWord_127413) baseStart_127413 baseEnd_127413 := by
    simpa [prefixWord, tailWord_127413, baseEnd_127413] using wordTrace_append hprefix tailTrace_127413
  have hstable : (prefixWord ++ tailWord_127413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127413).length < 2 ^ (prefixWord ++ tailWord_127413).sum := by decide
  have hdescent : baseEnd_127413 < baseStart_127413 := by decide
  rcases family_descends (prefixWord ++ tailWord_127413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127455 : List Nat := [1, 1, 2, 3, 3, 2, 2, 2, 2, 5]
def baseStart_127455 : Nat := 118140960795 + 127455 * 2 ^ 59
def prefixEnd_127455 : Nat := 4983230072969 + 3 ^ 40 * 127455 * 2
def baseEnd_127455 : Nat := 21815225606301355142117

theorem tailTrace_127455 : CollatzResearch.WordTrace tailWord_127455 prefixEnd_127455 21815225606301355142117 := by
  unfold tailWord_127455
  simp only [CollatzResearch.WordTrace]
  refine ⟨4648665753259777426103819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3099110502173184950735879 4648665753259777426103819)
  ·
    refine ⟨6972998629889666139155729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4648665753259777426103819 6972998629889666139155729)
    ·
      refine ⟨5229748972417249604366797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6972998629889666139155729 5229748972417249604366797)
      ·
        refine ⟨1961155864656468601637549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5229748972417249604366797 1961155864656468601637549)
        ·
          refine ⟨735433449246175725614081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1961155864656468601637549 735433449246175725614081)
          ·
            refine ⟨551575086934631794210561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 735433449246175725614081 551575086934631794210561)
            ·
              refine ⟨413681315200973845657921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551575086934631794210561 413681315200973845657921)
              ·
                refine ⟨310260986400730384243441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413681315200973845657921 310260986400730384243441)
                ·
                  refine ⟨232695739800547788182581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310260986400730384243441 232695739800547788182581)
                  ·
                    refine ⟨21815225606301355142117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 232695739800547788182581 21815225606301355142117)
                    ·
                      rfl

theorem cell23_127455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 5].length) (baseStart_127455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127455 prefixEnd_127455 := by exact prefixLift 127455
  have htrace : WordTrace (prefixWord ++ tailWord_127455) baseStart_127455 baseEnd_127455 := by
    simpa [prefixWord, tailWord_127455, baseEnd_127455] using wordTrace_append hprefix tailTrace_127455
  have hstable : (prefixWord ++ tailWord_127455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127455).length < 2 ^ (prefixWord ++ tailWord_127455).sum := by decide
  have hdescent : baseEnd_127455 < baseStart_127455 := by decide
  rcases family_descends (prefixWord ++ tailWord_127455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127488 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 6]
def baseStart_127488 : Nat := 118140960795 + 127488 * 2 ^ 59
def prefixEnd_127488 : Nat := 4983230072969 + 3 ^ 40 * 127488 * 2
def baseEnd_127488 : Nat := 65462621680502436313699

theorem tailTrace_127488 : CollatzResearch.WordTrace tailWord_127488 prefixEnd_127488 65462621680502436313699 := by
  unfold tailWord_127488
  simp only [CollatzResearch.WordTrace]
  refine ⟨2324934681070112031027559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3099912908093482708036745 2324934681070112031027559)
  ·
    refine ⟨3487402021605168046541339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2324934681070112031027559 3487402021605168046541339)
    ·
      refine ⟨5231103032407752069812009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3487402021605168046541339 5231103032407752069812009)
      ·
        refine ⟨3923327274305814052359007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5231103032407752069812009 3923327274305814052359007)
        ·
          refine ⟨5884990911458721078538511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3923327274305814052359007 5884990911458721078538511)
          ·
            refine ⟨8827486367188081617807767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5884990911458721078538511 8827486367188081617807767)
            ·
              refine ⟨13241229550782122426711651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8827486367188081617807767 13241229550782122426711651)
              ·
                refine ⟨19861844326173183640067477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13241229550782122426711651 19861844326173183640067477)
                ·
                  refine ⟨931023952789367983128163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19861844326173183640067477 931023952789367983128163)
                  ·
                    refine ⟨1396535929184051974692245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 931023952789367983128163 1396535929184051974692245)
                    ·
                      refine ⟨65462621680502436313699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1396535929184051974692245 65462621680502436313699)
                      ·
                        rfl

theorem cell23_127488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_127488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127488 prefixEnd_127488 := by exact prefixLift 127488
  have htrace : WordTrace (prefixWord ++ tailWord_127488) baseStart_127488 baseEnd_127488 := by
    simpa [prefixWord, tailWord_127488, baseEnd_127488] using wordTrace_append hprefix tailTrace_127488
  have hstable : (prefixWord ++ tailWord_127488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127488).length < 2 ^ (prefixWord ++ tailWord_127488).sum := by decide
  have hdescent : baseEnd_127488 < baseStart_127488 := by decide
  rcases family_descends (prefixWord ++ tailWord_127488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127492 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_127492 : Nat := 118140960795 + 127492 * 2 ^ 59
def prefixEnd_127492 : Nat := 4983230072969 + 3 ^ 40 * 127492 * 2
def baseEnd_127492 : Nat := 65464675603120420663681

theorem tailTrace_127492 : CollatzResearch.WordTrace tailWord_127492 prefixEnd_127492 65464675603120420663681 := by
  unfold tailWord_127492
  simp only [CollatzResearch.WordTrace]
  refine ⟨2325007627062866372600365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3100010169417155163467153 2325007627062866372600365)
  ·
    refine ⟨871877860148574889725137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2325007627062866372600365 871877860148574889725137)
    ·
      refine ⟨653908395111431167293853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 871877860148574889725137 653908395111431167293853)
      ·
        refine ⟨245215648166786687735195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 653908395111431167293853 245215648166786687735195)
        ·
          refine ⟨367823472250180031602793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245215648166786687735195 367823472250180031602793)
          ·
            refine ⟨275867604187635023702095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367823472250180031602793 275867604187635023702095)
            ·
              refine ⟨413801406281452535553143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275867604187635023702095 413801406281452535553143)
              ·
                refine ⟨620702109422178803329715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413801406281452535553143 620702109422178803329715)
                ·
                  refine ⟨931053164133268204994573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620702109422178803329715 931053164133268204994573)
                  ·
                    refine ⟨349144936549975576872965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 931053164133268204994573 349144936549975576872965)
                    ·
                      refine ⟨65464675603120420663681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 349144936549975576872965 65464675603120420663681)
                      ·
                        rfl

theorem cell23_127492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_127492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127492 prefixEnd_127492 := by exact prefixLift 127492
  have htrace : WordTrace (prefixWord ++ tailWord_127492) baseStart_127492 baseEnd_127492 := by
    simpa [prefixWord, tailWord_127492, baseEnd_127492] using wordTrace_append hprefix tailTrace_127492
  have hstable : (prefixWord ++ tailWord_127492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127492).length < 2 ^ (prefixWord ++ tailWord_127492).sum := by decide
  have hdescent : baseEnd_127492 < baseStart_127492 := by decide
  rcases family_descends (prefixWord ++ tailWord_127492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127552 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 1, 5, 2]
def baseStart_127552 : Nat := 118140960795 + 127552 * 2 ^ 59
def prefixEnd_127552 : Nat := 4983230072969 + 3 ^ 40 * 127552 * 2
def baseEnd_127552 : Nat := 65495484442390185913405

theorem tailTrace_127552 : CollatzResearch.WordTrace tailWord_127552 prefixEnd_127552 65495484442390185913405 := by
  unfold tailWord_127552
  simp only [CollatzResearch.WordTrace]
  refine ⟨2326101816954181496192455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3101469089272241994923273 2326101816954181496192455)
  ·
    refine ⟨3489152725431272244288683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2326101816954181496192455 3489152725431272244288683)
    ·
      refine ⟨5233729088146908366433025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3489152725431272244288683 5233729088146908366433025)
      ·
        refine ⟨3925296816110181274824769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5233729088146908366433025 3925296816110181274824769)
        ·
          refine ⟨2943972612082635956118577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3925296816110181274824769 2943972612082635956118577)
          ·
            refine ⟨2207979459061976967088933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2943972612082635956118577 2207979459061976967088933)
            ·
              refine ⟨413996148574120681329175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2207979459061976967088933 413996148574120681329175)
              ·
                refine ⟨620994222861181021993763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413996148574120681329175 620994222861181021993763)
                ·
                  refine ⟨931491334291771532990645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620994222861181021993763 931491334291771532990645)
                  ·
                    refine ⟨87327312589853581217873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 931491334291771532990645 87327312589853581217873)
                    ·
                      refine ⟨65495484442390185913405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 87327312589853581217873 65495484442390185913405)
                      ·
                        rfl

theorem cell23_127552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 1, 5, 2].length) (baseStart_127552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127552 prefixEnd_127552 := by exact prefixLift 127552
  have htrace : WordTrace (prefixWord ++ tailWord_127552) baseStart_127552 baseEnd_127552 := by
    simpa [prefixWord, tailWord_127552, baseEnd_127552] using wordTrace_append hprefix tailTrace_127552
  have hstable : (prefixWord ++ tailWord_127552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127552).length < 2 ^ (prefixWord ++ tailWord_127552).sum := by decide
  have hdescent : baseEnd_127552 < baseStart_127552 := by decide
  rcases family_descends (prefixWord ++ tailWord_127552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127562 : List Nat := [3, 1, 2, 1, 1, 4, 2, 3, 1, 5]
def baseStart_127562 : Nat := 118140960795 + 127562 * 2 ^ 59
def prefixEnd_127562 : Nat := 4983230072969 + 3 ^ 40 * 127562 * 2
def baseEnd_127562 : Nat := 21833539749645048929453

theorem tailTrace_127562 : CollatzResearch.WordTrace tailWord_127562 prefixEnd_127562 21833539749645048929453 := by
  unfold tailWord_127562
  simp only [CollatzResearch.WordTrace]
  refine ⟨1163142090968033675062235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3101712242581423133499293 1163142090968033675062235)
  ·
    refine ⟨1744713136452050512593353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1163142090968033675062235 1744713136452050512593353)
    ·
      refine ⟨1308534852339037884445015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1744713136452050512593353 1308534852339037884445015)
      ·
        refine ⟨1962802278508556826667523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1308534852339037884445015 1962802278508556826667523)
        ·
          refine ⟨2944203417762835240001285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1962802278508556826667523 2944203417762835240001285)
          ·
            refine ⟨552038140830531607500241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2944203417762835240001285 552038140830531607500241)
            ·
              refine ⟨414028605622898705625181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552038140830531607500241 414028605622898705625181)
              ·
                refine ⟨155260727108587014609443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414028605622898705625181 155260727108587014609443)
                ·
                  refine ⟨232891090662880521914165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155260727108587014609443 232891090662880521914165)
                  ·
                    refine ⟨21833539749645048929453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 232891090662880521914165 21833539749645048929453)
                    ·
                      rfl

theorem cell23_127562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_127562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127562 prefixEnd_127562 := by exact prefixLift 127562
  have htrace : WordTrace (prefixWord ++ tailWord_127562) baseStart_127562 baseEnd_127562 := by
    simpa [prefixWord, tailWord_127562, baseEnd_127562] using wordTrace_append hprefix tailTrace_127562
  have hstable : (prefixWord ++ tailWord_127562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127562).length < 2 ^ (prefixWord ++ tailWord_127562).sum := by decide
  have hdescent : baseEnd_127562 < baseStart_127562 := by decide
  rcases family_descends (prefixWord ++ tailWord_127562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127569 : List Nat := [1, 2, 2, 1, 3, 4, 1, 2, 2, 3, 2]
def baseStart_127569 : Nat := 118140960795 + 127569 * 2 ^ 59
def prefixEnd_127569 : Nat := 4983230072969 + 3 ^ 40 * 127569 * 2
def baseEnd_127569 : Nat := 65504213613516619400827

theorem tailTrace_127569 : CollatzResearch.WordTrace tailWord_127569 prefixEnd_127569 65504213613516619400827 := by
  unfold tailWord_127569
  simp only [CollatzResearch.WordTrace]
  refine ⟨4652823674846774895753761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3101882449897849930502507 4652823674846774895753761)
  ·
    refine ⟨3489617756135081171815321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4652823674846774895753761 3489617756135081171815321)
    ·
      refine ⟨2617213317101310878861491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3489617756135081171815321 2617213317101310878861491)
      ·
        refine ⟨3925819975651966318292237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2617213317101310878861491 3925819975651966318292237)
        ·
          refine ⟨1472182490869487369359589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3925819975651966318292237 1472182490869487369359589)
          ·
            refine ⟨276034217038028881754923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1472182490869487369359589 276034217038028881754923)
            ·
              refine ⟨414051325557043322632385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276034217038028881754923 414051325557043322632385)
              ·
                refine ⟨310538494167782491974289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414051325557043322632385 310538494167782491974289)
                ·
                  refine ⟨232903870625836868980717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310538494167782491974289 232903870625836868980717)
                  ·
                    refine ⟨87338951484688825867769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 232903870625836868980717 87338951484688825867769)
                    ·
                      refine ⟨65504213613516619400827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 87338951484688825867769 65504213613516619400827)
                      ·
                        rfl

theorem cell23_127569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 3, 2].length) (baseStart_127569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127569 prefixEnd_127569 := by exact prefixLift 127569
  have htrace : WordTrace (prefixWord ++ tailWord_127569) baseStart_127569 baseEnd_127569 := by
    simpa [prefixWord, tailWord_127569, baseEnd_127569] using wordTrace_append hprefix tailTrace_127569
  have hstable : (prefixWord ++ tailWord_127569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127569).length < 2 ^ (prefixWord ++ tailWord_127569).sum := by decide
  have hdescent : baseEnd_127569 < baseStart_127569 := by decide
  rcases family_descends (prefixWord ++ tailWord_127569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127599 : List Nat := [1, 1, 2, 1, 3, 2, 2, 4, 3, 2, 2]
def baseStart_127599 : Nat := 118140960795 + 127599 * 2 ^ 59
def prefixEnd_127599 : Nat := 4983230072969 + 3 ^ 40 * 127599 * 2
def baseEnd_127599 : Nat := 65519618033151502025689

theorem tailTrace_127599 : CollatzResearch.WordTrace tailWord_127599 prefixEnd_127599 65519618033151502025689 := by
  unfold tailWord_127599
  simp only [CollatzResearch.WordTrace]
  refine ⟨4653917864738090019345851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3102611909825393346230567 4653917864738090019345851)
  ·
    refine ⟨6980876797107135029018777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4653917864738090019345851 6980876797107135029018777)
    ·
      refine ⟨5235657597830351271764083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6980876797107135029018777 5235657597830351271764083)
      ·
        refine ⟨7853486396745526907646125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5235657597830351271764083 7853486396745526907646125)
        ·
          refine ⟨2945057398779572590367297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7853486396745526907646125 2945057398779572590367297)
          ·
            refine ⟨2208793049084679442775473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2945057398779572590367297 2208793049084679442775473)
            ·
              refine ⟨1656594786813509582081605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2208793049084679442775473 1656594786813509582081605)
              ·
                refine ⟨310611522527533046640301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1656594786813509582081605 310611522527533046640301)
                ·
                  refine ⟨116479320947824892490113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 310611522527533046640301 116479320947824892490113)
                  ·
                    refine ⟨87359490710868669367585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116479320947824892490113 87359490710868669367585)
                    ·
                      refine ⟨65519618033151502025689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 87359490710868669367585 65519618033151502025689)
                      ·
                        rfl

theorem cell23_127599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 2, 2].length) (baseStart_127599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127599 prefixEnd_127599 := by exact prefixLift 127599
  have htrace : WordTrace (prefixWord ++ tailWord_127599) baseStart_127599 baseEnd_127599 := by
    simpa [prefixWord, tailWord_127599, baseEnd_127599] using wordTrace_append hprefix tailTrace_127599
  have hstable : (prefixWord ++ tailWord_127599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127599).length < 2 ^ (prefixWord ++ tailWord_127599).sum := by decide
  have hdescent : baseEnd_127599 < baseStart_127599 := by decide
  rcases family_descends (prefixWord ++ tailWord_127599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127626 : List Nat := [3, 1, 2, 3, 3, 1, 2, 2, 2, 4]
def baseStart_127626 : Nat := 118140960795 + 127626 * 2 ^ 59
def prefixEnd_127626 : Nat := 4983230072969 + 3 ^ 40 * 127626 * 2
def baseEnd_127626 : Nat := 21844494003607632129355

theorem tailTrace_127626 : CollatzResearch.WordTrace tailWord_127626 prefixEnd_127626 21844494003607632129355 := by
  unfold tailWord_127626
  simp only [CollatzResearch.WordTrace]
  refine ⟨1163725658910068407644683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3103268423760182420385821 1163725658910068407644683)
  ·
    refine ⟨1745588488365102611467025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1163725658910068407644683 1745588488365102611467025)
    ·
      refine ⟨1309191366273826958600269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1745588488365102611467025 1309191366273826958600269)
      ·
        refine ⟨490946762352685109475101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1309191366273826958600269 490946762352685109475101)
        ·
          refine ⟨184105035882256916053163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490946762352685109475101 184105035882256916053163)
          ·
            refine ⟨276157553823385374079745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184105035882256916053163 276157553823385374079745)
            ·
              refine ⟨207118165367539030559809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276157553823385374079745 207118165367539030559809)
              ·
                refine ⟨155338624025654272919857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207118165367539030559809 155338624025654272919857)
                ·
                  refine ⟨116503968019240704689893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155338624025654272919857 116503968019240704689893)
                  ·
                    refine ⟨21844494003607632129355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 116503968019240704689893 21844494003607632129355)
                    ·
                      rfl

theorem cell23_127626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_127626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127626 prefixEnd_127626 := by exact prefixLift 127626
  have htrace : WordTrace (prefixWord ++ tailWord_127626) baseStart_127626 baseEnd_127626 := by
    simpa [prefixWord, tailWord_127626, baseEnd_127626] using wordTrace_append hprefix tailTrace_127626
  have hstable : (prefixWord ++ tailWord_127626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127626).length < 2 ^ (prefixWord ++ tailWord_127626).sum := by decide
  have hdescent : baseEnd_127626 < baseStart_127626 := by decide
  rcases family_descends (prefixWord ++ tailWord_127626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127676 : List Nat := [2, 2, 2, 3, 1, 1, 3, 3, 1, 3, 2]
def baseStart_127676 : Nat := 118140960795 + 127676 * 2 ^ 59
def prefixEnd_127676 : Nat := 4983230072969 + 3 ^ 40 * 127676 * 2
def baseEnd_127676 : Nat := 65559156043547700762835

theorem tailTrace_127676 : CollatzResearch.WordTrace tailWord_127676 prefixEnd_127676 65559156043547700762835 := by
  unfold tailWord_127676
  simp only [CollatzResearch.WordTrace]
  refine ⟨2328363142729566084949441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3104484190306088113265921 2328363142729566084949441)
  ·
    refine ⟨1746272357047174563712081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2328363142729566084949441 1746272357047174563712081)
    ·
      refine ⟨1309704267785380922784061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1746272357047174563712081 1309704267785380922784061)
      ·
        refine ⟨491139100419517846044023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1309704267785380922784061 491139100419517846044023)
        ·
          refine ⟨736708650629276769066035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491139100419517846044023 736708650629276769066035)
          ·
            refine ⟨1105062975943915153599053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736708650629276769066035 1105062975943915153599053)
            ·
              refine ⟨414398615978968182599645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1105062975943915153599053 414398615978968182599645)
              ·
                refine ⟨155399480992113068474867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414398615978968182599645 155399480992113068474867)
                ·
                  refine ⟨233099221488169602712301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155399480992113068474867 233099221488169602712301)
                  ·
                    refine ⟨87412208058063601017113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 233099221488169602712301 87412208058063601017113)
                    ·
                      refine ⟨65559156043547700762835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 87412208058063601017113 65559156043547700762835)
                      ·
                        rfl

theorem cell23_127676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_127676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127676 prefixEnd_127676 := by exact prefixLift 127676
  have htrace : WordTrace (prefixWord ++ tailWord_127676) baseStart_127676 baseEnd_127676 := by
    simpa [prefixWord, tailWord_127676, baseEnd_127676] using wordTrace_append hprefix tailTrace_127676
  have hstable : (prefixWord ++ tailWord_127676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127676).length < 2 ^ (prefixWord ++ tailWord_127676).sum := by decide
  have hdescent : baseEnd_127676 < baseStart_127676 := by decide
  rcases family_descends (prefixWord ++ tailWord_127676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127685 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 1, 5, 6]
def baseStart_127685 : Nat := 118140960795 + 127685 * 2 ^ 59
def prefixEnd_127685 : Nat := 4983230072969 + 3 ^ 40 * 127685 * 2
def baseEnd_127685 : Nat := 65563777369438165550293

theorem tailTrace_127685 : CollatzResearch.WordTrace tailWord_127685 prefixEnd_127685 65563777369438165550293 := by
  unfold tailWord_127685
  simp only [CollatzResearch.WordTrace]
  refine ⟨4657054542426526706976509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3104703028284351137984339 4657054542426526706976509)
  ·
    refine ⟨1746395453409947515116191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4657054542426526706976509 1746395453409947515116191)
    ·
      refine ⟨2619593180114921272674287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1746395453409947515116191 2619593180114921272674287)
      ·
        refine ⟨3929389770172381909011431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2619593180114921272674287 3929389770172381909011431)
        ·
          refine ⟨5894084655258572863517147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3929389770172381909011431 5894084655258572863517147)
          ·
            refine ⟨8841126982887859295275721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5894084655258572863517147 8841126982887859295275721)
            ·
              refine ⟨6630845237165894471456791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8841126982887859295275721 6630845237165894471456791)
              ·
                refine ⟨9946267855748841707185187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6630845237165894471456791 9946267855748841707185187)
                ·
                  refine ⟨14919401783623262560777781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9946267855748841707185187 14919401783623262560777781)
                  ·
                    refine ⟨1398693917214680865072917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14919401783623262560777781 1398693917214680865072917)
                    ·
                      refine ⟨65563777369438165550293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1398693917214680865072917 65563777369438165550293)
                      ·
                        rfl

theorem cell23_127685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_127685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127685 prefixEnd_127685 := by exact prefixLift 127685
  have htrace : WordTrace (prefixWord ++ tailWord_127685) baseStart_127685 baseEnd_127685 := by
    simpa [prefixWord, tailWord_127685, baseEnd_127685] using wordTrace_append hprefix tailTrace_127685
  have hstable : (prefixWord ++ tailWord_127685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127685).length < 2 ^ (prefixWord ++ tailWord_127685).sum := by decide
  have hdescent : baseEnd_127685 < baseStart_127685 := by decide
  rcases family_descends (prefixWord ++ tailWord_127685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127700 : List Nat := [2, 4, 1, 3, 2, 1, 3, 1, 2, 1, 3]
def baseStart_127700 : Nat := 118140960795 + 127700 * 2 ^ 59
def prefixEnd_127700 : Nat := 4983230072969 + 3 ^ 40 * 127700 * 2
def baseEnd_127700 : Nat := 65571479579255606862725

theorem tailTrace_127700 : CollatzResearch.WordTrace tailWord_127700 prefixEnd_127700 65571479579255606862725 := by
  unfold tailWord_127700
  simp only [CollatzResearch.WordTrace]
  refine ⟨2328800818686092134386277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3105067758248122845848369 2328800818686092134386277)
  ·
    refine ⟨436650153503642275197427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2328800818686092134386277 436650153503642275197427)
    ·
      refine ⟨654975230255463412796141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436650153503642275197427 654975230255463412796141)
      ·
        refine ⟨245615711345798779798553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 654975230255463412796141 245615711345798779798553)
        ·
          refine ⟨184211783509349084848915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245615711345798779798553 184211783509349084848915)
          ·
            refine ⟨276317675264023627273373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184211783509349084848915 276317675264023627273373)
            ·
              refine ⟨103619128224008860227515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276317675264023627273373 103619128224008860227515)
              ·
                refine ⟨155428692336013290341273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103619128224008860227515 155428692336013290341273)
                ·
                  refine ⟨116571519252009967755955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 155428692336013290341273 116571519252009967755955)
                  ·
                    refine ⟨174857278878014951633933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116571519252009967755955 174857278878014951633933)
                    ·
                      refine ⟨65571479579255606862725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 174857278878014951633933 65571479579255606862725)
                      ·
                        rfl

theorem cell23_127700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_127700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127700 prefixEnd_127700 := by exact prefixLift 127700
  have htrace : WordTrace (prefixWord ++ tailWord_127700) baseStart_127700 baseEnd_127700 := by
    simpa [prefixWord, tailWord_127700, baseEnd_127700] using wordTrace_append hprefix tailTrace_127700
  have hstable : (prefixWord ++ tailWord_127700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127700).length < 2 ^ (prefixWord ++ tailWord_127700).sum := by decide
  have hdescent : baseEnd_127700 < baseStart_127700 := by decide
  rcases family_descends (prefixWord ++ tailWord_127700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127746 : List Nat := [3, 4, 1, 1, 1, 4, 1, 1, 7]
def baseStart_127746 : Nat := 118140960795 + 127746 * 2 ^ 59
def prefixEnd_127746 : Nat := 4983230072969 + 3 ^ 40 * 127746 * 2
def baseEnd_127746 : Nat := 7288344409929158543057

theorem tailTrace_127746 : CollatzResearch.WordTrace tailWord_127746 prefixEnd_127746 7288344409929158543057 := by
  unfold tailWord_127746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1164819848801383531236773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3106186263470356083298061 1164819848801383531236773)
  ·
    refine ⟨218403721650259412106895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1164819848801383531236773 218403721650259412106895)
    ·
      refine ⟨327605582475389118160343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218403721650259412106895 327605582475389118160343)
      ·
        refine ⟨491408373713083677240515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327605582475389118160343 491408373713083677240515)
        ·
          refine ⟨737112560569625515860773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491408373713083677240515 737112560569625515860773)
          ·
            refine ⟨138208605106804784223895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 737112560569625515860773 138208605106804784223895)
            ·
              refine ⟨207312907660207176335843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138208605106804784223895 207312907660207176335843)
              ·
                refine ⟨310969361490310764503765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207312907660207176335843 310969361490310764503765)
                ·
                  refine ⟨7288344409929158543057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 310969361490310764503765 7288344409929158543057)
                  ·
                    rfl

theorem cell23_127746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_127746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127746 prefixEnd_127746 := by exact prefixLift 127746
  have htrace : WordTrace (prefixWord ++ tailWord_127746) baseStart_127746 baseEnd_127746 := by
    simpa [prefixWord, tailWord_127746, baseEnd_127746] using wordTrace_append hprefix tailTrace_127746
  have hstable : (prefixWord ++ tailWord_127746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127746).length < 2 ^ (prefixWord ++ tailWord_127746).sum := by decide
  have hdescent : baseEnd_127746 < baseStart_127746 := by decide
  rcases family_descends (prefixWord ++ tailWord_127746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127752 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_127752 : Nat := 118140960795 + 127752 * 2 ^ 59
def prefixEnd_127752 : Nat := 4983230072969 + 3 ^ 40 * 127752 * 2
def baseEnd_127752 : Nat := 65598180573289403412485

theorem tailTrace_127752 : CollatzResearch.WordTrace tailWord_127752 prefixEnd_127752 65598180573289403412485 := by
  unfold tailWord_127752
  simp only [CollatzResearch.WordTrace]
  refine ⟨2329749116591898574832755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3106332155455864766443673 2329749116591898574832755)
  ·
    refine ⟨3494623674887847862249133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2329749116591898574832755 3494623674887847862249133)
    ·
      refine ⟨1310483878082942948343425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3494623674887847862249133 1310483878082942948343425)
      ·
        refine ⟨982862908562207211257569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1310483878082942948343425 982862908562207211257569)
        ·
          refine ⟨737147181421655408443177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 982862908562207211257569 737147181421655408443177)
          ·
            refine ⟨552860386066241556332383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 737147181421655408443177 552860386066241556332383)
            ·
              refine ⟨829290579099362334498575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552860386066241556332383 829290579099362334498575)
              ·
                refine ⟨1243935868649043501747863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829290579099362334498575 1243935868649043501747863)
                ·
                  refine ⟨1865903802973565252621795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243935868649043501747863 1865903802973565252621795)
                  ·
                    refine ⟨2798855704460347878932693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1865903802973565252621795 2798855704460347878932693)
                    ·
                      refine ⟨65598180573289403412485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2798855704460347878932693 65598180573289403412485)
                      ·
                        rfl

theorem cell23_127752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_127752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127752 prefixEnd_127752 := by exact prefixLift 127752
  have htrace : WordTrace (prefixWord ++ tailWord_127752) baseStart_127752 baseEnd_127752 := by
    simpa [prefixWord, tailWord_127752, baseEnd_127752] using wordTrace_append hprefix tailTrace_127752
  have hstable : (prefixWord ++ tailWord_127752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127752).length < 2 ^ (prefixWord ++ tailWord_127752).sum := by decide
  have hdescent : baseEnd_127752 < baseStart_127752 := by decide
  rcases family_descends (prefixWord ++ tailWord_127752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127779 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 4, 4, 2]
def baseStart_127779 : Nat := 118140960795 + 127779 * 2 ^ 59
def prefixEnd_127779 : Nat := 4983230072969 + 3 ^ 40 * 127779 * 2
def baseEnd_127779 : Nat := 65612044550960797774861

theorem tailTrace_127779 : CollatzResearch.WordTrace tailWord_127779 prefixEnd_127779 65612044550960797774861 := by
  unfold tailWord_127779
  simp only [CollatzResearch.WordTrace]
  refine ⟨4660483004085980760898391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3106988669390653840598927 4660483004085980760898391)
  ·
    refine ⟨6990724506128971141347587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4660483004085980760898391 6990724506128971141347587)
    ·
      refine ⟨10486086759193456712021381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6990724506128971141347587 10486086759193456712021381)
      ·
        refine ⟨1966141267348773133504009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10486086759193456712021381 1966141267348773133504009)
        ·
          refine ⟨1474605950511579850128007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1966141267348773133504009 1474605950511579850128007)
          ·
            refine ⟨2211908925767369775192011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474605950511579850128007 2211908925767369775192011)
            ·
              refine ⟨3317863388651054662788017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2211908925767369775192011 3317863388651054662788017)
              ·
                refine ⟨2488397541488290997091013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3317863388651054662788017 2488397541488290997091013)
                ·
                  refine ⟨466574539029054561954565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2488397541488290997091013 466574539029054561954565)
                  ·
                    refine ⟨87482726067947730366481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 466574539029054561954565 87482726067947730366481)
                    ·
                      refine ⟨65612044550960797774861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 87482726067947730366481 65612044550960797774861)
                      ·
                        rfl

theorem cell23_127779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_127779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127779 prefixEnd_127779 := by exact prefixLift 127779
  have htrace : WordTrace (prefixWord ++ tailWord_127779) baseStart_127779 baseEnd_127779 := by
    simpa [prefixWord, tailWord_127779, baseEnd_127779] using wordTrace_append hprefix tailTrace_127779
  have hstable : (prefixWord ++ tailWord_127779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127779).length < 2 ^ (prefixWord ++ tailWord_127779).sum := by decide
  have hdescent : baseEnd_127779 < baseStart_127779 := by decide
  rcases family_descends (prefixWord ++ tailWord_127779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127799 : List Nat := [1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 3]
def baseStart_127799 : Nat := 118140960795 + 127799 * 2 ^ 59
def prefixEnd_127799 : Nat := 4983230072969 + 3 ^ 40 * 127799 * 2
def baseEnd_127799 : Nat := 65622314164050719524769

theorem tailTrace_127799 : CollatzResearch.WordTrace tailWord_127799 prefixEnd_127799 65622314164050719524769 := by
  unfold tailWord_127799
  simp only [CollatzResearch.WordTrace]
  refine ⟨4661212464013524176626451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3107474976009016117750967 4661212464013524176626451)
  ·
    refine ⟨6991818696020286264939677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4661212464013524176626451 6991818696020286264939677)
    ·
      refine ⟨2621932011007607349352379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6991818696020286264939677 2621932011007607349352379)
      ·
        refine ⟨3932898016511411024028569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2621932011007607349352379 3932898016511411024028569)
        ·
          refine ⟨2949673512383558268021427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3932898016511411024028569 2949673512383558268021427)
          ·
            refine ⟨4424510268575337402032141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2949673512383558268021427 4424510268575337402032141)
            ·
              refine ⟨1659191350715751525762053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4424510268575337402032141 1659191350715751525762053)
              ·
                refine ⟨311098378259203411080385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1659191350715751525762053 311098378259203411080385)
                ·
                  refine ⟨233323783694402558310289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311098378259203411080385 233323783694402558310289)
                  ·
                    refine ⟨174992837770801918732717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 233323783694402558310289 174992837770801918732717)
                    ·
                      refine ⟨65622314164050719524769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 174992837770801918732717 65622314164050719524769)
                      ·
                        rfl

theorem cell23_127799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_127799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127799 prefixEnd_127799 := by exact prefixLift 127799
  have htrace : WordTrace (prefixWord ++ tailWord_127799) baseStart_127799 baseEnd_127799 := by
    simpa [prefixWord, tailWord_127799, baseEnd_127799] using wordTrace_append hprefix tailTrace_127799
  have hstable : (prefixWord ++ tailWord_127799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127799).length < 2 ^ (prefixWord ++ tailWord_127799).sum := by decide
  have hdescent : baseEnd_127799 < baseStart_127799 := by decide
  rcases family_descends (prefixWord ++ tailWord_127799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127856 : List Nat := [2, 1, 1, 1, 4, 1, 2, 4, 2, 3, 2]
def baseStart_127856 : Nat := 118140960795 + 127856 * 2 ^ 59
def prefixEnd_127856 : Nat := 4983230072969 + 3 ^ 40 * 127856 * 2
def baseEnd_127856 : Nat := 65651582561356996512007

theorem tailTrace_127856 : CollatzResearch.WordTrace tailWord_127856 prefixEnd_127856 65651582561356996512007 := by
  unfold tailWord_127856
  simp only [CollatzResearch.WordTrace]
  refine ⟨2331645712403511455725711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3108860949871348607634281 2331645712403511455725711)
  ·
    refine ⟨3497468568605267183588567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2331645712403511455725711 3497468568605267183588567)
    ·
      refine ⟨5246202852907900775382851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3497468568605267183588567 5246202852907900775382851)
      ·
        refine ⟨7869304279361851163074277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5246202852907900775382851 7869304279361851163074277)
        ·
          refine ⟨1475494552380347093076427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7869304279361851163074277 1475494552380347093076427)
          ·
            refine ⟨2213241828570520639614641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475494552380347093076427 2213241828570520639614641)
            ·
              refine ⟨1659931371427890479710981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2213241828570520639614641 1659931371427890479710981)
              ·
                refine ⟨311237132142729464945809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1659931371427890479710981 311237132142729464945809)
                ·
                  refine ⟨233427849107047098709357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311237132142729464945809 233427849107047098709357)
                  ·
                    refine ⟨87535443415142662016009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 233427849107047098709357 87535443415142662016009)
                    ·
                      refine ⟨65651582561356996512007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 87535443415142662016009 65651582561356996512007)
                      ·
                        rfl

theorem cell23_127856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 2, 3, 2].length) (baseStart_127856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127856 prefixEnd_127856 := by exact prefixLift 127856
  have htrace : WordTrace (prefixWord ++ tailWord_127856) baseStart_127856 baseEnd_127856 := by
    simpa [prefixWord, tailWord_127856, baseEnd_127856] using wordTrace_append hprefix tailTrace_127856
  have hstable : (prefixWord ++ tailWord_127856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127856).length < 2 ^ (prefixWord ++ tailWord_127856).sum := by decide
  have hdescent : baseEnd_127856 < baseStart_127856 := by decide
  rcases family_descends (prefixWord ++ tailWord_127856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127869 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_127869 : Nat := 118140960795 + 127869 * 2 ^ 59
def prefixEnd_127869 : Nat := 4983230072969 + 3 ^ 40 * 127869 * 2
def baseEnd_127869 : Nat := 65658257809865445649447

theorem tailTrace_127869 : CollatzResearch.WordTrace tailWord_127869 prefixEnd_127869 65658257809865445649447 := by
  unfold tailWord_127869
  simp only [CollatzResearch.WordTrace]
  refine ⟨4663765573759926131674661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3109177049173284087783107 4663765573759926131674661)
  ·
    refine ⟨874456045079986149688999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4663765573759926131674661 874456045079986149688999)
    ·
      refine ⟨1311684067619979224533499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 874456045079986149688999 1311684067619979224533499)
      ·
        refine ⟨1967526101429968836800249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1311684067619979224533499 1967526101429968836800249)
        ·
          refine ⟨1475644576072476627600187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1967526101429968836800249 1475644576072476627600187)
          ·
            refine ⟨2213466864108714941400281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475644576072476627600187 2213466864108714941400281)
            ·
              refine ⟨1660100148081536206050211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2213466864108714941400281 1660100148081536206050211)
              ·
                refine ⟨2490150222122304309075317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1660100148081536206050211 2490150222122304309075317)
                ·
                  refine ⟨233451583323966028975811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2490150222122304309075317 233451583323966028975811)
                  ·
                    refine ⟨350177374985949043463717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 233451583323966028975811 350177374985949043463717)
                    ·
                      refine ⟨65658257809865445649447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 350177374985949043463717 65658257809865445649447)
                      ·
                        rfl

theorem cell23_127869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_127869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127869 prefixEnd_127869 := by exact prefixLift 127869
  have htrace : WordTrace (prefixWord ++ tailWord_127869) baseStart_127869 baseEnd_127869 := by
    simpa [prefixWord, tailWord_127869, baseEnd_127869] using wordTrace_append hprefix tailTrace_127869
  have hstable : (prefixWord ++ tailWord_127869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127869).length < 2 ^ (prefixWord ++ tailWord_127869).sum := by decide
  have hdescent : baseEnd_127869 < baseStart_127869 := by decide
  rcases family_descends (prefixWord ++ tailWord_127869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127870 : List Nat := [4, 2, 3, 1, 2, 1, 3, 1, 6]
def baseStart_127870 : Nat := 118140960795 + 127870 * 2 ^ 59
def prefixEnd_127870 : Nat := 4983230072969 + 3 ^ 40 * 127870 * 2
def baseEnd_127870 : Nat := 7295419032279993526327

theorem tailTrace_127870 : CollatzResearch.WordTrace tailWord_127870 prefixEnd_127870 7295419032279993526327 := by
  unfold tailWord_127870
  simp only [CollatzResearch.WordTrace]
  refine ⟨582975255844537912807633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3109201364504202201640709 582975255844537912807633)
  ·
    refine ⟨437231441883403434605725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 582975255844537912807633 437231441883403434605725)
    ·
      refine ⟨163961790706276287977147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437231441883403434605725 163961790706276287977147)
      ·
        refine ⟨245942686059414431965721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163961790706276287977147 245942686059414431965721)
        ·
          refine ⟨184457014544560823974291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245942686059414431965721 184457014544560823974291)
          ·
            refine ⟨276685521816841235961437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184457014544560823974291 276685521816841235961437)
            ·
              refine ⟨103757070681315463485539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 276685521816841235961437 103757070681315463485539)
              ·
                refine ⟨155635606021973195228309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103757070681315463485539 155635606021973195228309)
                ·
                  refine ⟨7295419032279993526327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 155635606021973195228309 7295419032279993526327)
                  ·
                    rfl

theorem cell23_127870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_127870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127870 prefixEnd_127870 := by exact prefixLift 127870
  have htrace : WordTrace (prefixWord ++ tailWord_127870) baseStart_127870 baseEnd_127870 := by
    simpa [prefixWord, tailWord_127870, baseEnd_127870] using wordTrace_append hprefix tailTrace_127870
  have hstable : (prefixWord ++ tailWord_127870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127870).length < 2 ^ (prefixWord ++ tailWord_127870).sum := by decide
  have hdescent : baseEnd_127870 < baseStart_127870 := by decide
  rcases family_descends (prefixWord ++ tailWord_127870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127906 : List Nat := [3, 3, 1, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_127906 : Nat := 118140960795 + 127906 * 2 ^ 59
def prefixEnd_127906 : Nat := 4983230072969 + 3 ^ 40 * 127906 * 2
def baseEnd_127906 : Nat := 65677256594081800886777

theorem tailTrace_127906 : CollatzResearch.WordTrace tailWord_127906 prefixEnd_127906 65677256594081800886777 := by
  unfold tailWord_127906
  simp only [CollatzResearch.WordTrace]
  refine ⟨1166278768656470362692893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3110076716417254300514381 1166278768656470362692893)
  ·
    refine ⟨437354538246176386009835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1166278768656470362692893 437354538246176386009835)
    ·
      refine ⟨656031807369264579014753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437354538246176386009835 656031807369264579014753)
      ·
        refine ⟨492023855526948434261065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 656031807369264579014753 492023855526948434261065)
        ·
          refine ⟨369017891645211325695799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492023855526948434261065 369017891645211325695799)
          ·
            refine ⟨553526837467816988543699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369017891645211325695799 553526837467816988543699)
            ·
              refine ⟨830290256201725482815549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553526837467816988543699 830290256201725482815549)
              ·
                refine ⟨311358846075647056055831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 830290256201725482815549 311358846075647056055831)
                ·
                  refine ⟨467038269113470584083747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311358846075647056055831 467038269113470584083747)
                  ·
                    refine ⟨700557403670205876125621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 467038269113470584083747 700557403670205876125621)
                    ·
                      refine ⟨65677256594081800886777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 700557403670205876125621 65677256594081800886777)
                      ·
                        rfl

theorem cell23_127906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_127906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127906 prefixEnd_127906 := by exact prefixLift 127906
  have htrace : WordTrace (prefixWord ++ tailWord_127906) baseStart_127906 baseEnd_127906 := by
    simpa [prefixWord, tailWord_127906, baseEnd_127906] using wordTrace_append hprefix tailTrace_127906
  have hstable : (prefixWord ++ tailWord_127906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127906).length < 2 ^ (prefixWord ++ tailWord_127906).sum := by decide
  have hdescent : baseEnd_127906 < baseStart_127906 := by decide
  rcases family_descends (prefixWord ++ tailWord_127906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127919 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 3]
def baseStart_127919 : Nat := 118140960795 + 127919 * 2 ^ 59
def prefixEnd_127919 : Nat := 4983230072969 + 3 ^ 40 * 127919 * 2
def baseEnd_127919 : Nat := 65683931842590250024217

theorem tailTrace_127919 : CollatzResearch.WordTrace tailWord_127919 prefixEnd_127919 65683931842590250024217 := by
  unfold tailWord_127919
  simp only [CollatzResearch.WordTrace]
  refine ⟨4665589223578784670994811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3110392815719189780663207 4665589223578784670994811)
  ·
    refine ⟨6998383835368177006492217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4665589223578784670994811 6998383835368177006492217)
    ·
      refine ⟨5248787876526132754869163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6998383835368177006492217 5248787876526132754869163)
      ·
        refine ⟨7873181814789199132303745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5248787876526132754869163 7873181814789199132303745)
        ·
          refine ⟨5904886361091899349227809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7873181814789199132303745 5904886361091899349227809)
          ·
            refine ⟨4428664770818924511920857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5904886361091899349227809 4428664770818924511920857)
            ·
              refine ⟨3321498578114193383940643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4428664770818924511920857 3321498578114193383940643)
              ·
                refine ⟨4982247867171290075910965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3321498578114193383940643 4982247867171290075910965)
                ·
                  refine ⟨467085737547308444616653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4982247867171290075910965 467085737547308444616653)
                  ·
                    refine ⟨175157151580240666731245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 467085737547308444616653 175157151580240666731245)
                    ·
                      refine ⟨65683931842590250024217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 175157151580240666731245 65683931842590250024217)
                      ·
                        rfl

theorem cell23_127919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 3].length) (baseStart_127919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127919 prefixEnd_127919 := by exact prefixLift 127919
  have htrace : WordTrace (prefixWord ++ tailWord_127919) baseStart_127919 baseEnd_127919 := by
    simpa [prefixWord, tailWord_127919, baseEnd_127919] using wordTrace_append hprefix tailTrace_127919
  have hstable : (prefixWord ++ tailWord_127919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127919).length < 2 ^ (prefixWord ++ tailWord_127919).sum := by decide
  have hdescent : baseEnd_127919 < baseStart_127919 := by decide
  rcases family_descends (prefixWord ++ tailWord_127919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127940 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_127940 : Nat := 118140960795 + 127940 * 2 ^ 59
def prefixEnd_127940 : Nat := 4983230072969 + 3 ^ 40 * 127940 * 2
def baseEnd_127940 : Nat := 65694714936334667861621

theorem tailTrace_127940 : CollatzResearch.WordTrace tailWord_127940 prefixEnd_127940 65694714936334667861621 := by
  unfold tailWord_127940
  simp only [CollatzResearch.WordTrace]
  refine ⟨2333177578251352628754637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3110903437668470171672849 2333177578251352628754637)
  ·
    refine ⟨874941591844257235782989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2333177578251352628754637 874941591844257235782989)
    ·
      refine ⟨328103096941596463418621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 874941591844257235782989 328103096941596463418621)
      ·
        refine ⟨123038661353098673781983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328103096941596463418621 123038661353098673781983)
        ·
          refine ⟨184557992029648010672975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123038661353098673781983 184557992029648010672975)
          ·
            refine ⟨276836988044472016009463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184557992029648010672975 276836988044472016009463)
            ·
              refine ⟨415255482066708024014195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276836988044472016009463 415255482066708024014195)
              ·
                refine ⟨622883223100062036021293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415255482066708024014195 622883223100062036021293)
                ·
                  refine ⟨233581208662523263507985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 622883223100062036021293 233581208662523263507985)
                  ·
                    refine ⟨175185906496892447630989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 233581208662523263507985 175185906496892447630989)
                    ·
                      refine ⟨65694714936334667861621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 175185906496892447630989 65694714936334667861621)
                      ·
                        rfl

theorem cell23_127940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_127940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127940 prefixEnd_127940 := by exact prefixLift 127940
  have htrace : WordTrace (prefixWord ++ tailWord_127940) baseStart_127940 baseEnd_127940 := by
    simpa [prefixWord, tailWord_127940, baseEnd_127940] using wordTrace_append hprefix tailTrace_127940
  have hstable : (prefixWord ++ tailWord_127940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127940).length < 2 ^ (prefixWord ++ tailWord_127940).sum := by decide
  have hdescent : baseEnd_127940 < baseStart_127940 := by decide
  rcases family_descends (prefixWord ++ tailWord_127940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127969 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 2, 6]
def baseStart_127969 : Nat := 118140960795 + 127969 * 2 ^ 59
def prefixEnd_127969 : Nat := 4983230072969 + 3 ^ 40 * 127969 * 2
def baseEnd_127969 : Nat := 21903201958438351466329

theorem tailTrace_127969 : CollatzResearch.WordTrace tailWord_127969 prefixEnd_127969 21903201958438351466329 := by
  unfold tailWord_127969
  simp only [CollatzResearch.WordTrace]
  refine ⟨4667412873397643210314961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3111608582265095473543307 4667412873397643210314961)
  ·
    refine ⟨3500559655048232407736221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4667412873397643210314961 3500559655048232407736221)
    ·
      refine ⟨1312709870643087152901083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3500559655048232407736221 1312709870643087152901083)
      ·
        refine ⟨1969064805964630729351625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1312709870643087152901083 1969064805964630729351625)
        ·
          refine ⟨1476798604473473047013719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1969064805964630729351625 1476798604473473047013719)
          ·
            refine ⟨2215197906710209570520579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476798604473473047013719 2215197906710209570520579)
            ·
              refine ⟨3322796860065314355780869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2215197906710209570520579 3322796860065314355780869)
              ·
                refine ⟨623024411262246441708913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3322796860065314355780869 623024411262246441708913)
                ·
                  refine ⟨467268308446684831281685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 623024411262246441708913 467268308446684831281685)
                  ·
                    refine ⟨21903201958438351466329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 467268308446684831281685 21903201958438351466329)
                    ·
                      rfl

theorem cell23_127969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_127969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127969 prefixEnd_127969 := by exact prefixLift 127969
  have htrace : WordTrace (prefixWord ++ tailWord_127969) baseStart_127969 baseEnd_127969 := by
    simpa [prefixWord, tailWord_127969, baseEnd_127969] using wordTrace_append hprefix tailTrace_127969
  have hstable : (prefixWord ++ tailWord_127969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127969).length < 2 ^ (prefixWord ++ tailWord_127969).sum := by decide
  have hdescent : baseEnd_127969 < baseStart_127969 := by decide
  rcases family_descends (prefixWord ++ tailWord_127969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_127993 : List Nat := [1, 2, 1, 3, 1, 3, 4, 1, 1, 4, 2]
def baseStart_127993 : Nat := 118140960795 + 127993 * 2 ^ 59
def prefixEnd_127993 : Nat := 4983230072969 + 3 ^ 40 * 127993 * 2
def baseEnd_127993 : Nat := 65721929411022960498877

theorem tailTrace_127993 : CollatzResearch.WordTrace tailWord_127993 prefixEnd_127993 65721929411022960498877 := by
  unfold tailWord_127993
  simp only [CollatzResearch.WordTrace]
  refine ⟨4668288225310695309188633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3112192150207130206125755 4668288225310695309188633)
  ·
    refine ⟨3501216168983021481891475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4668288225310695309188633 3501216168983021481891475)
    ·
      refine ⟨5251824253474532222837213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3501216168983021481891475 5251824253474532222837213)
      ·
        refine ⟨1969434095052949583563955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5251824253474532222837213 1969434095052949583563955)
        ·
          refine ⟨2954151142579424375345933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1969434095052949583563955 2954151142579424375345933)
          ·
            refine ⟨1107806678467284140754725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2954151142579424375345933 1107806678467284140754725)
            ·
              refine ⟨207713752212615776391511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1107806678467284140754725 207713752212615776391511)
              ·
                refine ⟨311570628318923664587267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207713752212615776391511 311570628318923664587267)
                ·
                  refine ⟨467355942478385496880901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311570628318923664587267 467355942478385496880901)
                  ·
                    refine ⟨87629239214697280665169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 467355942478385496880901 87629239214697280665169)
                    ·
                      refine ⟨65721929411022960498877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 87629239214697280665169 65721929411022960498877)
                      ·
                        rfl

theorem cell23_127993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_127993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_127993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_127993 prefixEnd_127993 := by exact prefixLift 127993
  have htrace : WordTrace (prefixWord ++ tailWord_127993) baseStart_127993 baseEnd_127993 := by
    simpa [prefixWord, tailWord_127993, baseEnd_127993] using wordTrace_append hprefix tailTrace_127993
  have hstable : (prefixWord ++ tailWord_127993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_127993).length < 2 ^ (prefixWord ++ tailWord_127993).sum := by decide
  have hdescent : baseEnd_127993 < baseStart_127993 := by decide
  rcases family_descends (prefixWord ++ tailWord_127993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128026 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3]
def baseStart_128026 : Nat := 118140960795 + 128026 * 2 ^ 59
def prefixEnd_128026 : Nat := 4983230072969 + 3 ^ 40 * 128026 * 2
def baseEnd_128026 : Nat := 65738874272621331386225

theorem tailTrace_128026 : CollatzResearch.WordTrace tailWord_128026 prefixEnd_128026 65738874272621331386225 := by
  unfold tailWord_128026
  simp only [CollatzResearch.WordTrace]
  refine ⟨1167372958547785486284983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3112994556127427963426621 1167372958547785486284983)
  ·
    refine ⟨1751059437821678229427475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1167372958547785486284983 1751059437821678229427475)
    ·
      refine ⟨2626589156732517344141213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1751059437821678229427475 2626589156732517344141213)
      ·
        refine ⟨984970933774694004052955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2626589156732517344141213 984970933774694004052955)
        ·
          refine ⟨1477456400662041006079433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 984970933774694004052955 1477456400662041006079433)
          ·
            refine ⟨1108092300496530754559575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1477456400662041006079433 1108092300496530754559575)
            ·
              refine ⟨1662138450744796131839363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108092300496530754559575 1662138450744796131839363)
              ·
                refine ⟨2493207676117194197759045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662138450744796131839363 2493207676117194197759045)
                ·
                  refine ⟨467476439271973912079821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2493207676117194197759045 467476439271973912079821)
                  ·
                    refine ⟨175303664726990217029933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 467476439271973912079821 175303664726990217029933)
                    ·
                      refine ⟨65738874272621331386225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 175303664726990217029933 65738874272621331386225)
                      ·
                        rfl

theorem cell23_128026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_128026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128026 prefixEnd_128026 := by exact prefixLift 128026
  have htrace : WordTrace (prefixWord ++ tailWord_128026) baseStart_128026 baseEnd_128026 := by
    simpa [prefixWord, tailWord_128026, baseEnd_128026] using wordTrace_append hprefix tailTrace_128026
  have hstable : (prefixWord ++ tailWord_128026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128026).length < 2 ^ (prefixWord ++ tailWord_128026).sum := by decide
  have hdescent : baseEnd_128026 < baseStart_128026 := by decide
  rcases family_descends (prefixWord ++ tailWord_128026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128033 : List Nat := [1, 2, 3, 2, 3, 1, 2, 4, 5]
def baseStart_128033 : Nat := 118140960795 + 128033 * 2 ^ 59
def prefixEnd_128033 : Nat := 4983230072969 + 3 ^ 40 * 128033 * 2
def baseEnd_128033 : Nat := 7304718737466978222077

theorem tailTrace_128033 : CollatzResearch.WordTrace tailWord_128033 prefixEnd_128033 7304718737466978222077 := by
  unfold tailWord_128033
  simp only [CollatzResearch.WordTrace]
  refine ⟨4669747145165782140644753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3113164763443854760429835 4669747145165782140644753)
  ·
    refine ⟨3502310358874336605483565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4669747145165782140644753 3502310358874336605483565)
    ·
      refine ⟨1313366384577876227056337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3502310358874336605483565 1313366384577876227056337)
      ·
        refine ⟨985024788433407170292253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1313366384577876227056337 985024788433407170292253)
        ·
          refine ⟨369384295662527688859595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 985024788433407170292253 369384295662527688859595)
          ·
            refine ⟨554076443493791533289393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369384295662527688859595 554076443493791533289393)
            ·
              refine ⟨415557332620343649967045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554076443493791533289393 415557332620343649967045)
              ·
                refine ⟨77916999866314434368821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 415557332620343649967045 77916999866314434368821)
                ·
                  refine ⟨7304718737466978222077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77916999866314434368821 7304718737466978222077)
                  ·
                    rfl

theorem cell23_128033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 5].length) (baseStart_128033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128033 prefixEnd_128033 := by exact prefixLift 128033
  have htrace : WordTrace (prefixWord ++ tailWord_128033) baseStart_128033 baseEnd_128033 := by
    simpa [prefixWord, tailWord_128033, baseEnd_128033] using wordTrace_append hprefix tailTrace_128033
  have hstable : (prefixWord ++ tailWord_128033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128033).length < 2 ^ (prefixWord ++ tailWord_128033).sum := by decide
  have hdescent : baseEnd_128033 < baseStart_128033 := by decide
  rcases family_descends (prefixWord ++ tailWord_128033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128046 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 3, 7]
def baseStart_128046 : Nat := 118140960795 + 128046 * 2 ^ 59
def prefixEnd_128046 : Nat := 4983230072969 + 3 ^ 40 * 128046 * 2
def baseEnd_128046 : Nat := 21916381295237084378711

theorem tailTrace_128046 : CollatzResearch.WordTrace tailWord_128046 prefixEnd_128046 21916381295237084378711 := by
  unfold tailWord_128046
  simp only [CollatzResearch.WordTrace]
  refine ⟨583777661764835670108499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3113480862745790240578661 583777661764835670108499)
  ·
    refine ⟨875666492647253505162749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 583777661764835670108499 875666492647253505162749)
    ·
      refine ⟨328374934742720064436031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 875666492647253505162749 328374934742720064436031)
      ·
        refine ⟨492562402114080096654047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328374934742720064436031 492562402114080096654047)
        ·
          refine ⟨738843603171120144981071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492562402114080096654047 738843603171120144981071)
          ·
            refine ⟨1108265404756680217471607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738843603171120144981071 1108265404756680217471607)
            ·
              refine ⟨1662398107135020326207411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108265404756680217471607 1662398107135020326207411)
              ·
                refine ⟨2493597160702530489311117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662398107135020326207411 2493597160702530489311117)
                ·
                  refine ⟨935098935263448933491669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2493597160702530489311117 935098935263448933491669)
                  ·
                    refine ⟨21916381295237084378711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 935098935263448933491669 21916381295237084378711)
                    ·
                      rfl

theorem cell23_128046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_128046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128046 prefixEnd_128046 := by exact prefixLift 128046
  have htrace : WordTrace (prefixWord ++ tailWord_128046) baseStart_128046 baseEnd_128046 := by
    simpa [prefixWord, tailWord_128046, baseEnd_128046] using wordTrace_append hprefix tailTrace_128046
  have hstable : (prefixWord ++ tailWord_128046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128046).length < 2 ^ (prefixWord ++ tailWord_128046).sum := by decide
  have hdescent : baseEnd_128046 < baseStart_128046 := by decide
  rcases family_descends (prefixWord ++ tailWord_128046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128117 : List Nat := [1, 3, 4, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_128117 : Nat := 118140960795 + 128117 * 2 ^ 59
def prefixEnd_128117 : Nat := 4983230072969 + 3 ^ 40 * 128117 * 2
def baseEnd_128117 : Nat := 65785601012180475348307

theorem tailTrace_128117 : CollatzResearch.WordTrace tailWord_128117 prefixEnd_128117 65785601012180475348307 := by
  unfold tailWord_128117
  simp only [CollatzResearch.WordTrace]
  refine ⟨4672810876861464486702605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3115207251240976324468403 4672810876861464486702605)
  ·
    refine ⟨1752304078823049182513477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4672810876861464486702605 1752304078823049182513477)
    ·
      refine ⟨328557014779321721721277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1752304078823049182513477 328557014779321721721277)
      ·
        refine ⟨123208880542245645645479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 328557014779321721721277 123208880542245645645479)
        ·
          refine ⟨184813320813368468468219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123208880542245645645479 184813320813368468468219)
          ·
            refine ⟨277219981220052702702329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184813320813368468468219 277219981220052702702329)
            ·
              refine ⟨207914985915039527026747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277219981220052702702329 207914985915039527026747)
              ·
                refine ⟨311872478872559290540121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207914985915039527026747 311872478872559290540121)
                ·
                  refine ⟨233904359154419467905091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311872478872559290540121 233904359154419467905091)
                  ·
                    refine ⟨350856538731629201857637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 233904359154419467905091 350856538731629201857637)
                    ·
                      refine ⟨65785601012180475348307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 350856538731629201857637 65785601012180475348307)
                      ·
                        rfl

theorem cell23_128117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_128117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128117 prefixEnd_128117 := by exact prefixLift 128117
  have htrace : WordTrace (prefixWord ++ tailWord_128117) baseStart_128117 baseEnd_128117 := by
    simpa [prefixWord, tailWord_128117, baseEnd_128117] using wordTrace_append hprefix tailTrace_128117
  have hstable : (prefixWord ++ tailWord_128117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128117).length < 2 ^ (prefixWord ++ tailWord_128117).sum := by decide
  have hdescent : baseEnd_128117 < baseStart_128117 := by decide
  rcases family_descends (prefixWord ++ tailWord_128117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128143 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 8, 3, 2]
def baseStart_128143 : Nat := 118140960795 + 128143 * 2 ^ 59
def prefixEnd_128143 : Nat := 4983230072969 + 3 ^ 40 * 128143 * 2
def baseEnd_128143 : Nat := 65798951509197373623187

theorem tailTrace_128143 : CollatzResearch.WordTrace tailWord_128143 prefixEnd_128143 65798951509197373623187 := by
  unfold tailWord_128143
  simp only [CollatzResearch.WordTrace]
  refine ⟨4673759174767270927149083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3115839449844847284766055 4673759174767270927149083)
  ·
    refine ⟨7010638762150906390723625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4673759174767270927149083 7010638762150906390723625)
    ·
      refine ⟨5257979071613179793042719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7010638762150906390723625 5257979071613179793042719)
      ·
        refine ⟨7886968607419769689564079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5257979071613179793042719 7886968607419769689564079)
        ·
          refine ⟨11830452911129654534346119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7886968607419769689564079 11830452911129654534346119)
          ·
            refine ⟨17745679366694481801519179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11830452911129654534346119 17745679366694481801519179)
            ·
              refine ⟨26618519050041722702278769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17745679366694481801519179 26618519050041722702278769)
              ·
                refine ⟨19963889287531292026709077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26618519050041722702278769 19963889287531292026709077)
                ·
                  refine ⟨233951827588257328437997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19963889287531292026709077 233951827588257328437997)
                  ·
                    refine ⟨87731935345596498164249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 233951827588257328437997 87731935345596498164249)
                    ·
                      refine ⟨65798951509197373623187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 87731935345596498164249 65798951509197373623187)
                      ·
                        rfl

theorem cell23_128143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 3, 2].length) (baseStart_128143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128143 prefixEnd_128143 := by exact prefixLift 128143
  have htrace : WordTrace (prefixWord ++ tailWord_128143) baseStart_128143 baseEnd_128143 := by
    simpa [prefixWord, tailWord_128143, baseEnd_128143] using wordTrace_append hprefix tailTrace_128143
  have hstable : (prefixWord ++ tailWord_128143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128143).length < 2 ^ (prefixWord ++ tailWord_128143).sum := by decide
  have hdescent : baseEnd_128143 < baseStart_128143 := by decide
  rcases family_descends (prefixWord ++ tailWord_128143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128167 : List Nat := [1, 1, 6, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_128167 : Nat := 118140960795 + 128167 * 2 ^ 59
def prefixEnd_128167 : Nat := 4983230072969 + 3 ^ 40 * 128167 * 2
def baseEnd_128167 : Nat := 65811275044905279723077

theorem tailTrace_128167 : CollatzResearch.WordTrace tailWord_128167 prefixEnd_128167 65811275044905279723077 := by
  unfold tailWord_128167
  simp only [CollatzResearch.WordTrace]
  refine ⟨4674634526680323026022755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3116423017786882017348503 4674634526680323026022755)
  ·
    refine ⟨7011951790020484539034133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4674634526680323026022755 7011951790020484539034133)
    ·
      refine ⟨328685240157210212767225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7011951790020484539034133 328685240157210212767225)
      ·
        refine ⟨246513930117907659575419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 328685240157210212767225 246513930117907659575419)
        ·
          refine ⟨369770895176861489363129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246513930117907659575419 369770895176861489363129)
          ·
            refine ⟨277328171382646117022347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369770895176861489363129 277328171382646117022347)
            ·
              refine ⟨415992257073969175533521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277328171382646117022347 415992257073969175533521)
              ·
                refine ⟨311994192805476881650141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415992257073969175533521 311994192805476881650141)
                ·
                  refine ⟨116997822302053830618803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 311994192805476881650141 116997822302053830618803)
                  ·
                    refine ⟨175496733453080745928205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116997822302053830618803 175496733453080745928205)
                    ·
                      refine ⟨65811275044905279723077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 175496733453080745928205 65811275044905279723077)
                      ·
                        rfl

theorem cell23_128167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_128167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128167 prefixEnd_128167 := by exact prefixLift 128167
  have htrace : WordTrace (prefixWord ++ tailWord_128167) baseStart_128167 baseEnd_128167 := by
    simpa [prefixWord, tailWord_128167, baseEnd_128167] using wordTrace_append hprefix tailTrace_128167
  have hstable : (prefixWord ++ tailWord_128167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128167).length < 2 ^ (prefixWord ++ tailWord_128167).sum := by decide
  have hdescent : baseEnd_128167 < baseStart_128167 := by decide
  rcases family_descends (prefixWord ++ tailWord_128167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128170 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 3, 5]
def baseStart_128170 : Nat := 118140960795 + 128170 * 2 ^ 59
def prefixEnd_128170 : Nat := 4983230072969 + 3 ^ 40 * 128170 * 2
def baseEnd_128170 : Nat := 21937605162289589328521

theorem tailTrace_128170 : CollatzResearch.WordTrace tailWord_128170 prefixEnd_128170 21937605162289589328521 := by
  unfold tailWord_128170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1168685986417363634595491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3116495963779636358921309 1168685986417363634595491)
  ·
    refine ⟨1753028979626045451893237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1168685986417363634595491 1753028979626045451893237)
    ·
      refine ⟨164346466839941761114991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1753028979626045451893237 164346466839941761114991)
      ·
        refine ⟨246519700259912641672487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164346466839941761114991 246519700259912641672487)
        ·
          refine ⟨369779550389868962508731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246519700259912641672487 369779550389868962508731)
          ·
            refine ⟨554669325584803443763097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369779550389868962508731 554669325584803443763097)
            ·
              refine ⟨416001994188602582822323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554669325584803443763097 416001994188602582822323)
              ·
                refine ⟨624002991282903874233485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416001994188602582822323 624002991282903874233485)
                ·
                  refine ⟨234001121731088952837557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 624002991282903874233485 234001121731088952837557)
                  ·
                    refine ⟨21937605162289589328521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 234001121731088952837557 21937605162289589328521)
                    ·
                      rfl

theorem cell23_128170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_128170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128170 prefixEnd_128170 := by exact prefixLift 128170
  have htrace : WordTrace (prefixWord ++ tailWord_128170) baseStart_128170 baseEnd_128170 := by
    simpa [prefixWord, tailWord_128170, baseEnd_128170] using wordTrace_append hprefix tailTrace_128170
  have hstable : (prefixWord ++ tailWord_128170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128170).length < 2 ^ (prefixWord ++ tailWord_128170).sum := by decide
  have hdescent : baseEnd_128170 < baseStart_128170 := by decide
  rcases family_descends (prefixWord ++ tailWord_128170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128176 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 5]
def baseStart_128176 : Nat := 118140960795 + 128176 * 2 ^ 59
def prefixEnd_128176 : Nat := 4983230072969 + 3 ^ 40 * 128176 * 2
def baseEnd_128176 : Nat := 65815896370795744510535

theorem tailTrace_128176 : CollatzResearch.WordTrace tailWord_128176 prefixEnd_128176 65815896370795744510535 := by
  unfold tailWord_128176
  simp only [CollatzResearch.WordTrace]
  refine ⟨2337481391823858781550191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3116641855765145042066921 2337481391823858781550191)
  ·
    refine ⟨3506222087735788172325287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2337481391823858781550191 3506222087735788172325287)
    ·
      refine ⟨5259333131603682258487931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3506222087735788172325287 5259333131603682258487931)
      ·
        refine ⟨7888999697405523387731897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5259333131603682258487931 7888999697405523387731897)
        ·
          refine ⟨5916749773054142540798923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7888999697405523387731897 5916749773054142540798923)
          ·
            refine ⟨8875124659581213811198385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5916749773054142540798923 8875124659581213811198385)
            ·
              refine ⟨6656343494685910358398789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8875124659581213811198385 6656343494685910358398789)
              ·
                refine ⟨1248064405253608192199773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6656343494685910358398789 1248064405253608192199773)
                ·
                  refine ⟨468024151970103072074915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1248064405253608192199773 468024151970103072074915)
                  ·
                    refine ⟨702036227955154608112373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 468024151970103072074915 702036227955154608112373)
                    ·
                      refine ⟨65815896370795744510535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 702036227955154608112373 65815896370795744510535)
                      ·
                        rfl

theorem cell23_128176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_128176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128176 prefixEnd_128176 := by exact prefixLift 128176
  have htrace : WordTrace (prefixWord ++ tailWord_128176) baseStart_128176 baseEnd_128176 := by
    simpa [prefixWord, tailWord_128176, baseEnd_128176] using wordTrace_append hprefix tailTrace_128176
  have hstable : (prefixWord ++ tailWord_128176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128176).length < 2 ^ (prefixWord ++ tailWord_128176).sum := by decide
  have hdescent : baseEnd_128176 < baseStart_128176 := by decide
  rcases family_descends (prefixWord ++ tailWord_128176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128177 : List Nat := [1, 2, 2, 5, 1, 1, 3, 1, 2, 3, 2]
def baseStart_128177 : Nat := 118140960795 + 128177 * 2 ^ 59
def prefixEnd_128177 : Nat := 4983230072969 + 3 ^ 40 * 128177 * 2
def baseEnd_128177 : Nat := 65816409851450240598031

theorem tailTrace_128177 : CollatzResearch.WordTrace tailWord_128177 prefixEnd_128177 65816409851450240598031 := by
  unfold tailWord_128177
  simp only [CollatzResearch.WordTrace]
  refine ⟨4674999256644094733886785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3116666171096063155924523 4674999256644094733886785)
  ·
    refine ⟨3506249442483071050415089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4674999256644094733886785 3506249442483071050415089)
    ·
      refine ⟨2629687081862303287811317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3506249442483071050415089 2629687081862303287811317)
      ·
        refine ⟨246533163924590933232311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2629687081862303287811317 246533163924590933232311)
        ·
          refine ⟨369799745886886399848467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246533163924590933232311 369799745886886399848467)
          ·
            refine ⟨554699618830329599772701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369799745886886399848467 554699618830329599772701)
            ·
              refine ⟨208012357061373599914763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 554699618830329599772701 208012357061373599914763)
              ·
                refine ⟨312018535592060399872145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208012357061373599914763 312018535592060399872145)
                ·
                  refine ⟨234013901694045299904109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 312018535592060399872145 234013901694045299904109)
                  ·
                    refine ⟨87755213135266987464041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 234013901694045299904109 87755213135266987464041)
                    ·
                      refine ⟨65816409851450240598031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 87755213135266987464041 65816409851450240598031)
                      ·
                        rfl

theorem cell23_128177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_128177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128177 prefixEnd_128177 := by exact prefixLift 128177
  have htrace : WordTrace (prefixWord ++ tailWord_128177) baseStart_128177 baseEnd_128177 := by
    simpa [prefixWord, tailWord_128177, baseEnd_128177] using wordTrace_append hprefix tailTrace_128177
  have hstable : (prefixWord ++ tailWord_128177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128177).length < 2 ^ (prefixWord ++ tailWord_128177).sum := by decide
  have hdescent : baseEnd_128177 < baseStart_128177 := by decide
  rcases family_descends (prefixWord ++ tailWord_128177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128183 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 4, 4]
def baseStart_128183 : Nat := 118140960795 + 128183 * 2 ^ 59
def prefixEnd_128183 : Nat := 4983230072969 + 3 ^ 40 * 128183 * 2
def baseEnd_128183 : Nat := 21939830245125739041001

theorem tailTrace_128183 : CollatzResearch.WordTrace tailWord_128183 prefixEnd_128183 21939830245125739041001 := by
  unfold tailWord_128183
  simp only [CollatzResearch.WordTrace]
  refine ⟨4675218094622357758605203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3116812063081571839070135 4675218094622357758605203)
  ·
    refine ⟨7012827141933536637907805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4675218094622357758605203 7012827141933536637907805)
    ·
      refine ⟨2629810178225076239215427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7012827141933536637907805 2629810178225076239215427)
      ·
        refine ⟨3944715267337614358823141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2629810178225076239215427 3944715267337614358823141)
        ·
          refine ⟨739634112625802692279339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3944715267337614358823141 739634112625802692279339)
          ·
            refine ⟨1109451168938704038419009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 739634112625802692279339 1109451168938704038419009)
            ·
              refine ⟨832088376704028028814257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1109451168938704038419009 832088376704028028814257)
              ·
                refine ⟨624066282528021021610693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 832088376704028028814257 624066282528021021610693)
                ·
                  refine ⟨117012427974003941552005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 624066282528021021610693 117012427974003941552005)
                  ·
                    refine ⟨21939830245125739041001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117012427974003941552005 21939830245125739041001)
                    ·
                      rfl

theorem cell23_128183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_128183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128183 prefixEnd_128183 := by exact prefixLift 128183
  have htrace : WordTrace (prefixWord ++ tailWord_128183) baseStart_128183 baseEnd_128183 := by
    simpa [prefixWord, tailWord_128183, baseEnd_128183] using wordTrace_append hprefix tailTrace_128183
  have hstable : (prefixWord ++ tailWord_128183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128183).length < 2 ^ (prefixWord ++ tailWord_128183).sum := by decide
  have hdescent : baseEnd_128183 < baseStart_128183 := by decide
  rcases family_descends (prefixWord ++ tailWord_128183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128186 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6]
def baseStart_128186 : Nat := 118140960795 + 128186 * 2 ^ 59
def prefixEnd_128186 : Nat := 4983230072969 + 3 ^ 40 * 128186 * 2
def baseEnd_128186 : Nat := 65821031177340705385489

theorem tailTrace_128186 : CollatzResearch.WordTrace tailWord_128186 prefixEnd_128186 65821031177340705385489 := by
  unfold tailWord_128186
  simp only [CollatzResearch.WordTrace]
  refine ⟨1168831878402872317741103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3116885009074326180642941 1168831878402872317741103)
  ·
    refine ⟨1753247817604308476611655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1168831878402872317741103 1753247817604308476611655)
    ·
      refine ⟨2629871726406462714917483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1753247817604308476611655 2629871726406462714917483)
      ·
        refine ⟨3944807589609694072376225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2629871726406462714917483 3944807589609694072376225)
        ·
          refine ⟨2958605692207270554282169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3944807589609694072376225 2958605692207270554282169)
          ·
            refine ⟨2218954269155452915711627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2958605692207270554282169 2218954269155452915711627)
            ·
              refine ⟨3328431403733179373567441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2218954269155452915711627 3328431403733179373567441)
              ·
                refine ⟨2496323552799884530175581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3328431403733179373567441 2496323552799884530175581)
                ·
                  refine ⟨936121332299956698815843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2496323552799884530175581 936121332299956698815843)
                  ·
                    refine ⟨1404181998449935048223765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 936121332299956698815843 1404181998449935048223765)
                    ·
                      refine ⟨65821031177340705385489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1404181998449935048223765 65821031177340705385489)
                      ·
                        rfl

theorem cell23_128186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_128186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128186 prefixEnd_128186 := by exact prefixLift 128186
  have htrace : WordTrace (prefixWord ++ tailWord_128186) baseStart_128186 baseEnd_128186 := by
    simpa [prefixWord, tailWord_128186, baseEnd_128186] using wordTrace_append hprefix tailTrace_128186
  have hstable : (prefixWord ++ tailWord_128186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128186).length < 2 ^ (prefixWord ++ tailWord_128186).sum := by decide
  have hdescent : baseEnd_128186 < baseStart_128186 := by decide
  rcases family_descends (prefixWord ++ tailWord_128186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128200 : List Nat := [2, 1, 3, 1, 2, 1, 5, 2, 2, 4]
def baseStart_128200 : Nat := 118140960795 + 128200 * 2 ^ 59
def prefixEnd_128200 : Nat := 4983230072969 + 3 ^ 40 * 128200 * 2
def baseEnd_128200 : Nat := 21942739968834550203475

theorem tailTrace_128200 : CollatzResearch.WordTrace tailWord_128200 prefixEnd_128200 21942739968834550203475 := by
  unfold tailWord_128200
  simp only [CollatzResearch.WordTrace]
  refine ⟨2337919067780384830987027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3117225423707179774649369 2337919067780384830987027)
  ·
    refine ⟨3506878601670577246480541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2337919067780384830987027 3506878601670577246480541)
    ·
      refine ⟨1315079475626466467430203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3506878601670577246480541 1315079475626466467430203)
      ·
        refine ⟨1972619213439699701145305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1315079475626466467430203 1972619213439699701145305)
        ·
          refine ⟨1479464410079774775858979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1972619213439699701145305 1479464410079774775858979)
          ·
            refine ⟨2219196615119662163788469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479464410079774775858979 2219196615119662163788469)
            ·
              refine ⟨208049682667468327855169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2219196615119662163788469 208049682667468327855169)
              ·
                refine ⟨156037262000601245891377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208049682667468327855169 156037262000601245891377)
                ·
                  refine ⟨117027946500450934418533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156037262000601245891377 117027946500450934418533)
                  ·
                    refine ⟨21942739968834550203475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117027946500450934418533 21942739968834550203475)
                    ·
                      rfl

theorem cell23_128200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_128200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128200 prefixEnd_128200 := by exact prefixLift 128200
  have htrace : WordTrace (prefixWord ++ tailWord_128200) baseStart_128200 baseEnd_128200 := by
    simpa [prefixWord, tailWord_128200, baseEnd_128200] using wordTrace_append hprefix tailTrace_128200
  have hstable : (prefixWord ++ tailWord_128200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128200).length < 2 ^ (prefixWord ++ tailWord_128200).sum := by decide
  have hdescent : baseEnd_128200 < baseStart_128200 := by decide
  rcases family_descends (prefixWord ++ tailWord_128200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128258 : List Nat := [3, 4, 1, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_128258 : Nat := 118140960795 + 128258 * 2 ^ 59
def prefixEnd_128258 : Nat := 4983230072969 + 3 ^ 40 * 128258 * 2
def baseEnd_128258 : Nat := 65858001784464423685159

theorem tailTrace_128258 : CollatzResearch.WordTrace tailWord_128258 prefixEnd_128258 65858001784464423685159 := by
  unfold tailWord_128258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1169488392337661391896357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3118635712900430378390285 1169488392337661391896357)
  ·
    refine ⟨219279073563311510980567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1169488392337661391896357 219279073563311510980567)
    ·
      refine ⟨328918610344967266470851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219279073563311510980567 328918610344967266470851)
      ·
        refine ⟨493377915517450899706277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328918610344967266470851 493377915517450899706277)
        ·
          refine ⟨92508359159522043694927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 493377915517450899706277 92508359159522043694927)
          ·
            refine ⟨138762538739283065542391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92508359159522043694927 138762538739283065542391)
            ·
              refine ⟨208143808108924598313587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138762538739283065542391 208143808108924598313587)
              ·
                refine ⟨312215712163386897470381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208143808108924598313587 312215712163386897470381)
                ·
                  refine ⟨117080892061270086551393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 312215712163386897470381 117080892061270086551393)
                  ·
                    refine ⟨87810669045952564913545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117080892061270086551393 87810669045952564913545)
                    ·
                      refine ⟨65858001784464423685159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 87810669045952564913545 65858001784464423685159)
                      ·
                        rfl

theorem cell23_128258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_128258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128258 prefixEnd_128258 := by exact prefixLift 128258
  have htrace : WordTrace (prefixWord ++ tailWord_128258) baseStart_128258 baseEnd_128258 := by
    simpa [prefixWord, tailWord_128258, baseEnd_128258] using wordTrace_append hprefix tailTrace_128258
  have hstable : (prefixWord ++ tailWord_128258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128258).length < 2 ^ (prefixWord ++ tailWord_128258).sum := by decide
  have hdescent : baseEnd_128258 < baseStart_128258 := by decide
  rcases family_descends (prefixWord ++ tailWord_128258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128314 : List Nat := [3, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2]
def baseStart_128314 : Nat := 118140960795 + 128314 * 2 ^ 59
def prefixEnd_128314 : Nat := 4983230072969 + 3 ^ 40 * 128314 * 2
def baseEnd_128314 : Nat := 65886756701116204584901

theorem tailTrace_128314 : CollatzResearch.WordTrace tailWord_128314 prefixEnd_128314 65886756701116204584901 := by
  unfold tailWord_128314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1169999014286941782905999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3119997371431844754415997 1169999014286941782905999)
  ·
    refine ⟨1754998521430412674358999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1169999014286941782905999 1754998521430412674358999)
    ·
      refine ⟨2632497782145619011538499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1754998521430412674358999 2632497782145619011538499)
      ·
        refine ⟨3948746673218428517307749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2632497782145619011538499 3948746673218428517307749)
        ·
          refine ⟨740390001228455346995203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3948746673218428517307749 740390001228455346995203)
          ·
            refine ⟨1110585001842683020492805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740390001228455346995203 1110585001842683020492805)
            ·
              refine ⟨208234687845503066342401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1110585001842683020492805 208234687845503066342401)
              ·
                refine ⟨156176015884127299756801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208234687845503066342401 156176015884127299756801)
                ·
                  refine ⟨117132011913095474817601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156176015884127299756801 117132011913095474817601)
                  ·
                    refine ⟨87849008934821606113201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117132011913095474817601 87849008934821606113201)
                    ·
                      refine ⟨65886756701116204584901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 87849008934821606113201 65886756701116204584901)
                      ·
                        rfl

theorem cell23_128314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2].length) (baseStart_128314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128314 prefixEnd_128314 := by exact prefixLift 128314
  have htrace : WordTrace (prefixWord ++ tailWord_128314) baseStart_128314 baseEnd_128314 := by
    simpa [prefixWord, tailWord_128314, baseEnd_128314] using wordTrace_append hprefix tailTrace_128314
  have hstable : (prefixWord ++ tailWord_128314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128314).length < 2 ^ (prefixWord ++ tailWord_128314).sum := by decide
  have hdescent : baseEnd_128314 < baseStart_128314 := by decide
  rcases family_descends (prefixWord ++ tailWord_128314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128320 : List Nat := [2, 1, 1, 2, 2, 1, 5, 4, 5]
def baseStart_128320 : Nat := 118140960795 + 128320 * 2 ^ 59
def prefixEnd_128320 : Nat := 4983230072969 + 3 ^ 40 * 128320 * 2
def baseEnd_128320 : Nat := 7321093065004797901097

theorem tailTrace_128320 : CollatzResearch.WordTrace tailWord_128320 prefixEnd_128320 7321093065004797901097 := by
  unfold tailWord_128320
  simp only [CollatzResearch.WordTrace]
  refine ⟨2340107447563015078171207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3120143263417353437561609 2340107447563015078171207)
  ·
    refine ⟨3510161171344522617256811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2340107447563015078171207 3510161171344522617256811)
    ·
      refine ⟨5265241757016783925885217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3510161171344522617256811 5265241757016783925885217)
      ·
        refine ⟨3948931317762587944413913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5265241757016783925885217 3948931317762587944413913)
        ·
          refine ⟨2961698488321940958310435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3948931317762587944413913 2961698488321940958310435)
          ·
            refine ⟨4442547732482911437465653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2961698488321940958310435 4442547732482911437465653)
            ·
              refine ⟨416488849920272947262405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4442547732482911437465653 416488849920272947262405)
              ·
                refine ⟨78091659360051177611701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 416488849920272947262405 78091659360051177611701)
                ·
                  refine ⟨7321093065004797901097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78091659360051177611701 7321093065004797901097)
                  ·
                    rfl

theorem cell23_128320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 5].length) (baseStart_128320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128320 prefixEnd_128320 := by exact prefixLift 128320
  have htrace : WordTrace (prefixWord ++ tailWord_128320) baseStart_128320 baseEnd_128320 := by
    simpa [prefixWord, tailWord_128320, baseEnd_128320] using wordTrace_append hprefix tailTrace_128320
  have hstable : (prefixWord ++ tailWord_128320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128320).length < 2 ^ (prefixWord ++ tailWord_128320).sum := by decide
  have hdescent : baseEnd_128320 < baseStart_128320 := by decide
  rcases family_descends (prefixWord ++ tailWord_128320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128370 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_128370 : Nat := 118140960795 + 128370 * 2 ^ 59
def prefixEnd_128370 : Nat := 4983230072969 + 3 ^ 40 * 128370 * 2
def baseEnd_128370 : Nat := 65915511617767985484643

theorem tailTrace_128370 : CollatzResearch.WordTrace tailWord_128370 prefixEnd_128370 65915511617767985484643 := by
  unfold tailWord_128370
  simp only [CollatzResearch.WordTrace]
  refine ⟨1170509636236222173915641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3121359029963259130441709 1170509636236222173915641)
  ·
    refine ⟨877882227177166630436731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1170509636236222173915641 877882227177166630436731)
    ·
      refine ⟨1316823340765749945655097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 877882227177166630436731 1316823340765749945655097)
      ·
        refine ⟨987617505574312459241323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1316823340765749945655097 987617505574312459241323)
        ·
          refine ⟨1481426258361468688861985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987617505574312459241323 1481426258361468688861985)
          ·
            refine ⟨1111069693771101516646489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1481426258361468688861985 1111069693771101516646489)
            ·
              refine ⟨833302270328326137484867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1111069693771101516646489 833302270328326137484867)
              ·
                refine ⟨1249953405492489206227301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833302270328326137484867 1249953405492489206227301)
                ·
                  refine ⟨234366263529841726167619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1249953405492489206227301 234366263529841726167619)
                  ·
                    refine ⟨351549395294762589251429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 234366263529841726167619 351549395294762589251429)
                    ·
                      refine ⟨65915511617767985484643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 351549395294762589251429 65915511617767985484643)
                      ·
                        rfl

theorem cell23_128370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_128370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128370 prefixEnd_128370 := by exact prefixLift 128370
  have htrace : WordTrace (prefixWord ++ tailWord_128370) baseStart_128370 baseEnd_128370 := by
    simpa [prefixWord, tailWord_128370, baseEnd_128370] using wordTrace_append hprefix tailTrace_128370
  have hstable : (prefixWord ++ tailWord_128370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128370).length < 2 ^ (prefixWord ++ tailWord_128370).sum := by decide
  have hdescent : baseEnd_128370 < baseStart_128370 := by decide
  rcases family_descends (prefixWord ++ tailWord_128370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128383 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 4]
def baseStart_128383 : Nat := 118140960795 + 128383 * 2 ^ 59
def prefixEnd_128383 : Nat := 4983230072969 + 3 ^ 40 * 128383 * 2
def baseEnd_128383 : Nat := 65922186866276434622083

theorem tailTrace_128383 : CollatzResearch.WordTrace tailWord_128383 prefixEnd_128383 65922186866276434622083 := by
  unfold tailWord_128383
  simp only [CollatzResearch.WordTrace]
  refine ⟨4682512693897791915885803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3121675129265194610590535 4682512693897791915885803)
  ·
    refine ⟨7023769040846687873828705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4682512693897791915885803 7023769040846687873828705)
    ·
      refine ⟨5267826780635015905371529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7023769040846687873828705 5267826780635015905371529)
      ·
        refine ⟨3950870085476261929028647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5267826780635015905371529 3950870085476261929028647)
        ·
          refine ⟨5926305128214392893542971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3950870085476261929028647 5926305128214392893542971)
          ·
            refine ⟨8889457692321589340314457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5926305128214392893542971 8889457692321589340314457)
            ·
              refine ⟨6667093269241192005235843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8889457692321589340314457 6667093269241192005235843)
              ·
                refine ⟨10000639903861788007853765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6667093269241192005235843 10000639903861788007853765)
                ·
                  refine ⟨1875119981974085251472581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10000639903861788007853765 1875119981974085251472581)
                  ·
                    refine ⟨351584996620140984651109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1875119981974085251472581 351584996620140984651109)
                    ·
                      refine ⟨65922186866276434622083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 351584996620140984651109 65922186866276434622083)
                      ·
                        rfl

theorem cell23_128383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_128383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128383 prefixEnd_128383 := by exact prefixLift 128383
  have htrace : WordTrace (prefixWord ++ tailWord_128383) baseStart_128383 baseEnd_128383 := by
    simpa [prefixWord, tailWord_128383, baseEnd_128383] using wordTrace_append hprefix tailTrace_128383
  have hstable : (prefixWord ++ tailWord_128383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128383).length < 2 ^ (prefixWord ++ tailWord_128383).sum := by decide
  have hdescent : baseEnd_128383 < baseStart_128383 := by decide
  rcases family_descends (prefixWord ++ tailWord_128383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128387 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 2, 4, 2]
def baseStart_128387 : Nat := 118140960795 + 128387 * 2 ^ 59
def prefixEnd_128387 : Nat := 4983230072969 + 3 ^ 40 * 128387 * 2
def baseEnd_128387 : Nat := 65924240788894418972065

theorem tailTrace_128387 : CollatzResearch.WordTrace tailWord_128387 prefixEnd_128387 65924240788894418972065 := by
  unfold tailWord_128387
  simp only [CollatzResearch.WordTrace]
  refine ⟨4682658585883300599031415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3121772390588867066020943 4682658585883300599031415)
  ·
    refine ⟨7023987878824950898547123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4682658585883300599031415 7023987878824950898547123)
    ·
      refine ⟨10535981818237426347820685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7023987878824950898547123 10535981818237426347820685)
      ·
        refine ⟨3950993181839034880432757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10535981818237426347820685 3950993181839034880432757)
        ·
          refine ⟨370405610797409520040571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3950993181839034880432757 370405610797409520040571)
          ·
            refine ⟨555608416196114280060857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370405610797409520040571 555608416196114280060857)
            ·
              refine ⟨416706312147085710045643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 555608416196114280060857 416706312147085710045643)
              ·
                refine ⟨625059468220628565068465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416706312147085710045643 625059468220628565068465)
                ·
                  refine ⟨468794601165471423801349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625059468220628565068465 468794601165471423801349)
                  ·
                    refine ⟨87898987718525891962753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 468794601165471423801349 87898987718525891962753)
                    ·
                      refine ⟨65924240788894418972065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 87898987718525891962753 65924240788894418972065)
                      ·
                        rfl

theorem cell23_128387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 4, 2].length) (baseStart_128387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128387 prefixEnd_128387 := by exact prefixLift 128387
  have htrace : WordTrace (prefixWord ++ tailWord_128387) baseStart_128387 baseEnd_128387 := by
    simpa [prefixWord, tailWord_128387, baseEnd_128387] using wordTrace_append hprefix tailTrace_128387
  have hstable : (prefixWord ++ tailWord_128387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128387).length < 2 ^ (prefixWord ++ tailWord_128387).sum := by decide
  have hdescent : baseEnd_128387 < baseStart_128387 := by decide
  rcases family_descends (prefixWord ++ tailWord_128387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128474 : List Nat := [3, 1, 1, 2, 3, 3, 3, 1, 1, 5]
def baseStart_128474 : Nat := 118140960795 + 128474 * 2 ^ 59
def prefixEnd_128474 : Nat := 4983230072969 + 3 ^ 40 * 128474 * 2
def baseEnd_128474 : Nat := 21989637868611859528055

theorem tailTrace_128474 : CollatzResearch.WordTrace tailWord_128474 prefixEnd_128474 21989637868611859528055 := by
  unfold tailWord_128474
  simp only [CollatzResearch.WordTrace]
  refine ⟨1171457934142028614362119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3123887824378742971632317 1171457934142028614362119)
  ·
    refine ⟨1757186901213042921543179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1171457934142028614362119 1757186901213042921543179)
    ·
      refine ⟨2635780351819564382314769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1757186901213042921543179 2635780351819564382314769)
      ·
        refine ⟨1976835263864673286736077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2635780351819564382314769 1976835263864673286736077)
        ·
          refine ⟨741313223949252482526029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1976835263864673286736077 741313223949252482526029)
          ·
            refine ⟨277992458980969680947261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 741313223949252482526029 277992458980969680947261)
            ·
              refine ⟨104247172117863630355223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277992458980969680947261 104247172117863630355223)
              ·
                refine ⟨156370758176795445532835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104247172117863630355223 156370758176795445532835)
                ·
                  refine ⟨234556137265193168299253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156370758176795445532835 234556137265193168299253)
                  ·
                    refine ⟨21989637868611859528055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 234556137265193168299253 21989637868611859528055)
                    ·
                      rfl

theorem cell23_128474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 1, 5].length) (baseStart_128474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128474 prefixEnd_128474 := by exact prefixLift 128474
  have htrace : WordTrace (prefixWord ++ tailWord_128474) baseStart_128474 baseEnd_128474 := by
    simpa [prefixWord, tailWord_128474, baseEnd_128474] using wordTrace_append hprefix tailTrace_128474
  have hstable : (prefixWord ++ tailWord_128474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128474).length < 2 ^ (prefixWord ++ tailWord_128474).sum := by decide
  have hdescent : baseEnd_128474 < baseStart_128474 := by decide
  rcases family_descends (prefixWord ++ tailWord_128474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128480 : List Nat := [2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 5]
def baseStart_128480 : Nat := 118140960795 + 128480 * 2 ^ 59
def prefixEnd_128480 : Nat := 4983230072969 + 3 ^ 40 * 128480 * 2
def baseEnd_128480 : Nat := 65971994489762555109137

theorem tailTrace_128480 : CollatzResearch.WordTrace tailWord_128480 prefixEnd_128480 65971994489762555109137 := by
  unfold tailWord_128480
  simp only [CollatzResearch.WordTrace]
  refine ⟨2343025287273188741083447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3124033716364251654777929 2343025287273188741083447)
  ·
    refine ⟨3514537930909783111625171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2343025287273188741083447 3514537930909783111625171)
    ·
      refine ⟨5271806896364674667437757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3514537930909783111625171 5271806896364674667437757)
      ·
        refine ⟨1976927586136753000289159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5271806896364674667437757 1976927586136753000289159)
        ·
          refine ⟨2965391379205129500433739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1976927586136753000289159 2965391379205129500433739)
          ·
            refine ⟨4448087068807694250650609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965391379205129500433739 4448087068807694250650609)
            ·
              refine ⟨3336065301605770687987957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4448087068807694250650609 3336065301605770687987957)
              ·
                refine ⟨312756122025541001998871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3336065301605770687987957 312756122025541001998871)
                ·
                  refine ⟨469134183038311502998307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312756122025541001998871 469134183038311502998307)
                  ·
                    refine ⟨703701274557467254497461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 469134183038311502998307 703701274557467254497461)
                    ·
                      refine ⟨65971994489762555109137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 703701274557467254497461 65971994489762555109137)
                      ·
                        rfl

theorem cell23_128480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_128480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128480 prefixEnd_128480 := by exact prefixLift 128480
  have htrace : WordTrace (prefixWord ++ tailWord_128480) baseStart_128480 baseEnd_128480 := by
    simpa [prefixWord, tailWord_128480, baseEnd_128480] using wordTrace_append hprefix tailTrace_128480
  have hstable : (prefixWord ++ tailWord_128480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128480).length < 2 ^ (prefixWord ++ tailWord_128480).sum := by decide
  have hdescent : baseEnd_128480 < baseStart_128480 := by decide
  rcases family_descends (prefixWord ++ tailWord_128480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128497 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 3, 2, 3]
def baseStart_128497 : Nat := 118140960795 + 128497 * 2 ^ 59
def prefixEnd_128497 : Nat := 4983230072969 + 3 ^ 40 * 128497 * 2
def baseEnd_128497 : Nat := 65980723660888988596559

theorem tailTrace_128497 : CollatzResearch.WordTrace tailWord_128497 prefixEnd_128497 65980723660888988596559 := by
  unfold tailWord_128497
  simp only [CollatzResearch.WordTrace]
  refine ⟨4686670615484789385535745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3124447076989859590357163 4686670615484789385535745)
  ·
    refine ⟨3515002961613592039151809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4686670615484789385535745 3515002961613592039151809)
    ·
      refine ⟨2636252221210194029363857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3515002961613592039151809 2636252221210194029363857)
      ·
        refine ⟨1977189165907645522022893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2636252221210194029363857 1977189165907645522022893)
        ·
          refine ⟨741445937215367070758585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1977189165907645522022893 741445937215367070758585)
          ·
            refine ⟨556084452911525303068939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741445937215367070758585 556084452911525303068939)
            ·
              refine ⟨834126679367287954603409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556084452911525303068939 834126679367287954603409)
              ·
                refine ⟨625595009525465965952557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 834126679367287954603409 625595009525465965952557)
                ·
                  refine ⟨234598128572049737232209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 625595009525465965952557 234598128572049737232209)
                  ·
                    refine ⟨175948596429037302924157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 234598128572049737232209 175948596429037302924157)
                    ·
                      refine ⟨65980723660888988596559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 175948596429037302924157 65980723660888988596559)
                      ·
                        rfl

theorem cell23_128497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_128497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128497 prefixEnd_128497 := by exact prefixLift 128497
  have htrace : WordTrace (prefixWord ++ tailWord_128497) baseStart_128497 baseEnd_128497 := by
    simpa [prefixWord, tailWord_128497, baseEnd_128497] using wordTrace_append hprefix tailTrace_128497
  have hstable : (prefixWord ++ tailWord_128497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128497).length < 2 ^ (prefixWord ++ tailWord_128497).sum := by decide
  have hdescent : baseEnd_128497 < baseStart_128497 := by decide
  rcases family_descends (prefixWord ++ tailWord_128497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128525 : List Nat := [1, 7, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_128525 : Nat := 118140960795 + 128525 * 2 ^ 59
def prefixEnd_128525 : Nat := 4983230072969 + 3 ^ 40 * 128525 * 2
def baseEnd_128525 : Nat := 21998367039738293015477

theorem tailTrace_128525 : CollatzResearch.WordTrace tailWord_128525 prefixEnd_128525 21998367039738293015477 := by
  unfold tailWord_128525
  simp only [CollatzResearch.WordTrace]
  refine ⟨4687691859383350167555029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3125127906255566778370019 4687691859383350167555029)
  ·
    refine ⟨109867777954297269552071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 4687691859383350167555029 109867777954297269552071)
    ·
      refine ⟨164801666931445904328107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109867777954297269552071 164801666931445904328107)
      ·
        refine ⟨247202500397168856492161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164801666931445904328107 247202500397168856492161)
        ·
          refine ⟨185401875297876642369121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247202500397168856492161 185401875297876642369121)
          ·
            refine ⟨139051406473407481776841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185401875297876642369121 139051406473407481776841)
            ·
              refine ⟨104288554855055611332631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139051406473407481776841 104288554855055611332631)
              ·
                refine ⟨156432832282583416998947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104288554855055611332631 156432832282583416998947)
                ·
                  refine ⟨234649248423875125498421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156432832282583416998947 234649248423875125498421)
                  ·
                    refine ⟨21998367039738293015477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 234649248423875125498421 21998367039738293015477)
                    ·
                      rfl

theorem cell23_128525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_128525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128525 prefixEnd_128525 := by exact prefixLift 128525
  have htrace : WordTrace (prefixWord ++ tailWord_128525) baseStart_128525 baseEnd_128525 := by
    simpa [prefixWord, tailWord_128525, baseEnd_128525] using wordTrace_append hprefix tailTrace_128525
  have hstable : (prefixWord ++ tailWord_128525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128525).length < 2 ^ (prefixWord ++ tailWord_128525).sum := by decide
  have hdescent : baseEnd_128525 < baseStart_128525 := by decide
  rcases family_descends (prefixWord ++ tailWord_128525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128531 : List Nat := [1, 1, 1, 2, 1, 8, 2, 1, 1, 2, 3]
def baseStart_128531 : Nat := 118140960795 + 128531 * 2 ^ 59
def prefixEnd_128531 : Nat := 4983230072969 + 3 ^ 40 * 128531 * 2
def baseEnd_128531 : Nat := 65998182003141855571403

theorem tailTrace_128531 : CollatzResearch.WordTrace tailWord_128531 prefixEnd_128531 65998182003141855571403 := by
  unfold tailWord_128531
  simp only [CollatzResearch.WordTrace]
  refine ⟨4687910697361613192273447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3125273798241075461515631 4687910697361613192273447)
  ·
    refine ⟨7031866046042419788410171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4687910697361613192273447 7031866046042419788410171)
    ·
      refine ⟨10547799069063629682615257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7031866046042419788410171 10547799069063629682615257)
      ·
        refine ⟨7910849301797722261961443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10547799069063629682615257 7910849301797722261961443)
        ·
          refine ⟨11866273952696583392942165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7910849301797722261961443 11866273952696583392942165)
          ·
            refine ⟨139057897883163086636041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 11866273952696583392942165 139057897883163086636041)
            ·
              refine ⟨104293423412372314977031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139057897883163086636041 104293423412372314977031)
              ·
                refine ⟨156440135118558472465547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104293423412372314977031 156440135118558472465547)
                ·
                  refine ⟨234660202677837708698321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156440135118558472465547 234660202677837708698321)
                  ·
                    refine ⟨175995152008378281523741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 234660202677837708698321 175995152008378281523741)
                    ·
                      refine ⟨65998182003141855571403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 175995152008378281523741 65998182003141855571403)
                      ·
                        rfl

theorem cell23_128531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 1, 2, 3].length) (baseStart_128531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128531 prefixEnd_128531 := by exact prefixLift 128531
  have htrace : WordTrace (prefixWord ++ tailWord_128531) baseStart_128531 baseEnd_128531 := by
    simpa [prefixWord, tailWord_128531, baseEnd_128531] using wordTrace_append hprefix tailTrace_128531
  have hstable : (prefixWord ++ tailWord_128531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128531).length < 2 ^ (prefixWord ++ tailWord_128531).sum := by decide
  have hdescent : baseEnd_128531 < baseStart_128531 := by decide
  rcases family_descends (prefixWord ++ tailWord_128531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128600 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 1, 1, 9]
def baseStart_128600 : Nat := 118140960795 + 128600 * 2 ^ 59
def prefixEnd_128600 : Nat := 4983230072969 + 3 ^ 40 * 128600 * 2
def baseEnd_128600 : Nat := 66033612168302085608585

theorem tailTrace_128600 : CollatzResearch.WordTrace tailWord_128600 prefixEnd_128600 66033612168302085608585 := by
  unfold tailWord_128600
  simp only [CollatzResearch.WordTrace]
  refine ⟨2345213667055818988267627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3126951556074425317690169 2345213667055818988267627)
  ·
    refine ⟨3517820500583728482401441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2345213667055818988267627 3517820500583728482401441)
    ·
      refine ⟨2638365375437796361801081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3517820500583728482401441 2638365375437796361801081)
      ·
        refine ⟨1978774031578347271350811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2638365375437796361801081 1978774031578347271350811)
        ·
          refine ⟨2968161047367520907026217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1978774031578347271350811 2968161047367520907026217)
          ·
            refine ⟨2226120785525640680269663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2968161047367520907026217 2226120785525640680269663)
            ·
              refine ⟨3339181178288461020404495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2226120785525640680269663 3339181178288461020404495)
              ·
                refine ⟨5008771767432691530606743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3339181178288461020404495 5008771767432691530606743)
                ·
                  refine ⟨7513157651149037295910115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5008771767432691530606743 7513157651149037295910115)
                  ·
                    refine ⟨11269736476723555943865173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7513157651149037295910115 11269736476723555943865173)
                    ·
                      refine ⟨66033612168302085608585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 11269736476723555943865173 66033612168302085608585)
                      ·
                        rfl

theorem cell23_128600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_128600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128600 prefixEnd_128600 := by exact prefixLift 128600
  have htrace : WordTrace (prefixWord ++ tailWord_128600) baseStart_128600 baseEnd_128600 := by
    simpa [prefixWord, tailWord_128600, baseEnd_128600] using wordTrace_append hprefix tailTrace_128600
  have hstable : (prefixWord ++ tailWord_128600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128600).length < 2 ^ (prefixWord ++ tailWord_128600).sum := by decide
  have hdescent : baseEnd_128600 < baseStart_128600 := by decide
  rcases family_descends (prefixWord ++ tailWord_128600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128617 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 2, 3, 3]
def baseStart_128617 : Nat := 118140960795 + 128617 * 2 ^ 59
def prefixEnd_128617 : Nat := 4983230072969 + 3 ^ 40 * 128617 * 2
def baseEnd_128617 : Nat := 66042341339428519096007

theorem tailTrace_128617 : CollatzResearch.WordTrace tailWord_128617 prefixEnd_128617 66042341339428519096007 := by
  unfold tailWord_128617
  simp only [CollatzResearch.WordTrace]
  refine ⟨4691047375050049879904105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3127364916700033253269403 4691047375050049879904105)
  ·
    refine ⟨3518285531287537409928079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4691047375050049879904105 3518285531287537409928079)
    ·
      refine ⟨5277428296931306114892119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3518285531287537409928079 5277428296931306114892119)
      ·
        refine ⟨7916142445396959172338179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5277428296931306114892119 7916142445396959172338179)
        ·
          refine ⟨11874213668095438758507269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7916142445396959172338179 11874213668095438758507269)
          ·
            refine ⟨2226415062767894767220113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11874213668095438758507269 2226415062767894767220113)
            ·
              refine ⟨1669811297075921075415085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2226415062767894767220113 1669811297075921075415085)
              ·
                refine ⟨626179236403470403280657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1669811297075921075415085 626179236403470403280657)
                ·
                  refine ⟨469634427302602802460493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 626179236403470403280657 469634427302602802460493)
                  ·
                    refine ⟨176112910238476050922685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 469634427302602802460493 176112910238476050922685)
                    ·
                      refine ⟨66042341339428519096007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 176112910238476050922685 66042341339428519096007)
                      ·
                        rfl

theorem cell23_128617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 3, 3].length) (baseStart_128617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128617 prefixEnd_128617 := by exact prefixLift 128617
  have htrace : WordTrace (prefixWord ++ tailWord_128617) baseStart_128617 baseEnd_128617 := by
    simpa [prefixWord, tailWord_128617, baseEnd_128617] using wordTrace_append hprefix tailTrace_128617
  have hstable : (prefixWord ++ tailWord_128617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128617).length < 2 ^ (prefixWord ++ tailWord_128617).sum := by decide
  have hdescent : baseEnd_128617 < baseStart_128617 := by decide
  rcases family_descends (prefixWord ++ tailWord_128617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128618 : List Nat := [3, 1, 3, 2, 1, 3, 1, 3, 2, 2, 2]
def baseStart_128618 : Nat := 118140960795 + 128618 * 2 ^ 59
def prefixEnd_128618 : Nat := 4983230072969 + 3 ^ 40 * 128618 * 2
def baseEnd_128618 : Nat := 66042854820083015183503

theorem tailTrace_128618 : CollatzResearch.WordTrace tailWord_128618 prefixEnd_128618 66042854820083015183503 := by
  unfold tailWord_128618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1172770962011606762672627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3127389232030951367127005 1172770962011606762672627)
  ·
    refine ⟨1759156443017410144008941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1172770962011606762672627 1759156443017410144008941)
    ·
      refine ⟨659683666131528804003353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1759156443017410144008941 659683666131528804003353)
      ·
        refine ⟨494762749598646603002515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 659683666131528804003353 494762749598646603002515)
        ·
          refine ⟨742144124397969904503773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494762749598646603002515 742144124397969904503773)
          ·
            refine ⟨278304046649238714188915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 742144124397969904503773 278304046649238714188915)
            ·
              refine ⟨417456069973858071283373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278304046649238714188915 417456069973858071283373)
              ·
                refine ⟨156546026240196776731265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417456069973858071283373 156546026240196776731265)
                ·
                  refine ⟨117409519680147582548449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156546026240196776731265 117409519680147582548449)
                  ·
                    refine ⟨88057139760110686911337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117409519680147582548449 88057139760110686911337)
                    ·
                      refine ⟨66042854820083015183503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 88057139760110686911337 66042854820083015183503)
                      ·
                        rfl

theorem cell23_128618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_128618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128618 prefixEnd_128618 := by exact prefixLift 128618
  have htrace : WordTrace (prefixWord ++ tailWord_128618) baseStart_128618 baseEnd_128618 := by
    simpa [prefixWord, tailWord_128618, baseEnd_128618] using wordTrace_append hprefix tailTrace_128618
  have hstable : (prefixWord ++ tailWord_128618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128618).length < 2 ^ (prefixWord ++ tailWord_128618).sum := by decide
  have hdescent : baseEnd_128618 < baseStart_128618 := by decide
  rcases family_descends (prefixWord ++ tailWord_128618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128647 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_128647 : Nat := 118140960795 + 128647 * 2 ^ 59
def prefixEnd_128647 : Nat := 4983230072969 + 3 ^ 40 * 128647 * 2
def baseEnd_128647 : Nat := 66057745759063401720869

theorem tailTrace_128647 : CollatzResearch.WordTrace tailWord_128647 prefixEnd_128647 66057745759063401720869 := by
  unfold tailWord_128647
  simp only [CollatzResearch.WordTrace]
  refine ⟨4692141564941365003496195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3128094376627576668997463 4692141564941365003496195)
  ·
    refine ⟨7038212347412047505244293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4692141564941365003496195 7038212347412047505244293)
    ·
      refine ⟨1319664815139758907233305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7038212347412047505244293 1319664815139758907233305)
      ·
        refine ⟨989748611354819180424979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1319664815139758907233305 989748611354819180424979)
        ·
          refine ⟨1484622917032228770637469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989748611354819180424979 1484622917032228770637469)
          ·
            refine ⟨556733593887085788989051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1484622917032228770637469 556733593887085788989051)
            ·
              refine ⟨835100390830628683483577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556733593887085788989051 835100390830628683483577)
              ·
                refine ⟨626325293122971512612683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 835100390830628683483577 626325293122971512612683)
                ·
                  refine ⟨939487939684457268919025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 626325293122971512612683 939487939684457268919025)
                  ·
                    refine ⟨704615954763342951689269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 939487939684457268919025 704615954763342951689269)
                    ·
                      refine ⟨66057745759063401720869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 704615954763342951689269 66057745759063401720869)
                      ·
                        rfl

theorem cell23_128647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_128647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128647 prefixEnd_128647 := by exact prefixLift 128647
  have htrace : WordTrace (prefixWord ++ tailWord_128647) baseStart_128647 baseEnd_128647 := by
    simpa [prefixWord, tailWord_128647, baseEnd_128647] using wordTrace_append hprefix tailTrace_128647
  have hstable : (prefixWord ++ tailWord_128647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128647).length < 2 ^ (prefixWord ++ tailWord_128647).sum := by decide
  have hdescent : baseEnd_128647 < baseStart_128647 := by decide
  rcases family_descends (prefixWord ++ tailWord_128647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128654 : List Nat := [4, 1, 1, 3, 1, 2, 2, 2, 2, 5]
def baseStart_128654 : Nat := 118140960795 + 128654 * 2 ^ 59
def prefixEnd_128654 : Nat := 4983230072969 + 3 ^ 40 * 128654 * 2
def baseEnd_128654 : Nat := 22020446707881624777779

theorem tailTrace_128654 : CollatzResearch.WordTrace tailWord_128654 prefixEnd_128654 22020446707881624777779 := by
  unfold tailWord_128654
  simp only [CollatzResearch.WordTrace]
  refine ⟨586549609489500649875127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3128264583944003466000677 586549609489500649875127)
  ·
    refine ⟨879824414234250974812691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 586549609489500649875127 879824414234250974812691)
    ·
      refine ⟨1319736621351376462219037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 879824414234250974812691 1319736621351376462219037)
      ·
        refine ⟨494901233006766173332139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1319736621351376462219037 494901233006766173332139)
        ·
          refine ⟨742351849510149259998209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494901233006766173332139 742351849510149259998209)
          ·
            refine ⟨556763887132611944998657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742351849510149259998209 556763887132611944998657)
            ·
              refine ⟨417572915349458958748993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556763887132611944998657 417572915349458958748993)
              ·
                refine ⟨313179686512094219061745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417572915349458958748993 313179686512094219061745)
                ·
                  refine ⟨234884764884070664296309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313179686512094219061745 234884764884070664296309)
                  ·
                    refine ⟨22020446707881624777779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 234884764884070664296309 22020446707881624777779)
                    ·
                      rfl

theorem cell23_128654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_128654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128654 prefixEnd_128654 := by exact prefixLift 128654
  have htrace : WordTrace (prefixWord ++ tailWord_128654) baseStart_128654 baseEnd_128654 := by
    simpa [prefixWord, tailWord_128654, baseEnd_128654] using wordTrace_append hprefix tailTrace_128654
  have hstable : (prefixWord ++ tailWord_128654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128654).length < 2 ^ (prefixWord ++ tailWord_128654).sum := by decide
  have hdescent : baseEnd_128654 < baseStart_128654 := by decide
  rcases family_descends (prefixWord ++ tailWord_128654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128657 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 4]
def baseStart_128657 : Nat := 118140960795 + 128657 * 2 ^ 59
def prefixEnd_128657 : Nat := 4983230072969 + 3 ^ 40 * 128657 * 2
def baseEnd_128657 : Nat := 66062880565608362595823

theorem tailTrace_128657 : CollatzResearch.WordTrace tailWord_128657 prefixEnd_128657 66062880565608362595823 := by
  unfold tailWord_128657
  simp only [CollatzResearch.WordTrace]
  refine ⟨4692506294905136711360225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3128337529936757807573483 4692506294905136711360225)
  ·
    refine ⟨3519379721178852533520169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4692506294905136711360225 3519379721178852533520169)
    ·
      refine ⟨2639534790884139400140127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3519379721178852533520169 2639534790884139400140127)
      ·
        refine ⟨3959302186326209100210191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2639534790884139400140127 3959302186326209100210191)
        ·
          refine ⟨5938953279489313650315287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3959302186326209100210191 5938953279489313650315287)
          ·
            refine ⟨8908429919233970475472931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5938953279489313650315287 8908429919233970475472931)
            ·
              refine ⟨13362644878850955713209397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8908429919233970475472931 13362644878850955713209397)
              ·
                refine ⟨1252747957392277098113381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13362644878850955713209397 1252747957392277098113381)
                ·
                  refine ⟨234890242011051955896259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1252747957392277098113381 234890242011051955896259)
                  ·
                    refine ⟨352335363016577933844389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 234890242011051955896259 352335363016577933844389)
                    ·
                      refine ⟨66062880565608362595823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 352335363016577933844389 66062880565608362595823)
                      ·
                        rfl

theorem cell23_128657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_128657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128657 prefixEnd_128657 := by exact prefixLift 128657
  have htrace : WordTrace (prefixWord ++ tailWord_128657) baseStart_128657 baseEnd_128657 := by
    simpa [prefixWord, tailWord_128657, baseEnd_128657] using wordTrace_append hprefix tailTrace_128657
  have hstable : (prefixWord ++ tailWord_128657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128657).length < 2 ^ (prefixWord ++ tailWord_128657).sum := by decide
  have hdescent : baseEnd_128657 < baseStart_128657 := by decide
  rcases family_descends (prefixWord ++ tailWord_128657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128707 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 3]
def baseStart_128707 : Nat := 118140960795 + 128707 * 2 ^ 59
def prefixEnd_128707 : Nat := 4983230072969 + 3 ^ 40 * 128707 * 2
def baseEnd_128707 : Nat := 66088554598333166970593

theorem tailTrace_128707 : CollatzResearch.WordTrace tailWord_128707 prefixEnd_128707 66088554598333166970593 := by
  unfold tailWord_128707
  simp only [CollatzResearch.WordTrace]
  refine ⟨4694329944723995250680375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3129553296482663500453583 4694329944723995250680375)
  ·
    refine ⟨7041494917085992876020563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4694329944723995250680375 7041494917085992876020563)
    ·
      refine ⟨10562242375628989314030845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7041494917085992876020563 10562242375628989314030845)
      ·
        refine ⟨3960840890860870992761567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10562242375628989314030845 3960840890860870992761567)
        ·
          refine ⟨5941261336291306489142351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3960840890860870992761567 5941261336291306489142351)
          ·
            refine ⟨8911892004436959733713527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5941261336291306489142351 8911892004436959733713527)
            ·
              refine ⟨13367838006655439600570291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8911892004436959733713527 13367838006655439600570291)
              ·
                refine ⟨20051757009983159400855437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13367838006655439600570291 20051757009983159400855437)
                ·
                  refine ⟨7519408878743684775320789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20051757009983159400855437 7519408878743684775320789)
                  ·
                    refine ⟨176236145595555111921581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7519408878743684775320789 176236145595555111921581)
                    ·
                      refine ⟨66088554598333166970593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 176236145595555111921581 66088554598333166970593)
                      ·
                        rfl

theorem cell23_128707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_128707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128707 prefixEnd_128707 := by exact prefixLift 128707
  have htrace : WordTrace (prefixWord ++ tailWord_128707) baseStart_128707 baseEnd_128707 := by
    simpa [prefixWord, tailWord_128707, baseEnd_128707] using wordTrace_append hprefix tailTrace_128707
  have hstable : (prefixWord ++ tailWord_128707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128707).length < 2 ^ (prefixWord ++ tailWord_128707).sum := by decide
  have hdescent : baseEnd_128707 < baseStart_128707 := by decide
  rcases family_descends (prefixWord ++ tailWord_128707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128714 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 8]
def baseStart_128714 : Nat := 118140960795 + 128714 * 2 ^ 59
def prefixEnd_128714 : Nat := 4983230072969 + 3 ^ 40 * 128714 * 2
def baseEnd_128714 : Nat := 7343572106990515509229

theorem tailTrace_128714 : CollatzResearch.WordTrace tailWord_128714 prefixEnd_128714 7343572106990515509229 := by
  unfold tailWord_128714
  simp only [CollatzResearch.WordTrace]
  refine ⟨1173646313924658861546299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3129723503799090297456797 1173646313924658861546299)
  ·
    refine ⟨1760469470886988292319449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1173646313924658861546299 1760469470886988292319449)
    ·
      refine ⟨1320352103165241219239587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1760469470886988292319449 1320352103165241219239587)
      ·
        refine ⟨1980528154747861828859381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1320352103165241219239587 1980528154747861828859381)
        ·
          refine ⟨185674514507612046455567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1980528154747861828859381 185674514507612046455567)
          ·
            refine ⟨278511771761418069683351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185674514507612046455567 278511771761418069683351)
            ·
              refine ⟨417767657642127104525027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278511771761418069683351 417767657642127104525027)
              ·
                refine ⟨626651486463190656787541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417767657642127104525027 626651486463190656787541)
                ·
                  refine ⟨7343572106990515509229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 626651486463190656787541 7343572106990515509229)
                  ·
                    rfl

theorem cell23_128714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 8].length) (baseStart_128714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128714 prefixEnd_128714 := by exact prefixLift 128714
  have htrace : WordTrace (prefixWord ++ tailWord_128714) baseStart_128714 baseEnd_128714 := by
    simpa [prefixWord, tailWord_128714, baseEnd_128714] using wordTrace_append hprefix tailTrace_128714
  have hstable : (prefixWord ++ tailWord_128714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128714).length < 2 ^ (prefixWord ++ tailWord_128714).sum := by decide
  have hdescent : baseEnd_128714 < baseStart_128714 := by decide
  rcases family_descends (prefixWord ++ tailWord_128714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128741 : List Nat := [1, 3, 1, 4, 1, 1, 1, 4, 3, 1, 3]
def baseStart_128741 : Nat := 118140960795 + 128741 * 2 ^ 59
def prefixEnd_128741 : Nat := 4983230072969 + 3 ^ 40 * 128741 * 2
def baseEnd_128741 : Nat := 66106012940586033945437

theorem tailTrace_128741 : CollatzResearch.WordTrace tailWord_128741 prefixEnd_128741 66106012940586033945437 := by
  unfold tailWord_128741
  simp only [CollatzResearch.WordTrace]
  refine ⟨4695570026600819057418077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3130380017733879371612051 4695570026600819057418077)
  ·
    refine ⟨1760838759975307146531779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4695570026600819057418077 1760838759975307146531779)
    ·
      refine ⟨2641258139962960719797669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1760838759975307146531779 2641258139962960719797669)
      ·
        refine ⟨495235901243055134962063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2641258139962960719797669 495235901243055134962063)
        ·
          refine ⟨742853851864582702443095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495235901243055134962063 742853851864582702443095)
          ·
            refine ⟨1114280777796874053664643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742853851864582702443095 1114280777796874053664643)
            ·
              refine ⟨1671421166695311080496965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1114280777796874053664643 1671421166695311080496965)
              ·
                refine ⟨313391468755370827593181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1671421166695311080496965 313391468755370827593181)
                ·
                  refine ⟨117521800783264060347443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313391468755370827593181 117521800783264060347443)
                  ·
                    refine ⟨176282701174896090521165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117521800783264060347443 176282701174896090521165)
                    ·
                      refine ⟨66106012940586033945437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 176282701174896090521165 66106012940586033945437)
                      ·
                        rfl

theorem cell23_128741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_128741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128741 prefixEnd_128741 := by exact prefixLift 128741
  have htrace : WordTrace (prefixWord ++ tailWord_128741) baseStart_128741 baseEnd_128741 := by
    simpa [prefixWord, tailWord_128741, baseEnd_128741] using wordTrace_append hprefix tailTrace_128741
  have hstable : (prefixWord ++ tailWord_128741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128741).length < 2 ^ (prefixWord ++ tailWord_128741).sum := by decide
  have hdescent : baseEnd_128741 < baseStart_128741 := by decide
  rcases family_descends (prefixWord ++ tailWord_128741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128751 : List Nat := [1, 1, 2, 1, 5, 1, 2, 3, 2, 3, 2]
def baseStart_128751 : Nat := 118140960795 + 128751 * 2 ^ 59
def prefixEnd_128751 : Nat := 4983230072969 + 3 ^ 40 * 128751 * 2
def baseEnd_128751 : Nat := 66111147747130994820391

theorem tailTrace_128751 : CollatzResearch.WordTrace tailWord_128751 prefixEnd_128751 66111147747130994820391 := by
  unfold tailWord_128751
  simp only [CollatzResearch.WordTrace]
  refine ⟨4695934756564590765282107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3130623171043060510188071 4695934756564590765282107)
  ·
    refine ⟨7043902134846886147923161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4695934756564590765282107 7043902134846886147923161)
    ·
      refine ⟨5282926601135164610942371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7043902134846886147923161 5282926601135164610942371)
      ·
        refine ⟨7924389901702746916413557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5282926601135164610942371 7924389901702746916413557)
        ·
          refine ⟨742911553284632523413771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7924389901702746916413557 742911553284632523413771)
          ·
            refine ⟨1114367329926948785120657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742911553284632523413771 1114367329926948785120657)
            ·
              refine ⟨835775497445211588840493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1114367329926948785120657 835775497445211588840493)
              ·
                refine ⟨313415811541954345815185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 835775497445211588840493 313415811541954345815185)
                ·
                  refine ⟨235061858656465759361389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313415811541954345815185 235061858656465759361389)
                  ·
                    refine ⟨88148196996174659760521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 235061858656465759361389 88148196996174659760521)
                    ·
                      refine ⟨66111147747130994820391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 88148196996174659760521 66111147747130994820391)
                      ·
                        rfl

theorem cell23_128751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 3, 2].length) (baseStart_128751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128751 prefixEnd_128751 := by exact prefixLift 128751
  have htrace : WordTrace (prefixWord ++ tailWord_128751) baseStart_128751 baseEnd_128751 := by
    simpa [prefixWord, tailWord_128751, baseEnd_128751] using wordTrace_append hprefix tailTrace_128751
  have hstable : (prefixWord ++ tailWord_128751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128751).length < 2 ^ (prefixWord ++ tailWord_128751).sum := by decide
  have hdescent : baseEnd_128751 < baseStart_128751 := by decide
  rcases family_descends (prefixWord ++ tailWord_128751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128775 : List Nat := [1, 1, 4, 4, 2, 2, 1, 1, 3, 1, 3]
def baseStart_128775 : Nat := 118140960795 + 128775 * 2 ^ 59
def prefixEnd_128775 : Nat := 4983230072969 + 3 ^ 40 * 128775 * 2
def baseEnd_128775 : Nat := 66123471282838900920281

theorem tailTrace_128775 : CollatzResearch.WordTrace tailWord_128775 prefixEnd_128775 66123471282838900920281 := by
  unfold tailWord_128775
  simp only [CollatzResearch.WordTrace]
  refine ⟨4696810108477642864155779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3131206738985095242770519 4696810108477642864155779)
  ·
    refine ⟨7045215162716464296233669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4696810108477642864155779 7045215162716464296233669)
    ·
      refine ⟨1320977843009337055543813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7045215162716464296233669 1320977843009337055543813)
      ·
        refine ⟨247683345564250697914465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1320977843009337055543813 247683345564250697914465)
        ·
          refine ⟨185762509173188023435849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247683345564250697914465 185762509173188023435849)
          ·
            refine ⟨139321881879891017576887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185762509173188023435849 139321881879891017576887)
            ·
              refine ⟨208982822819836526365331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139321881879891017576887 208982822819836526365331)
              ·
                refine ⟨313474234229754789547997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208982822819836526365331 313474234229754789547997)
                ·
                  refine ⟨117552837836158046080499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313474234229754789547997 117552837836158046080499)
                  ·
                    refine ⟨176329256754237069120749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117552837836158046080499 176329256754237069120749)
                    ·
                      refine ⟨66123471282838900920281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 176329256754237069120749 66123471282838900920281)
                      ·
                        rfl

theorem cell23_128775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_128775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128775 prefixEnd_128775 := by exact prefixLift 128775
  have htrace : WordTrace (prefixWord ++ tailWord_128775) baseStart_128775 baseEnd_128775 := by
    simpa [prefixWord, tailWord_128775, baseEnd_128775] using wordTrace_append hprefix tailTrace_128775
  have hstable : (prefixWord ++ tailWord_128775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128775).length < 2 ^ (prefixWord ++ tailWord_128775).sum := by decide
  have hdescent : baseEnd_128775 < baseStart_128775 := by decide
  rcases family_descends (prefixWord ++ tailWord_128775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128794 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6]
def baseStart_128794 : Nat := 118140960795 + 128794 * 2 ^ 59
def prefixEnd_128794 : Nat := 4983230072969 + 3 ^ 40 * 128794 * 2
def baseEnd_128794 : Nat := 66133227415274326582693

theorem tailTrace_128794 : CollatzResearch.WordTrace tailWord_128794 prefixEnd_128794 66133227415274326582693 := by
  unfold tailWord_128794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1174375773852202277274359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3131668730272539406064957 1174375773852202277274359)
  ·
    refine ⟨1761563660778303415911539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1174375773852202277274359 1761563660778303415911539)
    ·
      refine ⟨2642345491167455123867309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1761563660778303415911539 2642345491167455123867309)
      ·
        refine ⟨990879559187795671450241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2642345491167455123867309 990879559187795671450241)
        ·
          refine ⟨743159669390846753587681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 990879559187795671450241 743159669390846753587681)
          ·
            refine ⟨557369752043135065190761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743159669390846753587681 557369752043135065190761)
            ·
              refine ⟨418027314032351298893071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557369752043135065190761 418027314032351298893071)
              ·
                refine ⟨627040971048526948339607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418027314032351298893071 627040971048526948339607)
                ·
                  refine ⟨940561456572790422509411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 627040971048526948339607 940561456572790422509411)
                  ·
                    refine ⟨1410842184859185633764117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 940561456572790422509411 1410842184859185633764117)
                    ·
                      refine ⟨66133227415274326582693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1410842184859185633764117 66133227415274326582693)
                      ·
                        rfl

theorem cell23_128794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_128794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128794 prefixEnd_128794 := by exact prefixLift 128794
  have htrace : WordTrace (prefixWord ++ tailWord_128794) baseStart_128794 baseEnd_128794 := by
    simpa [prefixWord, tailWord_128794, baseEnd_128794] using wordTrace_append hprefix tailTrace_128794
  have hstable : (prefixWord ++ tailWord_128794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128794).length < 2 ^ (prefixWord ++ tailWord_128794).sum := by decide
  have hdescent : baseEnd_128794 < baseStart_128794 := by decide
  rcases family_descends (prefixWord ++ tailWord_128794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128801 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 3, 2, 3]
def baseStart_128801 : Nat := 118140960795 + 128801 * 2 ^ 59
def prefixEnd_128801 : Nat := 4983230072969 + 3 ^ 40 * 128801 * 2
def baseEnd_128801 : Nat := 66136821779855799195161

theorem tailTrace_128801 : CollatzResearch.WordTrace tailWord_128801 prefixEnd_128801 66136821779855799195161 := by
  unfold tailWord_128801
  simp only [CollatzResearch.WordTrace]
  refine ⟨4697758406383449304602257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3131838937588966203068171 4697758406383449304602257)
  ·
    refine ⟨3523318804787586978451693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4697758406383449304602257 3523318804787586978451693)
    ·
      refine ⟨1321244551795345116919385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3523318804787586978451693 1321244551795345116919385)
      ·
        refine ⟨990933413846508837689539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1321244551795345116919385 990933413846508837689539)
        ·
          refine ⟨1486400120769763256534309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990933413846508837689539 1486400120769763256534309)
          ·
            refine ⟨278700022644330610600183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1486400120769763256534309 278700022644330610600183)
            ·
              refine ⟨418050033966495915900275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278700022644330610600183 418050033966495915900275)
              ·
                refine ⟨627075050949743873850413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418050033966495915900275 627075050949743873850413)
                ·
                  refine ⟨235153144106153952693905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627075050949743873850413 235153144106153952693905)
                  ·
                    refine ⟨176364858079615464520429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 235153144106153952693905 176364858079615464520429)
                    ·
                      refine ⟨66136821779855799195161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 176364858079615464520429 66136821779855799195161)
                      ·
                        rfl

theorem cell23_128801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_128801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128801 prefixEnd_128801 := by exact prefixLift 128801
  have htrace : WordTrace (prefixWord ++ tailWord_128801) baseStart_128801 baseEnd_128801 := by
    simpa [prefixWord, tailWord_128801, baseEnd_128801] using wordTrace_append hprefix tailTrace_128801
  have hstable : (prefixWord ++ tailWord_128801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128801).length < 2 ^ (prefixWord ++ tailWord_128801).sum := by decide
  have hdescent : baseEnd_128801 < baseStart_128801 := by decide
  rcases family_descends (prefixWord ++ tailWord_128801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128804 : List Nat := [2, 3, 1, 3, 2, 1, 2, 9]
def baseStart_128804 : Nat := 118140960795 + 128804 * 2 ^ 59
def prefixEnd_128804 : Nat := 4983230072969 + 3 ^ 40 * 128804 * 2
def baseEnd_128804 : Nat := 2449568971178492128061

theorem tailTrace_128804 : CollatzResearch.WordTrace tailWord_128804 prefixEnd_128804 2449568971178492128061 := by
  unfold tailWord_128804
  simp only [CollatzResearch.WordTrace]
  refine ⟨2348933912686290408480733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3131911883581720544640977 2348933912686290408480733)
  ·
    refine ⟨880850217257358903180275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2348933912686290408480733 880850217257358903180275)
    ·
      refine ⟨1321275325886038354770413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 880850217257358903180275 1321275325886038354770413)
      ·
        refine ⟨495478247207264383038905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1321275325886038354770413 495478247207264383038905)
        ·
          refine ⟨371608685405448287279179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495478247207264383038905 371608685405448287279179)
          ·
            refine ⟨557413028108172430918769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371608685405448287279179 557413028108172430918769)
            ·
              refine ⟨418059771081129323189077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557413028108172430918769 418059771081129323189077)
              ·
                refine ⟨2449568971178492128061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 418059771081129323189077 2449568971178492128061)
                ·
                  rfl

theorem cell23_128804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 9].length) (baseStart_128804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128804 prefixEnd_128804 := by exact prefixLift 128804
  have htrace : WordTrace (prefixWord ++ tailWord_128804) baseStart_128804 baseEnd_128804 := by
    simpa [prefixWord, tailWord_128804, baseEnd_128804] using wordTrace_append hprefix tailTrace_128804
  have hstable : (prefixWord ++ tailWord_128804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128804).length < 2 ^ (prefixWord ++ tailWord_128804).sum := by decide
  have hdescent : baseEnd_128804 < baseStart_128804 := by decide
  rcases family_descends (prefixWord ++ tailWord_128804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128825 : List Nat := [1, 2, 1, 7, 1, 1, 2, 2, 2, 4]
def baseStart_128825 : Nat := 118140960795 + 128825 * 2 ^ 59
def prefixEnd_128825 : Nat := 4983230072969 + 3 ^ 40 * 128825 * 2
def baseEnd_128825 : Nat := 22049715105187901765017

theorem tailTrace_128825 : CollatzResearch.WordTrace tailWord_128825 prefixEnd_128825 22049715105187901765017 := by
  unfold tailWord_128825
  simp only [CollatzResearch.WordTrace]
  refine ⟨4698633758296501403475929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3132422505531000935650619 4698633758296501403475929)
  ·
    refine ⟨3523975318722376052606947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4698633758296501403475929 3523975318722376052606947)
    ·
      refine ⟨5285962978083564078910421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3523975318722376052606947 5285962978083564078910421)
      ·
        refine ⟨123889757298833533099463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 5285962978083564078910421 123889757298833533099463)
        ·
          refine ⟨185834635948250299649195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123889757298833533099463 185834635948250299649195)
          ·
            refine ⟨278751953922375449473793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185834635948250299649195 278751953922375449473793)
            ·
              refine ⟨209063965441781587105345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278751953922375449473793 209063965441781587105345)
              ·
                refine ⟨156797974081336190329009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209063965441781587105345 156797974081336190329009)
                ·
                  refine ⟨117598480561002142746757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156797974081336190329009 117598480561002142746757)
                  ·
                    refine ⟨22049715105187901765017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117598480561002142746757 22049715105187901765017)
                    ·
                      rfl

theorem cell23_128825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 4].length) (baseStart_128825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128825 prefixEnd_128825 := by exact prefixLift 128825
  have htrace : WordTrace (prefixWord ++ tailWord_128825) baseStart_128825 baseEnd_128825 := by
    simpa [prefixWord, tailWord_128825, baseEnd_128825] using wordTrace_append hprefix tailTrace_128825
  have hstable : (prefixWord ++ tailWord_128825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128825).length < 2 ^ (prefixWord ++ tailWord_128825).sum := by decide
  have hdescent : baseEnd_128825 < baseStart_128825 := by decide
  rcases family_descends (prefixWord ++ tailWord_128825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128838 : List Nat := [6, 1, 1, 2, 1, 1, 3, 8]
def baseStart_128838 : Nat := 118140960795 + 128838 * 2 ^ 59
def prefixEnd_128838 : Nat := 4983230072969 + 3 ^ 40 * 128838 * 2
def baseEnd_128838 : Nat := 2450215576447116830833

theorem tailTrace_128838 : CollatzResearch.WordTrace tailWord_128838 prefixEnd_128838 2450215576447116830833 := by
  unfold tailWord_128838
  simp only [CollatzResearch.WordTrace]
  refine ⟨146847122101543894490599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3132738604832936415799445 146847122101543894490599)
  ·
    refine ⟨220270683152315841735899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146847122101543894490599 220270683152315841735899)
    ·
      refine ⟨330406024728473762603849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220270683152315841735899 330406024728473762603849)
      ·
        refine ⟨247804518546355321952887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330406024728473762603849 247804518546355321952887)
        ·
          refine ⟨371706777819532982929331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247804518546355321952887 371706777819532982929331)
          ·
            refine ⟨557560166729299474393997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371706777819532982929331 557560166729299474393997)
            ·
              refine ⟨209085062523487302897749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 557560166729299474393997 209085062523487302897749)
              ·
                refine ⟨2450215576447116830833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 209085062523487302897749 2450215576447116830833)
                ·
                  rfl

theorem cell23_128838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_128838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128838 prefixEnd_128838 := by exact prefixLift 128838
  have htrace : WordTrace (prefixWord ++ tailWord_128838) baseStart_128838 baseEnd_128838 := by
    simpa [prefixWord, tailWord_128838, baseEnd_128838] using wordTrace_append hprefix tailTrace_128838
  have hstable : (prefixWord ++ tailWord_128838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128838).length < 2 ^ (prefixWord ++ tailWord_128838).sum := by decide
  have hdescent : baseEnd_128838 < baseStart_128838 := by decide
  rcases family_descends (prefixWord ++ tailWord_128838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128841 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 5, 3, 2]
def baseStart_128841 : Nat := 118140960795 + 128841 * 2 ^ 59
def prefixEnd_128841 : Nat := 4983230072969 + 3 ^ 40 * 128841 * 2
def baseEnd_128841 : Nat := 66157361006035642694977

theorem tailTrace_128841 : CollatzResearch.WordTrace tailWord_128841 prefixEnd_128841 66157361006035642694977 := by
  unfold tailWord_128841
  simp only [CollatzResearch.WordTrace]
  refine ⟨4699217326238536136058377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3132811550825690757372251 4699217326238536136058377)
  ·
    refine ⟨3524412994678902102043783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4699217326238536136058377 3524412994678902102043783)
    ·
      refine ⟨5286619492018353153065675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3524412994678902102043783 5286619492018353153065675)
      ·
        refine ⟨7929929238027529729598513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5286619492018353153065675 7929929238027529729598513)
        ·
          refine ⟨5947446928520647297198885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7929929238027529729598513 5947446928520647297198885)
          ·
            refine ⟨1115146299097621368224791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5947446928520647297198885 1115146299097621368224791)
            ·
              refine ⟨1672719448646432052337187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1115146299097621368224791 1672719448646432052337187)
              ·
                refine ⟨2509079172969648078505781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1672719448646432052337187 2509079172969648078505781)
                ·
                  refine ⟨235226172465904507359917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2509079172969648078505781 235226172465904507359917)
                  ·
                    refine ⟨88209814674714190259969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 235226172465904507359917 88209814674714190259969)
                    ·
                      refine ⟨66157361006035642694977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 88209814674714190259969 66157361006035642694977)
                      ·
                        rfl

theorem cell23_128841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 3, 2].length) (baseStart_128841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128841 prefixEnd_128841 := by exact prefixLift 128841
  have htrace : WordTrace (prefixWord ++ tailWord_128841) baseStart_128841 baseEnd_128841 := by
    simpa [prefixWord, tailWord_128841, baseEnd_128841] using wordTrace_append hprefix tailTrace_128841
  have hstable : (prefixWord ++ tailWord_128841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128841).length < 2 ^ (prefixWord ++ tailWord_128841).sum := by decide
  have hdescent : baseEnd_128841 < baseStart_128841 := by decide
  rcases family_descends (prefixWord ++ tailWord_128841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128858 : List Nat := [3, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2]
def baseStart_128858 : Nat := 118140960795 + 128858 * 2 ^ 59
def prefixEnd_128858 : Nat := 4983230072969 + 3 ^ 40 * 128858 * 2
def baseEnd_128858 : Nat := 66166090177162076182399

theorem tailTrace_128858 : CollatzResearch.WordTrace tailWord_128858 prefixEnd_128858 66166090177162076182399 := by
  unfold tailWord_128858
  simp only [CollatzResearch.WordTrace]
  refine ⟨1174959341794237009856807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3133224911451298692951485 1174959341794237009856807)
  ·
    refine ⟨1762439012691355514785211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1174959341794237009856807 1762439012691355514785211)
    ·
      refine ⟨2643658519037033272177817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1762439012691355514785211 2643658519037033272177817)
      ·
        refine ⟨1982743889277774954133363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2643658519037033272177817 1982743889277774954133363)
        ·
          refine ⟨2974115833916662431200045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1982743889277774954133363 2974115833916662431200045)
          ·
            refine ⟨1115293437718748411700017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2974115833916662431200045 1115293437718748411700017)
            ·
              refine ⟨836470078289061308775013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1115293437718748411700017 836470078289061308775013)
              ·
                refine ⟨156838139679198995395315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 836470078289061308775013 156838139679198995395315)
                ·
                  refine ⟨235257209518798493092973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156838139679198995395315 235257209518798493092973)
                  ·
                    refine ⟨88221453569549434909865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 235257209518798493092973 88221453569549434909865)
                    ·
                      refine ⟨66166090177162076182399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 88221453569549434909865 66166090177162076182399)
                      ·
                        rfl

theorem cell23_128858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_128858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128858 prefixEnd_128858 := by exact prefixLift 128858
  have htrace : WordTrace (prefixWord ++ tailWord_128858) baseStart_128858 baseEnd_128858 := by
    simpa [prefixWord, tailWord_128858, baseEnd_128858] using wordTrace_append hprefix tailTrace_128858
  have hstable : (prefixWord ++ tailWord_128858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128858).length < 2 ^ (prefixWord ++ tailWord_128858).sum := by decide
  have hdescent : baseEnd_128858 < baseStart_128858 := by decide
  rcases family_descends (prefixWord ++ tailWord_128858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128931 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 1, 7, 2]
def baseStart_128931 : Nat := 118140960795 + 128931 * 2 ^ 59
def prefixEnd_128931 : Nat := 4983230072969 + 3 ^ 40 * 128931 * 2
def baseEnd_128931 : Nat := 66203574264940290569563

theorem tailTrace_128931 : CollatzResearch.WordTrace tailWord_128931 prefixEnd_128931 66203574264940290569563 := by
  unfold tailWord_128931
  simp only [CollatzResearch.WordTrace]
  refine ⟨4702499895912481506834647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3134999930608321004556431 4702499895912481506834647)
  ·
    refine ⟨7053749843868722260251971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4702499895912481506834647 7053749843868722260251971)
    ·
      refine ⟨10580624765803083390377957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7053749843868722260251971 10580624765803083390377957)
      ·
        refine ⟨1983867143588078135695867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10580624765803083390377957 1983867143588078135695867)
        ·
          refine ⟨2975800715382117203543801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1983867143588078135695867 2975800715382117203543801)
          ·
            refine ⟨2231850536536587902657851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2975800715382117203543801 2231850536536587902657851)
            ·
              refine ⟨3347775804804881853986777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2231850536536587902657851 3347775804804881853986777)
              ·
                refine ⟨2510831853603661390490083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3347775804804881853986777 2510831853603661390490083)
                ·
                  refine ⟨3766247780405492085735125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2510831853603661390490083 3766247780405492085735125)
                  ·
                    refine ⟨88271432353253720759417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3766247780405492085735125 88271432353253720759417)
                    ·
                      refine ⟨66203574264940290569563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 88271432353253720759417 66203574264940290569563)
                      ·
                        rfl

theorem cell23_128931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_128931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128931 prefixEnd_128931 := by exact prefixLift 128931
  have htrace : WordTrace (prefixWord ++ tailWord_128931) baseStart_128931 baseEnd_128931 := by
    simpa [prefixWord, tailWord_128931, baseEnd_128931] using wordTrace_append hprefix tailTrace_128931
  have hstable : (prefixWord ++ tailWord_128931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128931).length < 2 ^ (prefixWord ++ tailWord_128931).sum := by decide
  have hdescent : baseEnd_128931 < baseStart_128931 := by decide
  rcases family_descends (prefixWord ++ tailWord_128931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128944 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 4]
def baseStart_128944 : Nat := 118140960795 + 128944 * 2 ^ 59
def prefixEnd_128944 : Nat := 4983230072969 + 3 ^ 40 * 128944 * 2
def baseEnd_128944 : Nat := 66210249513448739707003

theorem tailTrace_128944 : CollatzResearch.WordTrace tailWord_128944 prefixEnd_128944 66210249513448739707003 := by
  unfold tailWord_128944
  simp only [CollatzResearch.WordTrace]
  refine ⟨2351487022432692363528943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3135316029910256484705257 2351487022432692363528943)
  ·
    refine ⟨3527230533649038545293415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2351487022432692363528943 3527230533649038545293415)
    ·
      refine ⟨5290845800473557817940123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3527230533649038545293415 5290845800473557817940123)
      ·
        refine ⟨7936268700710336726910185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5290845800473557817940123 7936268700710336726910185)
        ·
          refine ⟨5952201525532752545182639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7936268700710336726910185 5952201525532752545182639)
          ·
            refine ⟨8928302288299128817773959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5952201525532752545182639 8928302288299128817773959)
            ·
              refine ⟨13392453432448693226660939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8928302288299128817773959 13392453432448693226660939)
              ·
                refine ⟨20088680148673039839991409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13392453432448693226660939 20088680148673039839991409)
                ·
                  refine ⟨15066510111504779879993557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20088680148673039839991409 15066510111504779879993557)
                  ·
                    refine ⟨353121330738393278437349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15066510111504779879993557 353121330738393278437349)
                    ·
                      refine ⟨66210249513448739707003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 353121330738393278437349 66210249513448739707003)
                      ·
                        rfl

theorem cell23_128944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_128944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128944 prefixEnd_128944 := by exact prefixLift 128944
  have htrace : WordTrace (prefixWord ++ tailWord_128944) baseStart_128944 baseEnd_128944 := by
    simpa [prefixWord, tailWord_128944, baseEnd_128944] using wordTrace_append hprefix tailTrace_128944
  have hstable : (prefixWord ++ tailWord_128944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128944).length < 2 ^ (prefixWord ++ tailWord_128944).sum := by decide
  have hdescent : baseEnd_128944 < baseStart_128944 := by decide
  rcases family_descends (prefixWord ++ tailWord_128944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128945 : List Nat := [1, 2, 2, 4, 2, 2, 3, 2, 5]
def baseStart_128945 : Nat := 118140960795 + 128945 * 2 ^ 59
def prefixEnd_128945 : Nat := 4983230072969 + 3 ^ 40 * 128945 * 2
def baseEnd_128945 : Nat := 7356751443789248421611

theorem tailTrace_128945 : CollatzResearch.WordTrace tailWord_128945 prefixEnd_128945 7356751443789248421611 := by
  unfold tailWord_128945
  simp only [CollatzResearch.WordTrace]
  refine ⟨4703010517861761897844289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3135340345241174598562859 4703010517861761897844289)
  ·
    refine ⟨3527257888396321423383217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4703010517861761897844289 3527257888396321423383217)
    ·
      refine ⟨2645443416297241067537413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3527257888396321423383217 2645443416297241067537413)
      ·
        refine ⟨496020640555732700163265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2645443416297241067537413 496020640555732700163265)
        ·
          refine ⟨372015480416799525122449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496020640555732700163265 372015480416799525122449)
          ·
            refine ⟨279011610312599643841837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372015480416799525122449 279011610312599643841837)
            ·
              refine ⟨104629353867224866440689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279011610312599643841837 104629353867224866440689)
              ·
                refine ⟨78472015400418649830517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104629353867224866440689 78472015400418649830517)
                ·
                  refine ⟨7356751443789248421611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78472015400418649830517 7356751443789248421611)
                  ·
                    rfl

theorem cell23_128945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 5].length) (baseStart_128945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128945 prefixEnd_128945 := by exact prefixLift 128945
  have htrace : WordTrace (prefixWord ++ tailWord_128945) baseStart_128945 baseEnd_128945 := by
    simpa [prefixWord, tailWord_128945, baseEnd_128945] using wordTrace_append hprefix tailTrace_128945
  have hstable : (prefixWord ++ tailWord_128945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128945).length < 2 ^ (prefixWord ++ tailWord_128945).sum := by decide
  have hdescent : baseEnd_128945 < baseStart_128945 := by decide
  rcases family_descends (prefixWord ++ tailWord_128945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128954 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 2, 8]
def baseStart_128954 : Nat := 118140960795 + 128954 * 2 ^ 59
def prefixEnd_128954 : Nat := 4983230072969 + 3 ^ 40 * 128954 * 2
def baseEnd_128954 : Nat := 22071794773331233527319

theorem tailTrace_128954 : CollatzResearch.WordTrace tailWord_128954 prefixEnd_128954 22071794773331233527319 := by
  unfold tailWord_128954
  simp only [CollatzResearch.WordTrace]
  refine ⟨1175834693707289108730479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3135559183219437623281277 1175834693707289108730479)
  ·
    refine ⟨1763752040560933663095719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1175834693707289108730479 1763752040560933663095719)
    ·
      refine ⟨2645628060841400494643579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1763752040560933663095719 2645628060841400494643579)
      ·
        refine ⟨3968442091262100741965369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2645628060841400494643579 3968442091262100741965369)
        ·
          refine ⟨2976331568446575556474027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3968442091262100741965369 2976331568446575556474027)
          ·
            refine ⟨4464497352669863334711041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2976331568446575556474027 4464497352669863334711041)
            ·
              refine ⟨3348373014502397501033281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4464497352669863334711041 3348373014502397501033281)
              ·
                refine ⟨2511279760876798125774961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3348373014502397501033281 2511279760876798125774961)
                ·
                  refine ⟨1883459820657598594331221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2511279760876798125774961 1883459820657598594331221)
                  ·
                    refine ⟨22071794773331233527319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1883459820657598594331221 22071794773331233527319)
                    ·
                      rfl

theorem cell23_128954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_128954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128954 prefixEnd_128954 := by exact prefixLift 128954
  have htrace : WordTrace (prefixWord ++ tailWord_128954) baseStart_128954 baseEnd_128954 := by
    simpa [prefixWord, tailWord_128954, baseEnd_128954] using wordTrace_append hprefix tailTrace_128954
  have hstable : (prefixWord ++ tailWord_128954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128954).length < 2 ^ (prefixWord ++ tailWord_128954).sum := by decide
  have hdescent : baseEnd_128954 < baseStart_128954 := by decide
  rcases family_descends (prefixWord ++ tailWord_128954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128956 : List Nat := [2, 2, 2, 5, 1, 2, 2, 1, 2, 2, 2]
def baseStart_128956 : Nat := 118140960795 + 128956 * 2 ^ 59
def prefixEnd_128956 : Nat := 4983230072969 + 3 ^ 40 * 128956 * 2
def baseEnd_128956 : Nat := 66216411281302692756949

theorem tailTrace_128956 : CollatzResearch.WordTrace tailWord_128956 prefixEnd_128956 66216411281302692756949 := by
  unfold tailWord_128956
  simp only [CollatzResearch.WordTrace]
  refine ⟨2351705860410955388247361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3135607813881273850996481 2351705860410955388247361)
  ·
    refine ⟨1763779395308216541185521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2351705860410955388247361 1763779395308216541185521)
    ·
      refine ⟨1322834546481162405889141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1763779395308216541185521 1322834546481162405889141)
      ·
        refine ⟨124015738732608975552107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1322834546481162405889141 124015738732608975552107)
        ·
          refine ⟨186023608098913463328161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124015738732608975552107 186023608098913463328161)
          ·
            refine ⟨139517706074185097496121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186023608098913463328161 139517706074185097496121)
            ·
              refine ⟨104638279555638823122091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139517706074185097496121 104638279555638823122091)
              ·
                refine ⟨156957419333458234683137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104638279555638823122091 156957419333458234683137)
                ·
                  refine ⟨117718064500093676012353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156957419333458234683137 117718064500093676012353)
                  ·
                    refine ⟨88288548375070257009265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117718064500093676012353 88288548375070257009265)
                    ·
                      refine ⟨66216411281302692756949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 88288548375070257009265 66216411281302692756949)
                      ·
                        rfl

theorem cell23_128956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_128956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128956 prefixEnd_128956 := by exact prefixLift 128956
  have htrace : WordTrace (prefixWord ++ tailWord_128956) baseStart_128956 baseEnd_128956 := by
    simpa [prefixWord, tailWord_128956, baseEnd_128956] using wordTrace_append hprefix tailTrace_128956
  have hstable : (prefixWord ++ tailWord_128956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128956).length < 2 ^ (prefixWord ++ tailWord_128956).sum := by decide
  have hdescent : baseEnd_128956 < baseStart_128956 := by decide
  rcases family_descends (prefixWord ++ tailWord_128956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_128971 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 5, 4]
def baseStart_128971 : Nat := 118140960795 + 128971 * 2 ^ 59
def prefixEnd_128971 : Nat := 4983230072969 + 3 ^ 40 * 128971 * 2
def baseEnd_128971 : Nat := 22074704497040044689793

theorem tailTrace_128971 : CollatzResearch.WordTrace tailWord_128971 prefixEnd_128971 22074704497040044689793 := by
  unfold tailWord_128971
  simp only [CollatzResearch.WordTrace]
  refine ⟨4703958815767568338290767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3135972543845045558860511 4703958815767568338290767)
  ·
    refine ⟨7055938223651352507436151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4703958815767568338290767 7055938223651352507436151)
    ·
      refine ⟨10583907335477028761154227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7055938223651352507436151 10583907335477028761154227)
      ·
        refine ⟨15875861003215543141731341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10583907335477028761154227 15875861003215543141731341)
        ·
          refine ⟨5953447876205828678149253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15875861003215543141731341 5953447876205828678149253)
          ·
            refine ⟨1116271476788592877152985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5953447876205828678149253 1116271476788592877152985)
            ·
              refine ⟨837203607591444657864739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1116271476788592877152985 837203607591444657864739)
              ·
                refine ⟨1255805411387166986797109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837203607591444657864739 1255805411387166986797109)
                ·
                  refine ⟨117731757317546905012229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1255805411387166986797109 117731757317546905012229)
                  ·
                    refine ⟨22074704497040044689793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117731757317546905012229 22074704497040044689793)
                    ·
                      rfl

theorem cell23_128971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 4].length) (baseStart_128971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_128971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_128971 prefixEnd_128971 := by exact prefixLift 128971
  have htrace : WordTrace (prefixWord ++ tailWord_128971) baseStart_128971 baseEnd_128971 := by
    simpa [prefixWord, tailWord_128971, baseEnd_128971] using wordTrace_append hprefix tailTrace_128971
  have hstable : (prefixWord ++ tailWord_128971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_128971).length < 2 ^ (prefixWord ++ tailWord_128971).sum := by decide
  have hdescent : baseEnd_128971 < baseStart_128971 := by decide
  rcases family_descends (prefixWord ++ tailWord_128971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129048 : List Nat := [2, 1, 2, 3, 2, 1, 3, 3, 1, 5]
def baseStart_129048 : Nat := 118140960795 + 129048 * 2 ^ 59
def prefixEnd_129048 : Nat := 4983230072969 + 3 ^ 40 * 129048 * 2
def baseEnd_129048 : Nat := 22087883833838777602175

theorem tailTrace_129048 : CollatzResearch.WordTrace tailWord_129048 prefixEnd_129048 22087883833838777602175 := by
  unfold tailWord_129048
  simp only [CollatzResearch.WordTrace]
  refine ⟨2353383618244305244421899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3137844824325740325895865 2353383618244305244421899)
  ·
    refine ⟨3530075427366457866632849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2353383618244305244421899 3530075427366457866632849)
    ·
      refine ⟨2647556570524843399974637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3530075427366457866632849 2647556570524843399974637)
      ·
        refine ⟨992833713946816274990489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2647556570524843399974637 992833713946816274990489)
        ·
          refine ⟨744625285460112206242867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 992833713946816274990489 744625285460112206242867)
          ·
            refine ⟨1116937928190168309364301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744625285460112206242867 1116937928190168309364301)
            ·
              refine ⟨418851723071313116011613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1116937928190168309364301 418851723071313116011613)
              ·
                refine ⟨157069396151742418504355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418851723071313116011613 157069396151742418504355)
                ·
                  refine ⟨235604094227613627756533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157069396151742418504355 235604094227613627756533)
                  ·
                    refine ⟨22087883833838777602175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 235604094227613627756533 22087883833838777602175)
                    ·
                      rfl

theorem cell23_129048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_129048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129048 prefixEnd_129048 := by exact prefixLift 129048
  have htrace : WordTrace (prefixWord ++ tailWord_129048) baseStart_129048 baseEnd_129048 := by
    simpa [prefixWord, tailWord_129048, baseEnd_129048] using wordTrace_append hprefix tailTrace_129048
  have hstable : (prefixWord ++ tailWord_129048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129048).length < 2 ^ (prefixWord ++ tailWord_129048).sum := by decide
  have hdescent : baseEnd_129048 < baseStart_129048 := by decide
  rcases family_descends (prefixWord ++ tailWord_129048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129051 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 4]
def baseStart_129051 : Nat := 118140960795 + 129051 * 2 ^ 59
def prefixEnd_129051 : Nat := 4983230072969 + 3 ^ 40 * 129051 * 2
def baseEnd_129051 : Nat := 66265191943479821069011

theorem tailTrace_129051 : CollatzResearch.WordTrace tailWord_129051 prefixEnd_129051 66265191943479821069011 := by
  unfold tailWord_129051
  simp only [CollatzResearch.WordTrace]
  refine ⟨4706876655477742001203007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3137917770318494667468671 4706876655477742001203007)
  ·
    refine ⟨7060314983216613001804511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4706876655477742001203007 7060314983216613001804511)
    ·
      refine ⟨10590472474824919502706767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7060314983216613001804511 10590472474824919502706767)
      ·
        refine ⟨15885708712237379254060151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10590472474824919502706767 15885708712237379254060151)
        ·
          refine ⟨23828563068356068881090227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15885708712237379254060151 23828563068356068881090227)
          ·
            refine ⟨35742844602534103321635341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23828563068356068881090227 35742844602534103321635341)
            ·
              refine ⟨13403566725950288745613253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35742844602534103321635341 13403566725950288745613253)
              ·
                refine ⟨2513168761115679139802485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13403566725950288745613253 2513168761115679139802485)
                ·
                  refine ⟨235609571354594919356483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2513168761115679139802485 235609571354594919356483)
                  ·
                    refine ⟨353414357031892379034725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 235609571354594919356483 353414357031892379034725)
                    ·
                      refine ⟨66265191943479821069011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 353414357031892379034725 66265191943479821069011)
                      ·
                        rfl

theorem cell23_129051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 4].length) (baseStart_129051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129051 prefixEnd_129051 := by exact prefixLift 129051
  have htrace : WordTrace (prefixWord ++ tailWord_129051) baseStart_129051 baseEnd_129051 := by
    simpa [prefixWord, tailWord_129051, baseEnd_129051] using wordTrace_append hprefix tailTrace_129051
  have hstable : (prefixWord ++ tailWord_129051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129051).length < 2 ^ (prefixWord ++ tailWord_129051).sum := by decide
  have hdescent : baseEnd_129051 < baseStart_129051 := by decide
  rcases family_descends (prefixWord ++ tailWord_129051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129071 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 3]
def baseStart_129071 : Nat := 118140960795 + 129071 * 2 ^ 59
def prefixEnd_129071 : Nat := 4983230072969 + 3 ^ 40 * 129071 * 2
def baseEnd_129071 : Nat := 66275461556569742818919

theorem tailTrace_129071 : CollatzResearch.WordTrace tailWord_129071 prefixEnd_129071 66275461556569742818919 := by
  unfold tailWord_129071
  simp only [CollatzResearch.WordTrace]
  refine ⟨4707606115405285416931067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3138404076936856944620711 4707606115405285416931067)
  ·
    refine ⟨7061409173107928125396601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4707606115405285416931067 7061409173107928125396601)
    ·
      refine ⟨5296056879830946094047451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7061409173107928125396601 5296056879830946094047451)
      ·
        refine ⟨7944085319746419141071177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5296056879830946094047451 7944085319746419141071177)
        ·
          refine ⟨5958063989809814355803383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7944085319746419141071177 5958063989809814355803383)
          ·
            refine ⟨8937095984714721533705075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5958063989809814355803383 8937095984714721533705075)
            ·
              refine ⟨13405643977072082300557613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8937095984714721533705075 13405643977072082300557613)
              ·
                refine ⟨5027116491402030862709105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13405643977072082300557613 5027116491402030862709105)
                ·
                  refine ⟨3770337368551523147031829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5027116491402030862709105 3770337368551523147031829)
                  ·
                    refine ⟨176734564150852647517117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3770337368551523147031829 176734564150852647517117)
                    ·
                      refine ⟨66275461556569742818919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 176734564150852647517117 66275461556569742818919)
                      ·
                        rfl

theorem cell23_129071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 3].length) (baseStart_129071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129071 prefixEnd_129071 := by exact prefixLift 129071
  have htrace : WordTrace (prefixWord ++ tailWord_129071) baseStart_129071 baseEnd_129071 := by
    simpa [prefixWord, tailWord_129071, baseEnd_129071] using wordTrace_append hprefix tailTrace_129071
  have hstable : (prefixWord ++ tailWord_129071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129071).length < 2 ^ (prefixWord ++ tailWord_129071).sum := by decide
  have hdescent : baseEnd_129071 < baseStart_129071 := by decide
  rcases family_descends (prefixWord ++ tailWord_129071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129085 : List Nat := [1, 4, 1, 3, 1, 1, 4, 2, 1, 1, 4]
def baseStart_129085 : Nat := 118140960795 + 129085 * 2 ^ 59
def prefixEnd_129085 : Nat := 4983230072969 + 3 ^ 40 * 129085 * 2
def baseEnd_129085 : Nat := 66282650285732688043855

theorem tailTrace_129085 : CollatzResearch.WordTrace tailWord_129085 prefixEnd_129085 66282650285732688043855 := by
  unfold tailWord_129085
  simp only [CollatzResearch.WordTrace]
  refine ⟨4708116737354565807940709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3138744491569710538627139 4708116737354565807940709)
  ·
    refine ⟨882771888253981088988883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4708116737354565807940709 882771888253981088988883)
    ·
      refine ⟨1324157832380971633483325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 882771888253981088988883 1324157832380971633483325)
      ·
        refine ⟨496559187142864362556247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1324157832380971633483325 496559187142864362556247)
        ·
          refine ⟨744838780714296543834371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496559187142864362556247 744838780714296543834371)
          ·
            refine ⟨1117258171071444815751557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744838780714296543834371 1117258171071444815751557)
            ·
              refine ⟨209485907075895902953417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1117258171071444815751557 209485907075895902953417)
              ·
                refine ⟨157114430306921927215063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209485907075895902953417 157114430306921927215063)
                ·
                  refine ⟨235671645460382890822595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157114430306921927215063 235671645460382890822595)
                  ·
                    refine ⟨353507468190574336233893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 235671645460382890822595 353507468190574336233893)
                    ·
                      refine ⟨66282650285732688043855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 353507468190574336233893 66282650285732688043855)
                      ·
                        rfl

theorem cell23_129085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_129085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129085 prefixEnd_129085 := by exact prefixLift 129085
  have htrace : WordTrace (prefixWord ++ tailWord_129085) baseStart_129085 baseEnd_129085 := by
    simpa [prefixWord, tailWord_129085, baseEnd_129085] using wordTrace_append hprefix tailTrace_129085
  have hstable : (prefixWord ++ tailWord_129085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129085).length < 2 ^ (prefixWord ++ tailWord_129085).sum := by decide
  have hdescent : baseEnd_129085 < baseStart_129085 := by decide
  rcases family_descends (prefixWord ++ tailWord_129085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129121 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 2, 7]
def baseStart_129121 : Nat := 118140960795 + 129121 * 2 ^ 59
def prefixEnd_129121 : Nat := 4983230072969 + 3 ^ 40 * 129121 * 2
def baseEnd_129121 : Nat := 22100378529764849064563

theorem tailTrace_129121 : CollatzResearch.WordTrace tailWord_129121 prefixEnd_129121 22100378529764849064563 := by
  unfold tailWord_129121
  simp only [CollatzResearch.WordTrace]
  refine ⟨4709429765224143956251217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3139619843482762637500811 4709429765224143956251217)
  ·
    refine ⟨3532072323918107967188413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4709429765224143956251217 3532072323918107967188413)
    ·
      refine ⟨1324527121469290487695655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3532072323918107967188413 1324527121469290487695655)
      ·
        refine ⟨1986790682203935731543483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1324527121469290487695655 1986790682203935731543483)
        ·
          refine ⟨2980186023305903597315225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1986790682203935731543483 2980186023305903597315225)
          ·
            refine ⟨2235139517479427697986419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2980186023305903597315225 2235139517479427697986419)
            ·
              refine ⟨3352709276219141546979629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2235139517479427697986419 3352709276219141546979629)
              ·
                refine ⟨1257265978582178080117361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3352709276219141546979629 1257265978582178080117361)
                ·
                  refine ⟨942949483936633560088021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1257265978582178080117361 942949483936633560088021)
                  ·
                    refine ⟨22100378529764849064563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 942949483936633560088021 22100378529764849064563)
                    ·
                      rfl

theorem cell23_129121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_129121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129121 prefixEnd_129121 := by exact prefixLift 129121
  have htrace : WordTrace (prefixWord ++ tailWord_129121) baseStart_129121 baseEnd_129121 := by
    simpa [prefixWord, tailWord_129121, baseEnd_129121] using wordTrace_append hprefix tailTrace_129121
  have hstable : (prefixWord ++ tailWord_129121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129121).length < 2 ^ (prefixWord ++ tailWord_129121).sum := by decide
  have hdescent : baseEnd_129121 < baseStart_129121 := by decide
  rcases family_descends (prefixWord ++ tailWord_129121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129171 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 6]
def baseStart_129171 : Nat := 118140960795 + 129171 * 2 ^ 59
def prefixEnd_129171 : Nat := 4983230072969 + 3 ^ 40 * 129171 * 2
def baseEnd_129171 : Nat := 66326809622019351568459

theorem tailTrace_129171 : CollatzResearch.WordTrace tailWord_129171 prefixEnd_129171 66326809622019351568459 := by
  unfold tailWord_129171
  simp only [CollatzResearch.WordTrace]
  refine ⟨4711253415043002495571367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3140835610028668330380911 4711253415043002495571367)
  ·
    refine ⟨7066880122564503743357051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4711253415043002495571367 7066880122564503743357051)
    ·
      refine ⟨10600320183846755615035577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7066880122564503743357051 10600320183846755615035577)
      ·
        refine ⟨7950240137885066711276683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10600320183846755615035577 7950240137885066711276683)
        ·
          refine ⟨11925360206827600066915025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7950240137885066711276683 11925360206827600066915025)
          ·
            refine ⟨8944020155120700050186269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11925360206827600066915025 8944020155120700050186269)
            ·
              refine ⟨3354007558170262518819851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8944020155120700050186269 3354007558170262518819851)
              ·
                refine ⟨5031011337255393778229777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3354007558170262518819851 5031011337255393778229777)
                ·
                  refine ⟨3773258502941545333672333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5031011337255393778229777 3773258502941545333672333)
                  ·
                    refine ⟨1414971938603079500127125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3773258502941545333672333 1414971938603079500127125)
                    ·
                      refine ⟨66326809622019351568459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1414971938603079500127125 66326809622019351568459)
                      ·
                        rfl

theorem cell23_129171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_129171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129171 prefixEnd_129171 := by exact prefixLift 129171
  have htrace : WordTrace (prefixWord ++ tailWord_129171) baseStart_129171 baseEnd_129171 := by
    simpa [prefixWord, tailWord_129171, baseEnd_129171] using wordTrace_append hprefix tailTrace_129171
  have hstable : (prefixWord ++ tailWord_129171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129171).length < 2 ^ (prefixWord ++ tailWord_129171).sum := by decide
  have hdescent : baseEnd_129171 < baseStart_129171 := by decide
  rcases family_descends (prefixWord ++ tailWord_129171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129208 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 1, 5, 3]
def baseStart_129208 : Nat := 118140960795 + 129208 * 2 ^ 59
def prefixEnd_129208 : Nat := 4983230072969 + 3 ^ 40 * 129208 * 2
def baseEnd_129208 : Nat := 66345808406235706805789

theorem tailTrace_129208 : CollatzResearch.WordTrace tailWord_129208 prefixEnd_129208 66345808406235706805789 := by
  unfold tailWord_129208
  simp only [CollatzResearch.WordTrace]
  refine ⟨2356301457954478907334139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3141735277272638543112185 2356301457954478907334139)
  ·
    refine ⟨3534452186931718361001209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2356301457954478907334139 3534452186931718361001209)
    ·
      refine ⟨2650839140198788770750907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3534452186931718361001209 2650839140198788770750907)
      ·
        refine ⟨3976258710298183156126361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2650839140198788770750907 3976258710298183156126361)
        ·
          refine ⟨2982194032723637367094771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3976258710298183156126361 2982194032723637367094771)
          ·
            refine ⟨4473291049085456050642157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2982194032723637367094771 4473291049085456050642157)
            ·
              refine ⟨1677484143407046018990809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4473291049085456050642157 1677484143407046018990809)
              ·
                refine ⟨1258113107555284514243107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1677484143407046018990809 1258113107555284514243107)
                ·
                  refine ⟨1887169661332926771364661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1258113107555284514243107 1887169661332926771364661)
                  ·
                    refine ⟨176922155749961884815437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1887169661332926771364661 176922155749961884815437)
                    ·
                      refine ⟨66345808406235706805789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 176922155749961884815437 66345808406235706805789)
                      ·
                        rfl

theorem cell23_129208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_129208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129208 prefixEnd_129208 := by exact prefixLift 129208
  have htrace : WordTrace (prefixWord ++ tailWord_129208) baseStart_129208 baseEnd_129208 := by
    simpa [prefixWord, tailWord_129208, baseEnd_129208] using wordTrace_append hprefix tailTrace_129208
  have hstable : (prefixWord ++ tailWord_129208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129208).length < 2 ^ (prefixWord ++ tailWord_129208).sum := by decide
  have hdescent : baseEnd_129208 < baseStart_129208 := by decide
  rcases family_descends (prefixWord ++ tailWord_129208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129245 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 1, 7]
def baseStart_129245 : Nat := 118140960795 + 129245 * 2 ^ 59
def prefixEnd_129245 : Nat := 4983230072969 + 3 ^ 40 * 129245 * 2
def baseEnd_129245 : Nat := 22121602396817354014373

theorem tailTrace_129245 : CollatzResearch.WordTrace tailWord_129245 prefixEnd_129245 22121602396817354014373 := by
  unfold tailWord_129245
  simp only [CollatzResearch.WordTrace]
  refine ⟨4713952416774913133765189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3142634944516608755843459 4713952416774913133765189)
  ·
    refine ⟨883866078145296212580973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4713952416774913133765189 883866078145296212580973)
    ·
      refine ⟨331449779304486079717865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 883866078145296212580973 331449779304486079717865)
      ·
        refine ⟨248587334478364559788399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331449779304486079717865 248587334478364559788399)
        ·
          refine ⟨372881001717546839682599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248587334478364559788399 372881001717546839682599)
          ·
            refine ⟨559321502576320259523899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372881001717546839682599 559321502576320259523899)
            ·
              refine ⟨838982253864480389285849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559321502576320259523899 838982253864480389285849)
              ·
                refine ⟨629236690398360291964387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 838982253864480389285849 629236690398360291964387)
                ·
                  refine ⟨943855035597540437946581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629236690398360291964387 943855035597540437946581)
                  ·
                    refine ⟨22121602396817354014373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 943855035597540437946581 22121602396817354014373)
                    ·
                      rfl

theorem cell23_129245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_129245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129245 prefixEnd_129245 := by exact prefixLift 129245
  have htrace : WordTrace (prefixWord ++ tailWord_129245) baseStart_129245 baseEnd_129245 := by
    simpa [prefixWord, tailWord_129245, baseEnd_129245] using wordTrace_append hprefix tailTrace_129245
  have hstable : (prefixWord ++ tailWord_129245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129245).length < 2 ^ (prefixWord ++ tailWord_129245).sum := by decide
  have hdescent : baseEnd_129245 < baseStart_129245 := by decide
  rcases family_descends (prefixWord ++ tailWord_129245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129248 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 4]
def baseStart_129248 : Nat := 118140960795 + 129248 * 2 ^ 59
def prefixEnd_129248 : Nat := 4983230072969 + 3 ^ 40 * 129248 * 2
def baseEnd_129248 : Nat := 66366347632415550305605

theorem tailTrace_129248 : CollatzResearch.WordTrace tailWord_129248 prefixEnd_129248 66366347632415550305605 := by
  unfold tailWord_129248
  simp only [CollatzResearch.WordTrace]
  refine ⟨2357030917882022323062199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3142707890509363097416265 2357030917882022323062199)
  ·
    refine ⟨3535546376823033484593299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2357030917882022323062199 3535546376823033484593299)
    ·
      refine ⟨5303319565234550226889949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3535546376823033484593299 5303319565234550226889949)
      ·
        refine ⟨1988744836962956335083731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5303319565234550226889949 1988744836962956335083731)
        ·
          refine ⟨2983117255444434502625597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1988744836962956335083731 2983117255444434502625597)
          ·
            refine ⟨1118668970791662938484599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2983117255444434502625597 1118668970791662938484599)
            ·
              refine ⟨1678003456187494407726899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118668970791662938484599 1678003456187494407726899)
              ·
                refine ⟨2517005184281241611590349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1678003456187494407726899 2517005184281241611590349)
                ·
                  refine ⟨943876944105465604346381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2517005184281241611590349 943876944105465604346381)
                  ·
                    refine ⟨353953854039549601629893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 943876944105465604346381 353953854039549601629893)
                    ·
                      refine ⟨66366347632415550305605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 353953854039549601629893 66366347632415550305605)
                      ·
                        rfl

theorem cell23_129248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_129248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129248 prefixEnd_129248 := by exact prefixLift 129248
  have htrace : WordTrace (prefixWord ++ tailWord_129248) baseStart_129248 baseEnd_129248 := by
    simpa [prefixWord, tailWord_129248, baseEnd_129248] using wordTrace_append hprefix tailTrace_129248
  have hstable : (prefixWord ++ tailWord_129248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129248).length < 2 ^ (prefixWord ++ tailWord_129248).sum := by decide
  have hdescent : baseEnd_129248 < baseStart_129248 := by decide
  rcases family_descends (prefixWord ++ tailWord_129248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129258 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 2, 8]
def baseStart_129258 : Nat := 118140960795 + 129258 * 2 ^ 59
def prefixEnd_129258 : Nat := 4983230072969 + 3 ^ 40 * 129258 * 2
def baseEnd_129258 : Nat := 22123827479653503726853

theorem tailTrace_129258 : CollatzResearch.WordTrace tailWord_129258 prefixEnd_129258 22123827479653503726853 := by
  unfold tailWord_129258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1178606641431954088497107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3142951043818544235992285 1178606641431954088497107)
  ·
    refine ⟨1767909962147931132745661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1178606641431954088497107 1767909962147931132745661)
    ·
      refine ⟨662966235805474174779623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1767909962147931132745661 662966235805474174779623)
      ·
        refine ⟨994449353708211262169435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662966235805474174779623 994449353708211262169435)
        ·
          refine ⟨1491674030562316893254153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994449353708211262169435 1491674030562316893254153)
          ·
            refine ⟨1118755522921737669940615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1491674030562316893254153 1118755522921737669940615)
            ·
              refine ⟨1678133284382606504910923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118755522921737669940615 1678133284382606504910923)
              ·
                refine ⟨2517199926573909757366385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1678133284382606504910923 2517199926573909757366385)
                ·
                  refine ⟨1887899944930432318024789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2517199926573909757366385 1887899944930432318024789)
                  ·
                    refine ⟨22123827479653503726853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1887899944930432318024789 22123827479653503726853)
                    ·
                      rfl

theorem cell23_129258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_129258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129258 prefixEnd_129258 := by exact prefixLift 129258
  have htrace : WordTrace (prefixWord ++ tailWord_129258) baseStart_129258 baseEnd_129258 := by
    simpa [prefixWord, tailWord_129258, baseEnd_129258] using wordTrace_append hprefix tailTrace_129258
  have hstable : (prefixWord ++ tailWord_129258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129258).length < 2 ^ (prefixWord ++ tailWord_129258).sum := by decide
  have hdescent : baseEnd_129258 < baseStart_129258 := by decide
  rcases family_descends (prefixWord ++ tailWord_129258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129265 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 1, 6, 2]
def baseStart_129265 : Nat := 118140960795 + 129265 * 2 ^ 59
def prefixEnd_129265 : Nat := 4983230072969 + 3 ^ 40 * 129265 * 2
def baseEnd_129265 : Nat := 66375076803541983793027

theorem tailTrace_129265 : CollatzResearch.WordTrace tailWord_129265 prefixEnd_129265 66375076803541983793027 := by
  unfold tailWord_129265
  simp only [CollatzResearch.WordTrace]
  refine ⟨4714681876702456549493249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3143121251134971032995499 4714681876702456549493249)
  ·
    refine ⟨3536011407526842412119937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4714681876702456549493249 3536011407526842412119937)
    ·
      refine ⟨2652008555645131809089953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3536011407526842412119937 2652008555645131809089953)
      ·
        refine ⟨1989006416733848856817465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2652008555645131809089953 1989006416733848856817465)
        ·
          refine ⟨1491754812550386642613099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1989006416733848856817465 1491754812550386642613099)
          ·
            refine ⟨2237632218825579963919649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491754812550386642613099 2237632218825579963919649)
            ·
              refine ⟨1678224164119184972939737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2237632218825579963919649 1678224164119184972939737)
              ·
                refine ⟨1258668123089388729704803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1678224164119184972939737 1258668123089388729704803)
                ·
                  refine ⟨1888002184634083094557205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1258668123089388729704803 1888002184634083094557205)
                  ·
                    refine ⟨88500102404722645057369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1888002184634083094557205 88500102404722645057369)
                    ·
                      refine ⟨66375076803541983793027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 88500102404722645057369 66375076803541983793027)
                      ·
                        rfl

theorem cell23_129265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_129265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129265 prefixEnd_129265 := by exact prefixLift 129265
  have htrace : WordTrace (prefixWord ++ tailWord_129265) baseStart_129265 baseEnd_129265 := by
    simpa [prefixWord, tailWord_129265, baseEnd_129265] using wordTrace_append hprefix tailTrace_129265
  have hstable : (prefixWord ++ tailWord_129265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129265).length < 2 ^ (prefixWord ++ tailWord_129265).sum := by decide
  have hdescent : baseEnd_129265 < baseStart_129265 := by decide
  rcases family_descends (prefixWord ++ tailWord_129265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129282 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_129282 : Nat := 118140960795 + 129282 * 2 ^ 59
def prefixEnd_129282 : Nat := 4983230072969 + 3 ^ 40 * 129282 * 2
def baseEnd_129282 : Nat := 66383805974668417280449

theorem tailTrace_129282 : CollatzResearch.WordTrace tailWord_129282 prefixEnd_129282 66383805974668417280449 := by
  unfold tailWord_129282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1178825479410217113215525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3143534611760578968574733 1178825479410217113215525)
  ·
    refine ⟨221029777389415708727911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1178825479410217113215525 221029777389415708727911)
    ·
      refine ⟨331544666084123563091867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221029777389415708727911 331544666084123563091867)
      ·
        refine ⟨497316999126185344637801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331544666084123563091867 497316999126185344637801)
        ·
          refine ⟨372987749344639008478351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497316999126185344637801 372987749344639008478351)
          ·
            refine ⟨559481624016958512717527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372987749344639008478351 559481624016958512717527)
            ·
              refine ⟨839222436025437769076291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559481624016958512717527 839222436025437769076291)
              ·
                refine ⟨1258833654038156653614437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 839222436025437769076291 1258833654038156653614437)
                ·
                  refine ⟨236031310132154372552707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1258833654038156653614437 236031310132154372552707)
                  ·
                    refine ⟨354046965198231558829061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 236031310132154372552707 354046965198231558829061)
                    ·
                      refine ⟨66383805974668417280449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 354046965198231558829061 66383805974668417280449)
                      ·
                        rfl

theorem cell23_129282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_129282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129282 prefixEnd_129282 := by exact prefixLift 129282
  have htrace : WordTrace (prefixWord ++ tailWord_129282) baseStart_129282 baseEnd_129282 := by
    simpa [prefixWord, tailWord_129282, baseEnd_129282] using wordTrace_append hprefix tailTrace_129282
  have hstable : (prefixWord ++ tailWord_129282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129282).length < 2 ^ (prefixWord ++ tailWord_129282).sum := by decide
  have hdescent : baseEnd_129282 < baseStart_129282 := by decide
  rcases family_descends (prefixWord ++ tailWord_129282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129328 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 5]
def baseStart_129328 : Nat := 118140960795 + 129328 * 2 ^ 59
def prefixEnd_129328 : Nat := 4983230072969 + 3 ^ 40 * 129328 * 2
def baseEnd_129328 : Nat := 66407426084775237305237

theorem tailTrace_129328 : CollatzResearch.WordTrace tailWord_129328 prefixEnd_129328 66407426084775237305237 := by
  unfold tailWord_129328
  simp only [CollatzResearch.WordTrace]
  refine ⟨2358489837737109154518319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3144653116982812206024425 2358489837737109154518319)
  ·
    refine ⟨3537734756605663731777479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2358489837737109154518319 3537734756605663731777479)
    ·
      refine ⟨5306602134908495597666219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3537734756605663731777479 5306602134908495597666219)
      ·
        refine ⟨7959903202362743396499329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5306602134908495597666219 7959903202362743396499329)
        ·
          refine ⟨5969927401772057547374497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7959903202362743396499329 5969927401772057547374497)
          ·
            refine ⟨4477445551329043160530873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5969927401772057547374497 4477445551329043160530873)
            ·
              refine ⟨3358084163496782370398155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4477445551329043160530873 3358084163496782370398155)
              ·
                refine ⟨5037126245245173555597233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3358084163496782370398155 5037126245245173555597233)
                ·
                  refine ⟨3777844683933880166697925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5037126245245173555597233 3777844683933880166697925)
                  ·
                    refine ⟨708345878237602531255861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3777844683933880166697925 708345878237602531255861)
                    ·
                      refine ⟨66407426084775237305237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 708345878237602531255861 66407426084775237305237)
                      ·
                        rfl

theorem cell23_129328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_129328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129328 prefixEnd_129328 := by exact prefixLift 129328
  have htrace : WordTrace (prefixWord ++ tailWord_129328) baseStart_129328 baseEnd_129328 := by
    simpa [prefixWord, tailWord_129328, baseEnd_129328] using wordTrace_append hprefix tailTrace_129328
  have hstable : (prefixWord ++ tailWord_129328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129328).length < 2 ^ (prefixWord ++ tailWord_129328).sum := by decide
  have hdescent : baseEnd_129328 < baseStart_129328 := by decide
  rcases family_descends (prefixWord ++ tailWord_129328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129335 : List Nat := [1, 1, 3, 1, 2, 1, 1, 7, 1, 5]
def baseStart_129335 : Nat := 118140960795 + 129335 * 2 ^ 59
def prefixEnd_129335 : Nat := 4983230072969 + 3 ^ 40 * 129335 * 2
def baseEnd_129335 : Nat := 22137006816452236639235

theorem tailTrace_129335 : CollatzResearch.WordTrace tailWord_129335 prefixEnd_129335 22137006816452236639235 := by
  unfold tailWord_129335
  simp only [CollatzResearch.WordTrace]
  refine ⟨4717234986448858504541459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3144823324299239003027639 4717234986448858504541459)
  ·
    refine ⟨7075852479673287756812189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4717234986448858504541459 7075852479673287756812189)
    ·
      refine ⟨2653444679877482908804571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7075852479673287756812189 2653444679877482908804571)
      ·
        refine ⟨3980167019816224363206857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2653444679877482908804571 3980167019816224363206857)
        ·
          refine ⟨2985125264862168272405143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3980167019816224363206857 2985125264862168272405143)
          ·
            refine ⟨4477687897293252408607715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2985125264862168272405143 4477687897293252408607715)
            ·
              refine ⟨6716531845939878612911573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4477687897293252408607715 6716531845939878612911573)
              ·
                refine ⟨157418715139215904990115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6716531845939878612911573 157418715139215904990115)
                ·
                  refine ⟨236128072708823857485173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157418715139215904990115 236128072708823857485173)
                  ·
                    refine ⟨22137006816452236639235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 236128072708823857485173 22137006816452236639235)
                    ·
                      rfl

theorem cell23_129335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_129335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129335 prefixEnd_129335 := by exact prefixLift 129335
  have htrace : WordTrace (prefixWord ++ tailWord_129335) baseStart_129335 baseEnd_129335 := by
    simpa [prefixWord, tailWord_129335, baseEnd_129335] using wordTrace_append hprefix tailTrace_129335
  have hstable : (prefixWord ++ tailWord_129335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129335).length < 2 ^ (prefixWord ++ tailWord_129335).sum := by decide
  have hdescent : baseEnd_129335 < baseStart_129335 := by decide
  rcases family_descends (prefixWord ++ tailWord_129335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129376 : List Nat := [2, 1, 1, 3, 5, 2, 1, 1, 2, 3, 2]
def baseStart_129376 : Nat := 118140960795 + 129376 * 2 ^ 59
def prefixEnd_129376 : Nat := 4983230072969 + 3 ^ 40 * 129376 * 2
def baseEnd_129376 : Nat := 66432073156191049505017

theorem tailTrace_129376 : CollatzResearch.WordTrace tailWord_129376 prefixEnd_129376 66432073156191049505017 := by
  unfold tailWord_129376
  simp only [CollatzResearch.WordTrace]
  refine ⟨2359365189650161253391991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3145820252866881671189321 2359365189650161253391991)
  ·
    refine ⟨3539047784475241880087987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2359365189650161253391991 3539047784475241880087987)
    ·
      refine ⟨5308571676712862820131981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3539047784475241880087987 5308571676712862820131981)
      ·
        refine ⟨1990714378767323557549493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5308571676712862820131981 1990714378767323557549493)
        ·
          refine ⟨186629473009436583520265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1990714378767323557549493 186629473009436583520265)
          ·
            refine ⟨139972104757077437640199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186629473009436583520265 139972104757077437640199)
            ·
              refine ⟨209958157135616156460299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139972104757077437640199 209958157135616156460299)
              ·
                refine ⟨314937235703424234690449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209958157135616156460299 314937235703424234690449)
                ·
                  refine ⟨236202926777568176017837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314937235703424234690449 236202926777568176017837)
                  ·
                    refine ⟨88576097541588066006689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 236202926777568176017837 88576097541588066006689)
                    ·
                      refine ⟨66432073156191049505017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 88576097541588066006689 66432073156191049505017)
                      ·
                        rfl

theorem cell23_129376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_129376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129376 prefixEnd_129376 := by exact prefixLift 129376
  have htrace : WordTrace (prefixWord ++ tailWord_129376) baseStart_129376 baseEnd_129376 := by
    simpa [prefixWord, tailWord_129376, baseEnd_129376] using wordTrace_append hprefix tailTrace_129376
  have hstable : (prefixWord ++ tailWord_129376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129376).length < 2 ^ (prefixWord ++ tailWord_129376).sum := by decide
  have hdescent : baseEnd_129376 < baseStart_129376 := by decide
  rcases family_descends (prefixWord ++ tailWord_129376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129385 : List Nat := [1, 2, 1, 1, 1, 3, 3, 4, 1, 2, 4]
def baseStart_129385 : Nat := 118140960795 + 129385 * 2 ^ 59
def prefixEnd_129385 : Nat := 4983230072969 + 3 ^ 40 * 129385 * 2
def baseEnd_129385 : Nat := 66436694482081514292475

theorem tailTrace_129385 : CollatzResearch.WordTrace tailWord_129385 prefixEnd_129385 66436694482081514292475 := by
  unfold tailWord_129385
  simp only [CollatzResearch.WordTrace]
  refine ⟨4719058636267717043861609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3146039090845144695907739 4719058636267717043861609)
  ·
    refine ⟨3539293977200787782896207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4719058636267717043861609 3539293977200787782896207)
    ·
      refine ⟨5308940965801181674344311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3539293977200787782896207 5308940965801181674344311)
      ·
        refine ⟨7963411448701772511516467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5308940965801181674344311 7963411448701772511516467)
        ·
          refine ⟨11945117173052658767274701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7963411448701772511516467 11945117173052658767274701)
          ·
            refine ⟨4479418939894747037728013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11945117173052658767274701 4479418939894747037728013)
            ·
              refine ⟨1679782102460530139148005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4479418939894747037728013 1679782102460530139148005)
              ·
                refine ⟨314959144211349401090251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1679782102460530139148005 314959144211349401090251)
                ·
                  refine ⟨472438716317024101635377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314959144211349401090251 472438716317024101635377)
                  ·
                    refine ⟨354329037237768076226533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 472438716317024101635377 354329037237768076226533)
                    ·
                      refine ⟨66436694482081514292475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 354329037237768076226533 66436694482081514292475)
                      ·
                        rfl

theorem cell23_129385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 2, 4].length) (baseStart_129385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129385 prefixEnd_129385 := by exact prefixLift 129385
  have htrace : WordTrace (prefixWord ++ tailWord_129385) baseStart_129385 baseEnd_129385 := by
    simpa [prefixWord, tailWord_129385, baseEnd_129385] using wordTrace_append hprefix tailTrace_129385
  have hstable : (prefixWord ++ tailWord_129385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129385).length < 2 ^ (prefixWord ++ tailWord_129385).sum := by decide
  have hdescent : baseEnd_129385 < baseStart_129385 := by decide
  rcases family_descends (prefixWord ++ tailWord_129385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129386 : List Nat := [3, 1, 3, 3, 1, 3, 2, 1, 1, 5]
def baseStart_129386 : Nat := 118140960795 + 129386 * 2 ^ 59
def prefixEnd_129386 : Nat := 4983230072969 + 3 ^ 40 * 129386 * 2
def baseEnd_129386 : Nat := 22145735987578670126657

theorem tailTrace_129386 : CollatzResearch.WordTrace tailWord_129386 prefixEnd_129386 22145735987578670126657 := by
  unfold tailWord_129386
  simp only [CollatzResearch.WordTrace]
  refine ⟨1179773777316023553662003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3146063406176062809765341 1179773777316023553662003)
  ·
    refine ⟨1769660665974035330493005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1179773777316023553662003 1769660665974035330493005)
    ·
      refine ⟨663622749740263248934877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1769660665974035330493005 663622749740263248934877)
      ·
        refine ⟨248858531152598718350579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 663622749740263248934877 248858531152598718350579)
        ·
          refine ⟨373287796728898077525869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248858531152598718350579 373287796728898077525869)
          ·
            refine ⟨139982923773336779072201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373287796728898077525869 139982923773336779072201)
            ·
              refine ⟨104987192830002584304151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139982923773336779072201 104987192830002584304151)
              ·
                refine ⟨157480789245003876456227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104987192830002584304151 157480789245003876456227)
                ·
                  refine ⟨236221183867505814684341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157480789245003876456227 236221183867505814684341)
                  ·
                    refine ⟨22145735987578670126657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 236221183867505814684341 22145735987578670126657)
                    ·
                      rfl

theorem cell23_129386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_129386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129386 prefixEnd_129386 := by exact prefixLift 129386
  have htrace : WordTrace (prefixWord ++ tailWord_129386) baseStart_129386 baseEnd_129386 := by
    simpa [prefixWord, tailWord_129386, baseEnd_129386] using wordTrace_append hprefix tailTrace_129386
  have hstable : (prefixWord ++ tailWord_129386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129386).length < 2 ^ (prefixWord ++ tailWord_129386).sum := by decide
  have hdescent : baseEnd_129386 < baseStart_129386 := by decide
  rcases family_descends (prefixWord ++ tailWord_129386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129389 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 5, 2, 2]
def baseStart_129389 : Nat := 118140960795 + 129389 * 2 ^ 59
def prefixEnd_129389 : Nat := 4983230072969 + 3 ^ 40 * 129389 * 2
def baseEnd_129389 : Nat := 66438748404699498642457

theorem tailTrace_129389 : CollatzResearch.WordTrace tailWord_129389 prefixEnd_129389 66438748404699498642457 := by
  unfold tailWord_129389
  simp only [CollatzResearch.WordTrace]
  refine ⟨4719204528253225727007221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3146136352168817151338147 4719204528253225727007221)
  ·
    refine ⟨442425424523739911906927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4719204528253225727007221 442425424523739911906927)
    ·
      refine ⟨663638136785609867860391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442425424523739911906927 663638136785609867860391)
      ·
        refine ⟨995457205178414801790587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663638136785609867860391 995457205178414801790587)
        ·
          refine ⟨1493185807767622202685881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995457205178414801790587 1493185807767622202685881)
          ·
            refine ⟨1119889355825716652014411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1493185807767622202685881 1119889355825716652014411)
            ·
              refine ⟨1679834033738574978021617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119889355825716652014411 1679834033738574978021617)
              ·
                refine ⟨1259875525303931233516213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1679834033738574978021617 1259875525303931233516213)
                ·
                  refine ⟨118113330497243553142145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1259875525303931233516213 118113330497243553142145)
                  ·
                    refine ⟨88584997872932664856609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118113330497243553142145 88584997872932664856609)
                    ·
                      refine ⟨66438748404699498642457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 88584997872932664856609 66438748404699498642457)
                      ·
                        rfl

theorem cell23_129389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_129389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129389 prefixEnd_129389 := by exact prefixLift 129389
  have htrace : WordTrace (prefixWord ++ tailWord_129389) baseStart_129389 baseEnd_129389 := by
    simpa [prefixWord, tailWord_129389, baseEnd_129389] using wordTrace_append hprefix tailTrace_129389
  have hstable : (prefixWord ++ tailWord_129389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129389).length < 2 ^ (prefixWord ++ tailWord_129389).sum := by decide
  have hdescent : baseEnd_129389 < baseStart_129389 := by decide
  rcases family_descends (prefixWord ++ tailWord_129389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129475 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 4]
def baseStart_129475 : Nat := 118140960795 + 129475 * 2 ^ 59
def prefixEnd_129475 : Nat := 4983230072969 + 3 ^ 40 * 129475 * 2
def baseEnd_129475 : Nat := 66482907740986162167061

theorem tailTrace_129475 : CollatzResearch.WordTrace tailWord_129475 prefixEnd_129475 66482907740986162167061 := by
  unfold tailWord_129475
  simp only [CollatzResearch.WordTrace]
  refine ⟨4722341205941662414637879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3148227470627774943091919 4722341205941662414637879)
  ·
    refine ⟨7083511808912493621956819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4722341205941662414637879 7083511808912493621956819)
    ·
      refine ⟨10625267713368740432935229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7083511808912493621956819 10625267713368740432935229)
      ·
        refine ⟨3984475392513277662350711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10625267713368740432935229 3984475392513277662350711)
        ·
          refine ⟨5976713088769916493526067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3984475392513277662350711 5976713088769916493526067)
          ·
            refine ⟨8965069633154874740289101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5976713088769916493526067 8965069633154874740289101)
            ·
              refine ⟨3361901112433078027608413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8965069633154874740289101 3361901112433078027608413)
              ·
                refine ⟨1260712917162404260353155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3361901112433078027608413 1260712917162404260353155)
                ·
                  refine ⟨1891069375743606390529733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1260712917162404260353155 1891069375743606390529733)
                  ·
                    refine ⟨354575507951926198224325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1891069375743606390529733 354575507951926198224325)
                    ·
                      refine ⟨66482907740986162167061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 354575507951926198224325 66482907740986162167061)
                      ·
                        rfl

theorem cell23_129475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_129475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129475 prefixEnd_129475 := by exact prefixLift 129475
  have htrace : WordTrace (prefixWord ++ tailWord_129475) baseStart_129475 baseEnd_129475 := by
    simpa [prefixWord, tailWord_129475, baseEnd_129475] using wordTrace_append hprefix tailTrace_129475
  have hstable : (prefixWord ++ tailWord_129475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129475).length < 2 ^ (prefixWord ++ tailWord_129475).sum := by decide
  have hdescent : baseEnd_129475 < baseStart_129475 := by decide
  rcases family_descends (prefixWord ++ tailWord_129475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129545 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 1, 10]
def baseStart_129545 : Nat := 118140960795 + 129545 * 2 ^ 59
def prefixEnd_129545 : Nat := 4983230072969 + 3 ^ 40 * 129545 * 2
def baseEnd_129545 : Nat := 22172950462266962763913

theorem tailTrace_129545 : CollatzResearch.WordTrace tailWord_129545 prefixEnd_129545 22172950462266962763913 := by
  unfold tailWord_129545
  simp only [CollatzResearch.WordTrace]
  refine ⟨4724894315688064369686089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3149929543792042913124059 4724894315688064369686089)
  ·
    refine ⟨3543670736766048277264567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4724894315688064369686089 3543670736766048277264567)
    ·
      refine ⟨5315506105149072415896851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3543670736766048277264567 5315506105149072415896851)
      ·
        refine ⟨7973259157723608623845277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5315506105149072415896851 7973259157723608623845277)
        ·
          refine ⟨2989972184146353233941979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7973259157723608623845277 2989972184146353233941979)
          ·
            refine ⟨4484958276219529850912969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2989972184146353233941979 4484958276219529850912969)
            ·
              refine ⟨3363718707164647388184727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4484958276219529850912969 3363718707164647388184727)
              ·
                refine ⟨5045578060746971082277091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3363718707164647388184727 5045578060746971082277091)
                ·
                  refine ⟨7568367091120456623415637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5045578060746971082277091 7568367091120456623415637)
                  ·
                    refine ⟨22172950462266962763913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 7568367091120456623415637 22172950462266962763913)
                    ·
                      rfl

theorem cell23_129545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 10].length) (baseStart_129545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129545 prefixEnd_129545 := by exact prefixLift 129545
  have htrace : WordTrace (prefixWord ++ tailWord_129545) baseStart_129545 baseEnd_129545 := by
    simpa [prefixWord, tailWord_129545, baseEnd_129545] using wordTrace_append hprefix tailTrace_129545
  have hstable : (prefixWord ++ tailWord_129545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129545).length < 2 ^ (prefixWord ++ tailWord_129545).sum := by decide
  have hdescent : baseEnd_129545 < baseStart_129545 := by decide
  rcases family_descends (prefixWord ++ tailWord_129545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129569 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 4, 4, 2]
def baseStart_129569 : Nat := 118140960795 + 129569 * 2 ^ 59
def prefixEnd_129569 : Nat := 4983230072969 + 3 ^ 40 * 129569 * 2
def baseEnd_129569 : Nat := 66531174922508794391629

theorem tailTrace_129569 : CollatzResearch.WordTrace tailWord_129569 prefixEnd_129569 66531174922508794391629 := by
  unfold tailWord_129569
  simp only [CollatzResearch.WordTrace]
  refine ⟨4725769667601116468559761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3150513111734077645706507 4725769667601116468559761)
  ·
    refine ⟨3544327250700837351419821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4725769667601116468559761 3544327250700837351419821)
    ·
      refine ⟨1329122719012814006782433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3544327250700837351419821 1329122719012814006782433)
      ·
        refine ⟨996842039259610505086825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1329122719012814006782433 996842039259610505086825)
        ·
          refine ⟨747631529444707878815119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 996842039259610505086825 747631529444707878815119)
          ·
            refine ⟨1121447294167061818222679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747631529444707878815119 1121447294167061818222679)
            ·
              refine ⟨1682170941250592727334019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121447294167061818222679 1682170941250592727334019)
              ·
                refine ⟨2523256411875889091001029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682170941250592727334019 2523256411875889091001029)
                ·
                  refine ⟨473110577226729204562693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2523256411875889091001029 473110577226729204562693)
                  ·
                    refine ⟨88708233230011725855505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 473110577226729204562693 88708233230011725855505)
                    ·
                      refine ⟨66531174922508794391629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 88708233230011725855505 66531174922508794391629)
                      ·
                        rfl

theorem cell23_129569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_129569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129569 prefixEnd_129569 := by exact prefixLift 129569
  have htrace : WordTrace (prefixWord ++ tailWord_129569) baseStart_129569 baseEnd_129569 := by
    simpa [prefixWord, tailWord_129569, baseEnd_129569] using wordTrace_append hprefix tailTrace_129569
  have hstable : (prefixWord ++ tailWord_129569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129569).length < 2 ^ (prefixWord ++ tailWord_129569).sum := by decide
  have hdescent : baseEnd_129569 < baseStart_129569 := by decide
  rcases family_descends (prefixWord ++ tailWord_129569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129659 : List Nat := [1, 1, 1, 1, 1, 4, 2, 6, 1, 1, 4]
def baseStart_129659 : Nat := 118140960795 + 129659 * 2 ^ 59
def prefixEnd_129659 : Nat := 4983230072969 + 3 ^ 40 * 129659 * 2
def baseEnd_129659 : Nat := 66577388181413442266215

theorem tailTrace_129659 : CollatzResearch.WordTrace tailWord_129659 prefixEnd_129659 66577388181413442266215 := by
  unfold tailWord_129659
  simp only [CollatzResearch.WordTrace]
  refine ⟨4729052237275061839336031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3152701491516707892890687 4729052237275061839336031)
  ·
    refine ⟨7093578355912592759004047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4729052237275061839336031 7093578355912592759004047)
    ·
      refine ⟨10640367533868889138506071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7093578355912592759004047 10640367533868889138506071)
      ·
        refine ⟨15960551300803333707759107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10640367533868889138506071 15960551300803333707759107)
        ·
          refine ⟨23940826951205000561638661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15960551300803333707759107 23940826951205000561638661)
          ·
            refine ⟨4488905053350937605307249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23940826951205000561638661 4488905053350937605307249)
            ·
              refine ⟨3366678790013203203980437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4488905053350937605307249 3366678790013203203980437)
              ·
                refine ⟨157813068281868900186583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3366678790013203203980437 157813068281868900186583)
                ·
                  refine ⟨236719602422803350279875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157813068281868900186583 236719602422803350279875)
                  ·
                    refine ⟨355079403634205025419813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 236719602422803350279875 355079403634205025419813)
                    ·
                      refine ⟨66577388181413442266215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 355079403634205025419813 66577388181413442266215)
                      ·
                        rfl

theorem cell23_129659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 1, 1, 4].length) (baseStart_129659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129659 prefixEnd_129659 := by exact prefixLift 129659
  have htrace : WordTrace (prefixWord ++ tailWord_129659) baseStart_129659 baseEnd_129659 := by
    simpa [prefixWord, tailWord_129659, baseEnd_129659] using wordTrace_append hprefix tailTrace_129659
  have hstable : (prefixWord ++ tailWord_129659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129659).length < 2 ^ (prefixWord ++ tailWord_129659).sum := by decide
  have hdescent : baseEnd_129659 < baseStart_129659 := by decide
  rcases family_descends (prefixWord ++ tailWord_129659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129669 : List Nat := [1, 3, 1, 1, 4, 3, 1, 2, 1, 6]
def baseStart_129669 : Nat := 118140960795 + 129669 * 2 ^ 59
def prefixEnd_129669 : Nat := 4983230072969 + 3 ^ 40 * 129669 * 2
def baseEnd_129669 : Nat := 22194174329319467713723

theorem tailTrace_129669 : CollatzResearch.WordTrace tailWord_129669 prefixEnd_129669 22194174329319467713723 := by
  unfold tailWord_129669
  simp only [CollatzResearch.WordTrace]
  refine ⟨4729416967238833547200061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3152944644825889031466707 4729416967238833547200061)
  ·
    refine ⟨1773531362714562580200023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4729416967238833547200061 1773531362714562580200023)
    ·
      refine ⟨2660297044071843870300035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1773531362714562580200023 2660297044071843870300035)
      ·
        refine ⟨3990445566107765805450053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2660297044071843870300035 3990445566107765805450053)
        ·
          refine ⟨748208543645206088521885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3990445566107765805450053 748208543645206088521885)
          ·
            refine ⟨280578203866952283195707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 748208543645206088521885 280578203866952283195707)
            ·
              refine ⟨420867305800428424793561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280578203866952283195707 420867305800428424793561)
              ·
                refine ⟨315650479350321318595171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420867305800428424793561 315650479350321318595171)
                ·
                  refine ⟨473475719025481977892757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315650479350321318595171 473475719025481977892757)
                  ·
                    refine ⟨22194174329319467713723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 473475719025481977892757 22194174329319467713723)
                    ·
                      rfl

theorem cell23_129669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_129669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129669 prefixEnd_129669 := by exact prefixLift 129669
  have htrace : WordTrace (prefixWord ++ tailWord_129669) baseStart_129669 baseEnd_129669 := by
    simpa [prefixWord, tailWord_129669, baseEnd_129669] using wordTrace_append hprefix tailTrace_129669
  have hstable : (prefixWord ++ tailWord_129669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129669).length < 2 ^ (prefixWord ++ tailWord_129669).sum := by decide
  have hdescent : baseEnd_129669 < baseStart_129669 := by decide
  rcases family_descends (prefixWord ++ tailWord_129669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129676 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 7, 2, 2]
def baseStart_129676 : Nat := 118140960795 + 129676 * 2 ^ 59
def prefixEnd_129676 : Nat := 4983230072969 + 3 ^ 40 * 129676 * 2
def baseEnd_129676 : Nat := 66586117352539875753637

theorem tailTrace_129676 : CollatzResearch.WordTrace tailWord_129676 prefixEnd_129676 66586117352539875753637 := by
  unfold tailWord_129676
  simp only [CollatzResearch.WordTrace]
  refine ⟨2364836139106736871352441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3153114852142315828469921 2364836139106736871352441)
  ·
    refine ⟨1773627104330052653514331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2364836139106736871352441 1773627104330052653514331)
    ·
      refine ⟨2660440656495078980271497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1773627104330052653514331 2660440656495078980271497)
      ·
        refine ⟨1995330492371309235203623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2660440656495078980271497 1995330492371309235203623)
        ·
          refine ⟨2992995738556963852805435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1995330492371309235203623 2992995738556963852805435)
          ·
            refine ⟨4489493607835445779208153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2992995738556963852805435 4489493607835445779208153)
            ·
              refine ⟨3367120205876584334406115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4489493607835445779208153 3367120205876584334406115)
              ·
                refine ⟨5050680308814876501609173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3367120205876584334406115 5050680308814876501609173)
                ·
                  refine ⟨118375319737848668006465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5050680308814876501609173 118375319737848668006465)
                  ·
                    refine ⟨88781489803386501004849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118375319737848668006465 88781489803386501004849)
                    ·
                      refine ⟨66586117352539875753637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 88781489803386501004849 66586117352539875753637)
                      ·
                        rfl

theorem cell23_129676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_129676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129676 prefixEnd_129676 := by exact prefixLift 129676
  have htrace : WordTrace (prefixWord ++ tailWord_129676) baseStart_129676 baseEnd_129676 := by
    simpa [prefixWord, tailWord_129676, baseEnd_129676] using wordTrace_append hprefix tailTrace_129676
  have hstable : (prefixWord ++ tailWord_129676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129676).length < 2 ^ (prefixWord ++ tailWord_129676).sum := by decide
  have hdescent : baseEnd_129676 < baseStart_129676 := by decide
  rcases family_descends (prefixWord ++ tailWord_129676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129703 : List Nat := [1, 1, 6, 3, 1, 1, 2, 1, 1, 6]
def baseStart_129703 : Nat := 118140960795 + 129703 * 2 ^ 59
def prefixEnd_129703 : Nat := 4983230072969 + 3 ^ 40 * 129703 * 2
def baseEnd_129703 : Nat := 22199993776737090038671

theorem tailTrace_129703 : CollatzResearch.WordTrace tailWord_129703 prefixEnd_129703 22199993776737090038671 := by
  unfold tailWord_129703
  simp only [CollatzResearch.WordTrace]
  refine ⟨4730657049115657353937763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3153771366077104902625175 4730657049115657353937763)
  ·
    refine ⟨7095985573673486030906645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4730657049115657353937763 7095985573673486030906645)
    ·
      refine ⟨332624323765944657698749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7095985573673486030906645 332624323765944657698749)
      ·
        refine ⟨124734121412229246637031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332624323765944657698749 124734121412229246637031)
        ·
          refine ⟨187101182118343869955547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124734121412229246637031 187101182118343869955547)
          ·
            refine ⟨280651773177515804933321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187101182118343869955547 280651773177515804933321)
            ·
              refine ⟨210488829883136853699991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280651773177515804933321 210488829883136853699991)
              ·
                refine ⟨315733244824705280549987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210488829883136853699991 315733244824705280549987)
                ·
                  refine ⟨473599867237057920824981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315733244824705280549987 473599867237057920824981)
                  ·
                    refine ⟨22199993776737090038671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 473599867237057920824981 22199993776737090038671)
                    ·
                      rfl

theorem cell23_129703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_129703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129703 prefixEnd_129703 := by exact prefixLift 129703
  have htrace : WordTrace (prefixWord ++ tailWord_129703) baseStart_129703 baseEnd_129703 := by
    simpa [prefixWord, tailWord_129703, baseEnd_129703] using wordTrace_append hprefix tailTrace_129703
  have hstable : (prefixWord ++ tailWord_129703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129703).length < 2 ^ (prefixWord ++ tailWord_129703).sum := by decide
  have hdescent : baseEnd_129703 < baseStart_129703 := by decide
  rcases family_descends (prefixWord ++ tailWord_129703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129710 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_129710 : Nat := 118140960795 + 129710 * 2 ^ 59
def prefixEnd_129710 : Nat := 4983230072969 + 3 ^ 40 * 129710 * 2
def baseEnd_129710 : Nat := 66603575694792742728481

theorem tailTrace_129710 : CollatzResearch.WordTrace tailWord_129710 prefixEnd_129710 66603575694792742728481 := by
  unfold tailWord_129710
  simp only [CollatzResearch.WordTrace]
  refine ⟨591364045011287193680323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3153941573393531699628389 591364045011287193680323)
  ·
    refine ⟨887046067516930790520485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 591364045011287193680323 887046067516930790520485)
    ·
      refine ⟨166321137659424523222591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 887046067516930790520485 166321137659424523222591)
      ·
        refine ⟨249481706489136784833887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166321137659424523222591 249481706489136784833887)
        ·
          refine ⟨374222559733705177250831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249481706489136784833887 374222559733705177250831)
          ·
            refine ⟨561333839600557765876247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374222559733705177250831 561333839600557765876247)
            ·
              refine ⟨842000759400836648814371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561333839600557765876247 842000759400836648814371)
              ·
                refine ⟨1263001139101254973221557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842000759400836648814371 1263001139101254973221557)
                ·
                  refine ⟨118406356790742653739521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1263001139101254973221557 118406356790742653739521)
                  ·
                    refine ⟨88804767593056990304641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118406356790742653739521 88804767593056990304641)
                    ·
                      refine ⟨66603575694792742728481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 88804767593056990304641 66603575694792742728481)
                      ·
                        rfl

theorem cell23_129710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_129710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129710 prefixEnd_129710 := by exact prefixLift 129710
  have htrace : WordTrace (prefixWord ++ tailWord_129710) baseStart_129710 baseEnd_129710 := by
    simpa [prefixWord, tailWord_129710, baseEnd_129710] using wordTrace_append hprefix tailTrace_129710
  have hstable : (prefixWord ++ tailWord_129710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129710).length < 2 ^ (prefixWord ++ tailWord_129710).sum := by decide
  have hdescent : baseEnd_129710 < baseStart_129710 := by decide
  rcases family_descends (prefixWord ++ tailWord_129710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129712 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 4, 7]
def baseStart_129712 : Nat := 118140960795 + 129712 * 2 ^ 59
def prefixEnd_129712 : Nat := 4983230072969 + 3 ^ 40 * 129712 * 2
def baseEnd_129712 : Nat := 22201534218700578301157

theorem tailTrace_129712 : CollatzResearch.WordTrace tailWord_129712 prefixEnd_129712 22201534218700578301157 := by
  unfold tailWord_129712
  simp only [CollatzResearch.WordTrace]
  refine ⟨2365492653041525945507695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3153990204055367927343593 2365492653041525945507695)
  ·
    refine ⟨3548238979562288918261543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2365492653041525945507695 3548238979562288918261543)
    ·
      refine ⟨5322358469343433377392315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3548238979562288918261543 5322358469343433377392315)
      ·
        refine ⟨7983537704015150066088473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5322358469343433377392315 7983537704015150066088473)
        ·
          refine ⟨5987653278011362549566355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7983537704015150066088473 5987653278011362549566355)
          ·
            refine ⟨8981479917017043824349533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5987653278011362549566355 8981479917017043824349533)
            ·
              refine ⟨3368054968881391434131075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8981479917017043824349533 3368054968881391434131075)
              ·
                refine ⟨5052082453322087151196613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368054968881391434131075 5052082453322087151196613)
                ·
                  refine ⟨947265459997891340849365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5052082453322087151196613 947265459997891340849365)
                  ·
                    refine ⟨22201534218700578301157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 947265459997891340849365 22201534218700578301157)
                    ·
                      rfl

theorem cell23_129712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 4, 7].length) (baseStart_129712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129712 prefixEnd_129712 := by exact prefixLift 129712
  have htrace : WordTrace (prefixWord ++ tailWord_129712) baseStart_129712 baseEnd_129712 := by
    simpa [prefixWord, tailWord_129712, baseEnd_129712] using wordTrace_append hprefix tailTrace_129712
  have hstable : (prefixWord ++ tailWord_129712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129712).length < 2 ^ (prefixWord ++ tailWord_129712).sum := by decide
  have hdescent : baseEnd_129712 < baseStart_129712 := by decide
  rcases family_descends (prefixWord ++ tailWord_129712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129726 : List Nat := [4, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_129726 : Nat := 118140960795 + 129726 * 2 ^ 59
def prefixEnd_129726 : Nat := 4983230072969 + 3 ^ 40 * 129726 * 2
def baseEnd_129726 : Nat := 66611791385264680128407

theorem tailTrace_129726 : CollatzResearch.WordTrace tailWord_129726 prefixEnd_129726 66611791385264680128407 := by
  unfold tailWord_129726
  simp only [CollatzResearch.WordTrace]
  refine ⟨591436991004041535253129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3154330618688221521350021 591436991004041535253129)
  ·
    refine ⟨443577743253031151439847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 591436991004041535253129 443577743253031151439847)
    ·
      refine ⟨665366614879546727159771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443577743253031151439847 665366614879546727159771)
      ·
        refine ⟨998049922319320090739657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665366614879546727159771 998049922319320090739657)
        ·
          refine ⟨748537441739490068054743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 998049922319320090739657 748537441739490068054743)
          ·
            refine ⟨1122806162609235102082115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748537441739490068054743 1122806162609235102082115)
            ·
              refine ⟨1684209243913852653123173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122806162609235102082115 1684209243913852653123173)
              ·
                refine ⟨315789233233847372460595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1684209243913852653123173 315789233233847372460595)
                ·
                  refine ⟨473683849850771058690893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315789233233847372460595 473683849850771058690893)
                  ·
                    refine ⟨177631443694039147009085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 473683849850771058690893 177631443694039147009085)
                    ·
                      refine ⟨66611791385264680128407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 177631443694039147009085 66611791385264680128407)
                      ·
                        rfl

theorem cell23_129726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_129726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129726 prefixEnd_129726 := by exact prefixLift 129726
  have htrace : WordTrace (prefixWord ++ tailWord_129726) baseStart_129726 baseEnd_129726 := by
    simpa [prefixWord, tailWord_129726, baseEnd_129726] using wordTrace_append hprefix tailTrace_129726
  have hstable : (prefixWord ++ tailWord_129726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129726).length < 2 ^ (prefixWord ++ tailWord_129726).sum := by decide
  have hdescent : baseEnd_129726 < baseStart_129726 := by decide
  rcases family_descends (prefixWord ++ tailWord_129726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129759 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 2, 6]
def baseStart_129759 : Nat := 118140960795 + 129759 * 2 ^ 59
def prefixEnd_129759 : Nat := 4983230072969 + 3 ^ 40 * 129759 * 2
def baseEnd_129759 : Nat := 22209578748954350338585

theorem tailTrace_129759 : CollatzResearch.WordTrace tailWord_129759 prefixEnd_129759 22209578748954350338585 := by
  unfold tailWord_129759
  simp only [CollatzResearch.WordTrace]
  refine ⟨4732699536912778917976331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3155133024608519278650887 4732699536912778917976331)
  ·
    refine ⟨7099049305369168376964497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4732699536912778917976331 7099049305369168376964497)
    ·
      refine ⟨5324286979026876282723373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7099049305369168376964497 5324286979026876282723373)
      ·
        refine ⟨1996607617135078606021265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5324286979026876282723373 1996607617135078606021265)
        ·
          refine ⟨1497455712851308954515949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1996607617135078606021265 1497455712851308954515949)
          ·
            refine ⟨561545892319240857943481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1497455712851308954515949 561545892319240857943481)
            ·
              refine ⟨421159419239430643457611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561545892319240857943481 421159419239430643457611)
              ·
                refine ⟨631739128859145965186417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421159419239430643457611 631739128859145965186417)
                ·
                  refine ⟨473804346644359473889813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631739128859145965186417 473804346644359473889813)
                  ·
                    refine ⟨22209578748954350338585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 473804346644359473889813 22209578748954350338585)
                    ·
                      rfl

theorem cell23_129759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 6].length) (baseStart_129759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129759 prefixEnd_129759 := by exact prefixLift 129759
  have htrace : WordTrace (prefixWord ++ tailWord_129759) baseStart_129759 baseEnd_129759 := by
    simpa [prefixWord, tailWord_129759, baseEnd_129759] using wordTrace_append hprefix tailTrace_129759
  have hstable : (prefixWord ++ tailWord_129759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129759).length < 2 ^ (prefixWord ++ tailWord_129759).sum := by decide
  have hdescent : baseEnd_129759 < baseStart_129759 := by decide
  rcases family_descends (prefixWord ++ tailWord_129759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129769 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 2, 4, 3]
def baseStart_129769 : Nat := 118140960795 + 129769 * 2 ^ 59
def prefixEnd_129769 : Nat := 4983230072969 + 3 ^ 40 * 129769 * 2
def baseEnd_129769 : Nat := 66633871053408011890709

theorem tailTrace_129769 : CollatzResearch.WordTrace tailWord_129769 prefixEnd_129769 66633871053408011890709 := by
  unfold tailWord_129769
  simp only [CollatzResearch.WordTrace]
  refine ⟨4733064266876550625840361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3155376177917700417226907 4733064266876550625840361)
  ·
    refine ⟨3549798200157412969380271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4733064266876550625840361 3549798200157412969380271)
    ·
      refine ⟨5324697300236119454070407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3549798200157412969380271 5324697300236119454070407)
      ·
        refine ⟨7987045950354179181105611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5324697300236119454070407 7987045950354179181105611)
        ·
          refine ⟨11980568925531268771658417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7987045950354179181105611 11980568925531268771658417)
          ·
            refine ⟨8985426694148451578743813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11980568925531268771658417 8985426694148451578743813)
            ·
              refine ⟨1684767505152834671014465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8985426694148451578743813 1684767505152834671014465)
              ·
                refine ⟨1263575628864626003260849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1684767505152834671014465 1263575628864626003260849)
                ·
                  refine ⟨947681721648469502445637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1263575628864626003260849 947681721648469502445637)
                  ·
                    refine ⟨177690322809088031708557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 947681721648469502445637 177690322809088031708557)
                    ·
                      refine ⟨66633871053408011890709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 177690322809088031708557 66633871053408011890709)
                      ·
                        rfl

theorem cell23_129769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 4, 3].length) (baseStart_129769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129769 prefixEnd_129769 := by exact prefixLift 129769
  have htrace : WordTrace (prefixWord ++ tailWord_129769) baseStart_129769 baseEnd_129769 := by
    simpa [prefixWord, tailWord_129769, baseEnd_129769] using wordTrace_append hprefix tailTrace_129769
  have hstable : (prefixWord ++ tailWord_129769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129769).length < 2 ^ (prefixWord ++ tailWord_129769).sum := by decide
  have hdescent : baseEnd_129769 < baseStart_129769 := by decide
  rcases family_descends (prefixWord ++ tailWord_129769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129829 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 1, 1, 7]
def baseStart_129829 : Nat := 118140960795 + 129829 * 2 ^ 59
def prefixEnd_129829 : Nat := 4983230072969 + 3 ^ 40 * 129829 * 2
def baseEnd_129829 : Nat := 66664679892677777140433

theorem tailTrace_129829 : CollatzResearch.WordTrace tailWord_129829 prefixEnd_129829 66664679892677777140433 := by
  unfold tailWord_129829
  simp only [CollatzResearch.WordTrace]
  refine ⟨4735252646659180873024541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3156835097772787248683027 4735252646659180873024541)
  ·
    refine ⟨1775719742497192827384203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4735252646659180873024541 1775719742497192827384203)
    ·
      refine ⟨2663579613745789241076305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1775719742497192827384203 2663579613745789241076305)
      ·
        refine ⟨1997684710309341930807229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2663579613745789241076305 1997684710309341930807229)
        ·
          refine ⟨749131766366003224052711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1997684710309341930807229 749131766366003224052711)
          ·
            refine ⟨1123697649549004836079067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749131766366003224052711 1123697649549004836079067)
            ·
              refine ⟨1685546474323507254118601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123697649549004836079067 1685546474323507254118601)
              ·
                refine ⟨1264159855742630440588951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1685546474323507254118601 1264159855742630440588951)
                ·
                  refine ⟨1896239783613945660883427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1264159855742630440588951 1896239783613945660883427)
                  ·
                    refine ⟨2844359675420918491325141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1896239783613945660883427 2844359675420918491325141)
                    ·
                      refine ⟨66664679892677777140433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2844359675420918491325141 66664679892677777140433)
                      ·
                        rfl

theorem cell23_129829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_129829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129829 prefixEnd_129829 := by exact prefixLift 129829
  have htrace : WordTrace (prefixWord ++ tailWord_129829) baseStart_129829 baseEnd_129829 := by
    simpa [prefixWord, tailWord_129829, baseEnd_129829] using wordTrace_append hprefix tailTrace_129829
  have hstable : (prefixWord ++ tailWord_129829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129829).length < 2 ^ (prefixWord ++ tailWord_129829).sum := by decide
  have hdescent : baseEnd_129829 < baseStart_129829 := by decide
  rcases family_descends (prefixWord ++ tailWord_129829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129836 : List Nat := [2, 2, 1, 1, 1, 4, 4, 1, 2, 5]
def baseStart_129836 : Nat := 118140960795 + 129836 * 2 ^ 59
def prefixEnd_129836 : Nat := 4983230072969 + 3 ^ 40 * 129836 * 2
def baseEnd_129836 : Nat := 22222758085753083250967

theorem tailTrace_129836 : CollatzResearch.WordTrace tailWord_129836 prefixEnd_129836 22222758085753083250967 := by
  unfold tailWord_129836
  simp only [CollatzResearch.WordTrace]
  refine ⟨2367753978816910534264681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3157005305089214045686241 2367753978816910534264681)
  ·
    refine ⟨1775815484112682900698511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2367753978816910534264681 1775815484112682900698511)
    ·
      refine ⟨2663723226169024351047767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1775815484112682900698511 2663723226169024351047767)
      ·
        refine ⟨3995584839253536526571651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2663723226169024351047767 3995584839253536526571651)
        ·
          refine ⟨5993377258880304789857477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3995584839253536526571651 5993377258880304789857477)
          ·
            refine ⟨1123758236040057148098277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5993377258880304789857477 1123758236040057148098277)
            ·
              refine ⟨210704669257510715268427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1123758236040057148098277 210704669257510715268427)
              ·
                refine ⟨316057003886266072902641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210704669257510715268427 316057003886266072902641)
                ·
                  refine ⟨237042752914699554676981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316057003886266072902641 237042752914699554676981)
                  ·
                    refine ⟨22222758085753083250967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 237042752914699554676981 22222758085753083250967)
                    ·
                      rfl

theorem cell23_129836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_129836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129836 prefixEnd_129836 := by exact prefixLift 129836
  have htrace : WordTrace (prefixWord ++ tailWord_129836) baseStart_129836 baseEnd_129836 := by
    simpa [prefixWord, tailWord_129836, baseEnd_129836] using wordTrace_append hprefix tailTrace_129836
  have hstable : (prefixWord ++ tailWord_129836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129836).length < 2 ^ (prefixWord ++ tailWord_129836).sum := by decide
  have hdescent : baseEnd_129836 < baseStart_129836 := by decide
  rcases family_descends (prefixWord ++ tailWord_129836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129856 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 3, 6, 2]
def baseStart_129856 : Nat := 118140960795 + 129856 * 2 ^ 59
def prefixEnd_129856 : Nat := 4983230072969 + 3 ^ 40 * 129856 * 2
def baseEnd_129856 : Nat := 66678543870349171502809

theorem tailTrace_129856 : CollatzResearch.WordTrace tailWord_129856 prefixEnd_129856 66678543870349171502809 := by
  unfold tailWord_129856
  simp only [CollatzResearch.WordTrace]
  refine ⟨2368118708780682242128711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3157491611707576322838281 2368118708780682242128711)
  ·
    refine ⟨3552178063171023363193067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2368118708780682242128711 3552178063171023363193067)
    ·
      refine ⟨5328267094756535044789601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3552178063171023363193067 5328267094756535044789601)
      ·
        refine ⟨3996200321067401283592201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5328267094756535044789601 3996200321067401283592201)
        ·
          refine ⟨2997150240800550962694151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3996200321067401283592201 2997150240800550962694151)
          ·
            refine ⟨4495725361200826444041227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2997150240800550962694151 4495725361200826444041227)
            ·
              refine ⟨6743588041801239666061841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4495725361200826444041227 6743588041801239666061841)
              ·
                refine ⟨5057691031350929749546381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6743588041801239666061841 5057691031350929749546381)
                ·
                  refine ⟨1896634136756598656079893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5057691031350929749546381 1896634136756598656079893)
                  ·
                    refine ⟨88904725160465562003745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1896634136756598656079893 88904725160465562003745)
                    ·
                      refine ⟨66678543870349171502809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 88904725160465562003745 66678543870349171502809)
                      ·
                        rfl

theorem cell23_129856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 6, 2].length) (baseStart_129856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129856 prefixEnd_129856 := by exact prefixLift 129856
  have htrace : WordTrace (prefixWord ++ tailWord_129856) baseStart_129856 baseEnd_129856 := by
    simpa [prefixWord, tailWord_129856, baseEnd_129856] using wordTrace_append hprefix tailTrace_129856
  have hstable : (prefixWord ++ tailWord_129856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129856).length < 2 ^ (prefixWord ++ tailWord_129856).sum := by decide
  have hdescent : baseEnd_129856 < baseStart_129856 := by decide
  rcases family_descends (prefixWord ++ tailWord_129856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129859 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 5]
def baseStart_129859 : Nat := 118140960795 + 129859 * 2 ^ 59
def prefixEnd_129859 : Nat := 4983230072969 + 3 ^ 40 * 129859 * 2
def baseEnd_129859 : Nat := 66680084312312659765295

theorem tailTrace_129859 : CollatzResearch.WordTrace tailWord_129859 prefixEnd_129859 66680084312312659765295 := by
  unfold tailWord_129859
  simp only [CollatzResearch.WordTrace]
  refine ⟨4736346836550495996616631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3157564557700330664411087 4736346836550495996616631)
  ·
    refine ⟨7104520254825743994924947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4736346836550495996616631 7104520254825743994924947)
    ·
      refine ⟨10656780382238615992387421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7104520254825743994924947 10656780382238615992387421)
      ·
        refine ⟨3996292643339480997145283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10656780382238615992387421 3996292643339480997145283)
        ·
          refine ⟨5994438965009221495717925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3996292643339480997145283 5994438965009221495717925)
          ·
            refine ⟨1123957305939229030447111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5994438965009221495717925 1123957305939229030447111)
            ·
              refine ⟨1685935958908843545670667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123957305939229030447111 1685935958908843545670667)
              ·
                refine ⟨2528903938363265318506001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1685935958908843545670667 2528903938363265318506001)
                ·
                  refine ⟨1896677953772448988879501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2528903938363265318506001 1896677953772448988879501)
                  ·
                    refine ⟨711254232664668370829813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1896677953772448988879501 711254232664668370829813)
                    ·
                      refine ⟨66680084312312659765295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 711254232664668370829813 66680084312312659765295)
                      ·
                        rfl

theorem cell23_129859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_129859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129859 prefixEnd_129859 := by exact prefixLift 129859
  have htrace : WordTrace (prefixWord ++ tailWord_129859) baseStart_129859 baseEnd_129859 := by
    simpa [prefixWord, tailWord_129859, baseEnd_129859] using wordTrace_append hprefix tailTrace_129859
  have hstable : (prefixWord ++ tailWord_129859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129859).length < 2 ^ (prefixWord ++ tailWord_129859).sum := by decide
  have hdescent : baseEnd_129859 < baseStart_129859 := by decide
  rcases family_descends (prefixWord ++ tailWord_129859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129893 : List Nat := [1, 3, 1, 3, 1, 1, 5, 1, 2, 2, 3]
def baseStart_129893 : Nat := 118140960795 + 129893 * 2 ^ 59
def prefixEnd_129893 : Nat := 4983230072969 + 3 ^ 40 * 129893 * 2
def baseEnd_129893 : Nat := 66697542654565526740139

theorem tailTrace_129893 : CollatzResearch.WordTrace tailWord_129893 prefixEnd_129893 66697542654565526740139 := by
  unfold tailWord_129893
  simp only [CollatzResearch.WordTrace]
  refine ⟨4737586918427319803354333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3158391278951546535569555 4737586918427319803354333)
  ·
    refine ⟨1776595094410244926257875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4737586918427319803354333 1776595094410244926257875)
    ·
      refine ⟨2664892641615367389386813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1776595094410244926257875 2664892641615367389386813)
      ·
        refine ⟨999334740605762771020055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2664892641615367389386813 999334740605762771020055)
        ·
          refine ⟨1499002110908644156530083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999334740605762771020055 1499002110908644156530083)
          ·
            refine ⟨2248503166362966234795125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499002110908644156530083 2248503166362966234795125)
            ·
              refine ⟨210797171846528084512043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2248503166362966234795125 210797171846528084512043)
              ·
                refine ⟨316195757769792126768065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210797171846528084512043 316195757769792126768065)
                ·
                  refine ⟨237146818327344095076049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316195757769792126768065 237146818327344095076049)
                  ·
                    refine ⟨177860113745508071307037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 237146818327344095076049 177860113745508071307037)
                    ·
                      refine ⟨66697542654565526740139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 177860113745508071307037 66697542654565526740139)
                      ·
                        rfl

theorem cell23_129893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_129893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129893 prefixEnd_129893 := by exact prefixLift 129893
  have htrace : WordTrace (prefixWord ++ tailWord_129893) baseStart_129893 baseEnd_129893 := by
    simpa [prefixWord, tailWord_129893, baseEnd_129893] using wordTrace_append hprefix tailTrace_129893
  have hstable : (prefixWord ++ tailWord_129893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129893).length < 2 ^ (prefixWord ++ tailWord_129893).sum := by decide
  have hdescent : baseEnd_129893 < baseStart_129893 := by decide
  rcases family_descends (prefixWord ++ tailWord_129893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129900 : List Nat := [2, 2, 1, 1, 4, 1, 4, 3, 1, 4]
def baseStart_129900 : Nat := 118140960795 + 129900 * 2 ^ 59
def prefixEnd_129900 : Nat := 4983230072969 + 3 ^ 40 * 129900 * 2
def baseEnd_129900 : Nat := 22233712339715666450869

theorem tailTrace_129900 : CollatzResearch.WordTrace tailWord_129900 prefixEnd_129900 22233712339715666450869 := by
  unfold tailWord_129900
  simp only [CollatzResearch.WordTrace]
  refine ⟨2368921114700979999429577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3158561486267973332572769 2368921114700979999429577)
  ·
    refine ⟨1776690836025734999572183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2368921114700979999429577 1776690836025734999572183)
    ·
      refine ⟨2665036254038602499358275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1776690836025734999572183 2665036254038602499358275)
      ·
        refine ⟨3997554381057903749037413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2665036254038602499358275 3997554381057903749037413)
        ·
          refine ⟨749541446448356952944515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3997554381057903749037413 749541446448356952944515)
          ·
            refine ⟨1124312169672535429416773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749541446448356952944515 1124312169672535429416773)
            ·
              refine ⟨210808531813600393015645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1124312169672535429416773 210808531813600393015645)
              ·
                refine ⟨79053199430100147380867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210808531813600393015645 79053199430100147380867)
                ·
                  refine ⟨118579799145150221071301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79053199430100147380867 118579799145150221071301)
                  ·
                    refine ⟨22233712339715666450869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118579799145150221071301 22233712339715666450869)
                    ·
                      rfl

theorem cell23_129900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 1, 4].length) (baseStart_129900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129900 prefixEnd_129900 := by exact prefixLift 129900
  have htrace : WordTrace (prefixWord ++ tailWord_129900) baseStart_129900 baseEnd_129900 := by
    simpa [prefixWord, tailWord_129900, baseEnd_129900] using wordTrace_append hprefix tailTrace_129900
  have hstable : (prefixWord ++ tailWord_129900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129900).length < 2 ^ (prefixWord ++ tailWord_129900).sum := by decide
  have hdescent : baseEnd_129900 < baseStart_129900 := by decide
  rcases family_descends (prefixWord ++ tailWord_129900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129913 : List Nat := [1, 2, 1, 3, 2, 5, 1, 2, 6]
def baseStart_129913 : Nat := 118140960795 + 129913 * 2 ^ 59
def prefixEnd_129913 : Nat := 4983230072969 + 3 ^ 40 * 129913 * 2
def baseEnd_129913 : Nat := 7411979140850605387783

theorem tailTrace_129913 : CollatzResearch.WordTrace tailWord_129913 prefixEnd_129913 7411979140850605387783 := by
  unfold tailWord_129913
  simp only [CollatzResearch.WordTrace]
  refine ⟨4738316378354863219082393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3158877585569908812721595 4738316378354863219082393)
  ·
    refine ⟨3553737283766147414311795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4738316378354863219082393 3553737283766147414311795)
    ·
      refine ⟨5330605925649221121467693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3553737283766147414311795 5330605925649221121467693)
      ·
        refine ⟨1998977222118457920550385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5330605925649221121467693 1998977222118457920550385)
        ·
          refine ⟨1499232916588843440412789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1998977222118457920550385 1499232916588843440412789)
          ·
            refine ⟨140553085930204072538699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1499232916588843440412789 140553085930204072538699)
            ·
              refine ⟨210829628895306108808049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140553085930204072538699 210829628895306108808049)
              ·
                refine ⟨158122221671479581606037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210829628895306108808049 158122221671479581606037)
                ·
                  refine ⟨7411979140850605387783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158122221671479581606037 7411979140850605387783)
                  ·
                    rfl

theorem cell23_129913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 6].length) (baseStart_129913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129913 prefixEnd_129913 := by exact prefixLift 129913
  have htrace : WordTrace (prefixWord ++ tailWord_129913) baseStart_129913 baseEnd_129913 := by
    simpa [prefixWord, tailWord_129913, baseEnd_129913] using wordTrace_append hprefix tailTrace_129913
  have hstable : (prefixWord ++ tailWord_129913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129913).length < 2 ^ (prefixWord ++ tailWord_129913).sum := by decide
  have hdescent : baseEnd_129913 < baseStart_129913 := by decide
  rcases family_descends (prefixWord ++ tailWord_129913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129930 : List Nat := [3, 1, 2, 4, 1, 2, 3, 1, 6]
def baseStart_129930 : Nat := 118140960795 + 129930 * 2 ^ 59
def prefixEnd_129930 : Nat := 4983230072969 + 3 ^ 40 * 129930 * 2
def baseEnd_129930 : Nat := 7412949048753542441941

theorem tailTrace_129930 : CollatzResearch.WordTrace tailWord_129930 prefixEnd_129930 7412949048753542441941 := by
  unfold tailWord_129930
  simp only [CollatzResearch.WordTrace]
  refine ⟨1184734104823318780612811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3159290946195516748300829 1184734104823318780612811)
  ·
    refine ⟨1777101157234978170919217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1184734104823318780612811 1777101157234978170919217)
    ·
      refine ⟨1332825867926233628189413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1777101157234978170919217 1332825867926233628189413)
      ·
        refine ⟨249904850236168805285515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1332825867926233628189413 249904850236168805285515)
        ·
          refine ⟨374857275354253207928273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249904850236168805285515 374857275354253207928273)
          ·
            refine ⟨281142956515689905946205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374857275354253207928273 281142956515689905946205)
            ·
              refine ⟨105428608693383714729827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281142956515689905946205 105428608693383714729827)
              ·
                refine ⟨158142913040075572094741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105428608693383714729827 158142913040075572094741)
                ·
                  refine ⟨7412949048753542441941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158142913040075572094741 7412949048753542441941)
                  ·
                    rfl

theorem cell23_129930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 6].length) (baseStart_129930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129930 prefixEnd_129930 := by exact prefixLift 129930
  have htrace : WordTrace (prefixWord ++ tailWord_129930) baseStart_129930 baseEnd_129930 := by
    simpa [prefixWord, tailWord_129930, baseEnd_129930] using wordTrace_append hprefix tailTrace_129930
  have hstable : (prefixWord ++ tailWord_129930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129930).length < 2 ^ (prefixWord ++ tailWord_129930).sum := by decide
  have hdescent : baseEnd_129930 < baseStart_129930 := by decide
  rcases family_descends (prefixWord ++ tailWord_129930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129940 : List Nat := [2, 4, 2, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_129940 : Nat := 118140960795 + 129940 * 2 ^ 59
def prefixEnd_129940 : Nat := 4983230072969 + 3 ^ 40 * 129940 * 2
def baseEnd_129940 : Nat := 66721676245326842852423

theorem tailTrace_129940 : CollatzResearch.WordTrace tailWord_129940 prefixEnd_129940 66721676245326842852423 := by
  unfold tailWord_129940
  simp only [CollatzResearch.WordTrace]
  refine ⟨2369650574628523415157637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3159534099504697886876849 2369650574628523415157637)
  ·
    refine ⟨444309482742848140342057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2369650574628523415157637 444309482742848140342057)
    ·
      refine ⟨333232112057136105256543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444309482742848140342057 333232112057136105256543)
      ·
        refine ⟨499848168085704157884815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333232112057136105256543 499848168085704157884815)
        ·
          refine ⟨749772252128556236827223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499848168085704157884815 749772252128556236827223)
          ·
            refine ⟨1124658378192834355240835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749772252128556236827223 1124658378192834355240835)
            ·
              refine ⟨1686987567289251532861253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124658378192834355240835 1686987567289251532861253)
              ·
                refine ⟨316310168866734662411485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1686987567289251532861253 316310168866734662411485)
                ·
                  refine ⟨118616313325025498404307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 316310168866734662411485 118616313325025498404307)
                  ·
                    refine ⟨177924469987538247606461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118616313325025498404307 177924469987538247606461)
                    ·
                      refine ⟨66721676245326842852423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 177924469987538247606461 66721676245326842852423)
                      ·
                        rfl

theorem cell23_129940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_129940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129940 prefixEnd_129940 := by exact prefixLift 129940
  have htrace : WordTrace (prefixWord ++ tailWord_129940) baseStart_129940 baseEnd_129940 := by
    simpa [prefixWord, tailWord_129940, baseEnd_129940] using wordTrace_append hprefix tailTrace_129940
  have hstable : (prefixWord ++ tailWord_129940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129940).length < 2 ^ (prefixWord ++ tailWord_129940).sum := by decide
  have hdescent : baseEnd_129940 < baseStart_129940 := by decide
  rcases family_descends (prefixWord ++ tailWord_129940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129943 : List Nat := [1, 1, 3, 3, 1, 2, 4, 2, 1, 5]
def baseStart_129943 : Nat := 118140960795 + 129943 * 2 ^ 59
def prefixEnd_129943 : Nat := 4983230072969 + 3 ^ 40 * 129943 * 2
def baseEnd_129943 : Nat := 22241072229096777038303

theorem tailTrace_129943 : CollatzResearch.WordTrace tailWord_129943 prefixEnd_129943 22241072229096777038303 := by
  unfold tailWord_129943
  simp only [CollatzResearch.WordTrace]
  refine ⟨4739410568246178342674483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3159607045497452228449655 4739410568246178342674483)
  ·
    refine ⟨7109115852369267514011725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4739410568246178342674483 7109115852369267514011725)
    ·
      refine ⟨2665918444638475317754397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7109115852369267514011725 2665918444638475317754397)
      ·
        refine ⟨999719416739428244157899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2665918444638475317754397 999719416739428244157899)
        ·
          refine ⟨1499579125109142366236849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999719416739428244157899 1499579125109142366236849)
          ·
            refine ⟨1124684343831856774677637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1499579125109142366236849 1124684343831856774677637)
            ·
              refine ⟨210878314468473145252057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1124684343831856774677637 210878314468473145252057)
              ·
                refine ⟨158158735851354858939043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210878314468473145252057 158158735851354858939043)
                ·
                  refine ⟨237238103777032288408565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158158735851354858939043 237238103777032288408565)
                  ·
                    refine ⟨22241072229096777038303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 237238103777032288408565 22241072229096777038303)
                    ·
                      rfl

theorem cell23_129943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_129943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129943 prefixEnd_129943 := by exact prefixLift 129943
  have htrace : WordTrace (prefixWord ++ tailWord_129943) baseStart_129943 baseEnd_129943 := by
    simpa [prefixWord, tailWord_129943, baseEnd_129943] using wordTrace_append hprefix tailTrace_129943
  have hstable : (prefixWord ++ tailWord_129943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129943).length < 2 ^ (prefixWord ++ tailWord_129943).sum := by decide
  have hdescent : baseEnd_129943 < baseStart_129943 := by decide
  rcases family_descends (prefixWord ++ tailWord_129943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129956 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 3, 6]
def baseStart_129956 : Nat := 118140960795 + 129956 * 2 ^ 59
def prefixEnd_129956 : Nat := 4983230072969 + 3 ^ 40 * 129956 * 2
def baseEnd_129956 : Nat := 22243297311932926750783

theorem tailTrace_129956 : CollatzResearch.WordTrace tailWord_129956 prefixEnd_129956 22243297311932926750783 := by
  unfold tailWord_129956
  simp only [CollatzResearch.WordTrace]
  refine ⟨2369942358599540781448861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3159923144799387708598481 2369942358599540781448861)
  ·
    refine ⟨888728384474827793043323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2369942358599540781448861 888728384474827793043323)
    ·
      refine ⟨1333092576712241689564985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 888728384474827793043323 1333092576712241689564985)
      ·
        refine ⟨999819432534181267173739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1333092576712241689564985 999819432534181267173739)
        ·
          refine ⟨1499729148801271900760609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999819432534181267173739 1499729148801271900760609)
          ·
            refine ⟨1124796861600953925570457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1499729148801271900760609 1124796861600953925570457)
            ·
              refine ⟨843597646200715444177843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1124796861600953925570457 843597646200715444177843)
              ·
                refine ⟨1265396469301073166266765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843597646200715444177843 1265396469301073166266765)
                ·
                  refine ⟨474523675987902437350037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1265396469301073166266765 474523675987902437350037)
                  ·
                    refine ⟨22243297311932926750783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 474523675987902437350037 22243297311932926750783)
                    ·
                      rfl

theorem cell23_129956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_129956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129956 prefixEnd_129956 := by exact prefixLift 129956
  have htrace : WordTrace (prefixWord ++ tailWord_129956) baseStart_129956 baseEnd_129956 := by
    simpa [prefixWord, tailWord_129956, baseEnd_129956] using wordTrace_append hprefix tailTrace_129956
  have hstable : (prefixWord ++ tailWord_129956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129956).length < 2 ^ (prefixWord ++ tailWord_129956).sum := by decide
  have hdescent : baseEnd_129956 < baseStart_129956 := by decide
  rcases family_descends (prefixWord ++ tailWord_129956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129973 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 4, 4]
def baseStart_129973 : Nat := 118140960795 + 129973 * 2 ^ 59
def prefixEnd_129973 : Nat := 4983230072969 + 3 ^ 40 * 129973 * 2
def baseEnd_129973 : Nat := 22246207035641737913257

theorem tailTrace_129973 : CollatzResearch.WordTrace tailWord_129973 prefixEnd_129973 22246207035641737913257 := by
  unfold tailWord_129973
  simp only [CollatzResearch.WordTrace]
  refine ⟨4740504758137493466266573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3160336505424995644177715 4740504758137493466266573)
  ·
    refine ⟨1777689284301560049849965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4740504758137493466266573 1777689284301560049849965)
    ·
      refine ⟨666633481613085018693737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1777689284301560049849965 666633481613085018693737)
      ·
        refine ⟨499975111209813764020303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666633481613085018693737 499975111209813764020303)
        ·
          refine ⟨749962666814720646030455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499975111209813764020303 749962666814720646030455)
          ·
            refine ⟨1124944000222080969045683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749962666814720646030455 1124944000222080969045683)
            ·
              refine ⟨1687416000333121453568525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124944000222080969045683 1687416000333121453568525)
              ·
                refine ⟨632781000124920545088197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1687416000333121453568525 632781000124920545088197)
                ·
                  refine ⟨118646437523422602204037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 632781000124920545088197 118646437523422602204037)
                  ·
                    refine ⟨22246207035641737913257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118646437523422602204037 22246207035641737913257)
                    ·
                      rfl

theorem cell23_129973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_129973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129973 prefixEnd_129973 := by exact prefixLift 129973
  have htrace : WordTrace (prefixWord ++ tailWord_129973) baseStart_129973 baseEnd_129973 := by
    simpa [prefixWord, tailWord_129973, baseEnd_129973] using wordTrace_append hprefix tailTrace_129973
  have hstable : (prefixWord ++ tailWord_129973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129973).length < 2 ^ (prefixWord ++ tailWord_129973).sum := by decide
  have hdescent : baseEnd_129973 < baseStart_129973 := by decide
  rcases family_descends (prefixWord ++ tailWord_129973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_129976 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 1, 1, 6]
def baseStart_129976 : Nat := 118140960795 + 129976 * 2 ^ 59
def prefixEnd_129976 : Nat := 4983230072969 + 3 ^ 40 * 129976 * 2
def baseEnd_129976 : Nat := 66740161548888702002257

theorem tailTrace_129976 : CollatzResearch.WordTrace tailWord_129976 prefixEnd_129976 66740161548888702002257 := by
  unfold tailWord_129976
  simp only [CollatzResearch.WordTrace]
  refine ⟨2370307088563312489312891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3160409451417749985750521 2370307088563312489312891)
  ·
    refine ⟨3555460632844968733969337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2370307088563312489312891 3555460632844968733969337)
    ·
      refine ⟨2666595474633726550477003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3555460632844968733969337 2666595474633726550477003)
      ·
        refine ⟨3999893211950589825715505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2666595474633726550477003 3999893211950589825715505)
        ·
          refine ⟨2999919908962942369286629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3999893211950589825715505 2999919908962942369286629)
          ·
            refine ⟨562484982930551694241243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2999919908962942369286629 562484982930551694241243)
            ·
              refine ⟨843727474395827541361865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562484982930551694241243 843727474395827541361865)
              ·
                refine ⟨632795605796870656021399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843727474395827541361865 632795605796870656021399)
                ·
                  refine ⟨949193408695305984032099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 632795605796870656021399 949193408695305984032099)
                  ·
                    refine ⟨1423790113042958976048149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 949193408695305984032099 1423790113042958976048149)
                    ·
                      refine ⟨66740161548888702002257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1423790113042958976048149 66740161548888702002257)
                      ·
                        rfl

theorem cell23_129976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_129976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_129976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_129976 prefixEnd_129976 := by exact prefixLift 129976
  have htrace : WordTrace (prefixWord ++ tailWord_129976) baseStart_129976 baseEnd_129976 := by
    simpa [prefixWord, tailWord_129976, baseEnd_129976] using wordTrace_append hprefix tailTrace_129976
  have hstable : (prefixWord ++ tailWord_129976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_129976).length < 2 ^ (prefixWord ++ tailWord_129976).sum := by decide
  have hdescent : baseEnd_129976 < baseStart_129976 := by decide
  rcases family_descends (prefixWord ++ tailWord_129976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130031 : List Nat := [1, 1, 2, 1, 4, 5, 2, 2, 1, 2, 2]
def baseStart_130031 : Nat := 118140960795 + 130031 * 2 ^ 59
def prefixEnd_130031 : Nat := 4983230072969 + 3 ^ 40 * 130031 * 2
def baseEnd_130031 : Nat := 66768402984885986814505

theorem tailTrace_130031 : CollatzResearch.WordTrace tailWord_130031 prefixEnd_130031 66768402984885986814505 := by
  unfold tailWord_130031
  simp only [CollatzResearch.WordTrace]
  refine ⟨4742620191927369371877947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3161746794618246247918631 4742620191927369371877947)
  ·
    refine ⟨7113930287891054057816921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4742620191927369371877947 7113930287891054057816921)
    ·
      refine ⟨5335447715918290543362691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7113930287891054057816921 5335447715918290543362691)
      ·
        refine ⟨8003171573877435815044037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5335447715918290543362691 8003171573877435815044037)
        ·
          refine ⟨1500594670102019215320757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8003171573877435815044037 1500594670102019215320757)
          ·
            refine ⟨140680750322064301436321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1500594670102019215320757 140680750322064301436321)
            ·
              refine ⟨105510562741548226077241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140680750322064301436321 105510562741548226077241)
              ·
                refine ⟨79132922056161169557931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105510562741548226077241 79132922056161169557931)
                ·
                  refine ⟨118699383084241754336897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79132922056161169557931 118699383084241754336897)
                  ·
                    refine ⟨89024537313181315752673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118699383084241754336897 89024537313181315752673)
                    ·
                      refine ⟨66768402984885986814505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 89024537313181315752673 66768402984885986814505)
                      ·
                        rfl

theorem cell23_130031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 1, 2, 2].length) (baseStart_130031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130031 prefixEnd_130031 := by exact prefixLift 130031
  have htrace : WordTrace (prefixWord ++ tailWord_130031) baseStart_130031 baseEnd_130031 := by
    simpa [prefixWord, tailWord_130031, baseEnd_130031] using wordTrace_append hprefix tailTrace_130031
  have hstable : (prefixWord ++ tailWord_130031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130031).length < 2 ^ (prefixWord ++ tailWord_130031).sum := by decide
  have hdescent : baseEnd_130031 < baseStart_130031 := by decide
  rcases family_descends (prefixWord ++ tailWord_130031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130037 : List Nat := [1, 3, 5, 2, 1, 2, 1, 8]
def baseStart_130037 : Nat := 118140960795 + 130037 * 2 ^ 59
def prefixEnd_130037 : Nat := 4983230072969 + 3 ^ 40 * 130037 * 2
def baseEnd_130037 : Nat := 2473017921067146790351

theorem tailTrace_130037 : CollatzResearch.WordTrace tailWord_130037 prefixEnd_130037 2473017921067146790351 := by
  unfold tailWord_130037
  simp only [CollatzResearch.WordTrace]
  refine ⟨4742839029905632396596365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3161892686603754931064243 4742839029905632396596365)
  ·
    refine ⟨1778564636214612148723637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4742839029905632396596365 1778564636214612148723637)
    ·
      refine ⟨166740434645119888942841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1778564636214612148723637 166740434645119888942841)
      ·
        refine ⟨125055325983839916707131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166740434645119888942841 125055325983839916707131)
        ·
          refine ⟨187582988975759875060697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125055325983839916707131 187582988975759875060697)
          ·
            refine ⟨140687241731819906295523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187582988975759875060697 140687241731819906295523)
            ·
              refine ⟨211030862597729859443285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140687241731819906295523 211030862597729859443285)
              ·
                refine ⟨2473017921067146790351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 211030862597729859443285 2473017921067146790351)
                ·
                  rfl

theorem cell23_130037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 8].length) (baseStart_130037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130037 prefixEnd_130037 := by exact prefixLift 130037
  have htrace : WordTrace (prefixWord ++ tailWord_130037) baseStart_130037 baseEnd_130037 := by
    simpa [prefixWord, tailWord_130037, baseEnd_130037] using wordTrace_append hprefix tailTrace_130037
  have hstable : (prefixWord ++ tailWord_130037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130037).length < 2 ^ (prefixWord ++ tailWord_130037).sum := by decide
  have hdescent : baseEnd_130037 < baseStart_130037 := by decide
  rcases family_descends (prefixWord ++ tailWord_130037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130083 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 4]
def baseStart_130083 : Nat := 118140960795 + 130083 * 2 ^ 59
def prefixEnd_130083 : Nat := 4983230072969 + 3 ^ 40 * 130083 * 2
def baseEnd_130083 : Nat := 66795103978919783364265

theorem tailTrace_130083 : CollatzResearch.WordTrace tailWord_130083 prefixEnd_130083 66795103978919783364265 := by
  unfold tailWord_130083
  simp only [CollatzResearch.WordTrace]
  refine ⟨4744516787738982252770903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3163011191825988168513935 4744516787738982252770903)
  ·
    refine ⟨7116775181608473379156355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4744516787738982252770903 7116775181608473379156355)
    ·
      refine ⟨10675162772412710068734533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7116775181608473379156355 10675162772412710068734533)
      ·
        refine ⟨2001593019827383137887725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10675162772412710068734533 2001593019827383137887725)
        ·
          refine ⟨750597382435268676707897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2001593019827383137887725 750597382435268676707897)
          ·
            refine ⟨562948036826451507530923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 750597382435268676707897 562948036826451507530923)
            ·
              refine ⟨844422055239677261296385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562948036826451507530923 844422055239677261296385)
              ·
                refine ⟨633316541429757945972289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844422055239677261296385 633316541429757945972289)
                ·
                  refine ⟨474987406072318459479217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633316541429757945972289 474987406072318459479217)
                  ·
                    refine ⟨356240554554238844609413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 474987406072318459479217 356240554554238844609413)
                    ·
                      refine ⟨66795103978919783364265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 356240554554238844609413 66795103978919783364265)
                      ·
                        rfl

theorem cell23_130083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_130083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130083 prefixEnd_130083 := by exact prefixLift 130083
  have htrace : WordTrace (prefixWord ++ tailWord_130083) baseStart_130083 baseEnd_130083 := by
    simpa [prefixWord, tailWord_130083, baseEnd_130083] using wordTrace_append hprefix tailTrace_130083
  have hstable : (prefixWord ++ tailWord_130083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130083).length < 2 ^ (prefixWord ++ tailWord_130083).sum := by decide
  have hdescent : baseEnd_130083 < baseStart_130083 := by decide
  rcases family_descends (prefixWord ++ tailWord_130083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130110 : List Nat := [4, 2, 1, 3, 1, 1, 2, 2, 7]
def baseStart_130110 : Nat := 118140960795 + 130110 * 2 ^ 59
def prefixEnd_130110 : Nat := 4983230072969 + 3 ^ 40 * 130110 * 2
def baseEnd_130110 : Nat := 7423218661843464191849

theorem tailTrace_130110 : CollatzResearch.WordTrace tailWord_130110 prefixEnd_130110 7423218661843464191849 := by
  unfold tailWord_130110
  simp only [CollatzResearch.WordTrace]
  refine ⟨593187694830145733000473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3163667705760777242669189 593187694830145733000473)
  ·
    refine ⟨444890771122609299750355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 593187694830145733000473 444890771122609299750355)
    ·
      refine ⟨667336156683913949625533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444890771122609299750355 667336156683913949625533)
      ·
        refine ⟨250251058756467731109575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 667336156683913949625533 250251058756467731109575)
        ·
          refine ⟨375376588134701596664363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250251058756467731109575 375376588134701596664363)
          ·
            refine ⟨563064882202052394996545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375376588134701596664363 563064882202052394996545)
            ·
              refine ⟨422298661651539296247409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563064882202052394996545 422298661651539296247409)
              ·
                refine ⟨316723996238654472185557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422298661651539296247409 316723996238654472185557)
                ·
                  refine ⟨7423218661843464191849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 316723996238654472185557 7423218661843464191849)
                  ·
                    rfl

theorem cell23_130110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_130110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130110 prefixEnd_130110 := by exact prefixLift 130110
  have htrace : WordTrace (prefixWord ++ tailWord_130110) baseStart_130110 baseEnd_130110 := by
    simpa [prefixWord, tailWord_130110, baseEnd_130110] using wordTrace_append hprefix tailTrace_130110
  have hstable : (prefixWord ++ tailWord_130110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130110).length < 2 ^ (prefixWord ++ tailWord_130110).sum := by decide
  have hdescent : baseEnd_130110 < baseStart_130110 := by decide
  rcases family_descends (prefixWord ++ tailWord_130110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130133 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_130133 : Nat := 118140960795 + 130133 * 2 ^ 59
def prefixEnd_130133 : Nat := 4983230072969 + 3 ^ 40 * 130133 * 2
def baseEnd_130133 : Nat := 66820778011644587739035

theorem tailTrace_130133 : CollatzResearch.WordTrace tailWord_130133 prefixEnd_130133 66820778011644587739035 := by
  unfold tailWord_130133
  simp only [CollatzResearch.WordTrace]
  refine ⟨4746340437557840792091053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3164226958371893861394035 4746340437557840792091053)
  ·
    refine ⟨1779877664084190297034145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4746340437557840792091053 1779877664084190297034145)
    ·
      refine ⟨1334908248063142722775609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1779877664084190297034145 1334908248063142722775609)
      ·
        refine ⟨1001181186047357042081707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1334908248063142722775609 1001181186047357042081707)
        ·
          refine ⟨1501771779071035563122561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001181186047357042081707 1501771779071035563122561)
          ·
            refine ⟨1126328834303276672341921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1501771779071035563122561 1126328834303276672341921)
            ·
              refine ⟨844746625727457504256441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1126328834303276672341921 844746625727457504256441)
              ·
                refine ⟨633559969295593128192331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844746625727457504256441 633559969295593128192331)
                ·
                  refine ⟨950339953943389692288497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 633559969295593128192331 950339953943389692288497)
                  ·
                    refine ⟨712754965457542269216373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 950339953943389692288497 712754965457542269216373)
                    ·
                      refine ⟨66820778011644587739035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 712754965457542269216373 66820778011644587739035)
                      ·
                        rfl

theorem cell23_130133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_130133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130133 prefixEnd_130133 := by exact prefixLift 130133
  have htrace : WordTrace (prefixWord ++ tailWord_130133) baseStart_130133 baseEnd_130133 := by
    simpa [prefixWord, tailWord_130133, baseEnd_130133] using wordTrace_append hprefix tailTrace_130133
  have hstable : (prefixWord ++ tailWord_130133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130133).length < 2 ^ (prefixWord ++ tailWord_130133).sum := by decide
  have hdescent : baseEnd_130133 < baseStart_130133 := by decide
  rcases family_descends (prefixWord ++ tailWord_130133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130140 : List Nat := [2, 2, 4, 1, 1, 1, 3, 2, 2, 5]
def baseStart_130140 : Nat := 118140960795 + 130140 * 2 ^ 59
def prefixEnd_130140 : Nat := 4983230072969 + 3 ^ 40 * 130140 * 2
def baseEnd_130140 : Nat := 22274790792075353450501

theorem tailTrace_130140 : CollatzResearch.WordTrace tailWord_130140 prefixEnd_130140 22274790792075353450501 := by
  unfold tailWord_130140
  simp only [CollatzResearch.WordTrace]
  refine ⟨2373297874266240493797937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3164397165688320658397249 2373297874266240493797937)
  ·
    refine ⟨1779973405699680370348453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2373297874266240493797937 1779973405699680370348453)
    ·
      refine ⟨333745013568690069440335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1779973405699680370348453 333745013568690069440335)
      ·
        refine ⟨500617520353035104160503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333745013568690069440335 500617520353035104160503)
        ·
          refine ⟨750926280529552656240755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500617520353035104160503 750926280529552656240755)
          ·
            refine ⟨1126389420794328984361133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750926280529552656240755 1126389420794328984361133)
            ·
              refine ⟨422396032797873369135425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1126389420794328984361133 422396032797873369135425)
              ·
                refine ⟨316797024598405026851569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422396032797873369135425 316797024598405026851569)
                ·
                  refine ⟨237597768448803770138677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316797024598405026851569 237597768448803770138677)
                  ·
                    refine ⟨22274790792075353450501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 237597768448803770138677 22274790792075353450501)
                    ·
                      rfl

theorem cell23_130140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_130140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130140 prefixEnd_130140 := by exact prefixLift 130140
  have htrace : WordTrace (prefixWord ++ tailWord_130140) baseStart_130140 baseEnd_130140 := by
    simpa [prefixWord, tailWord_130140, baseEnd_130140] using wordTrace_append hprefix tailTrace_130140
  have hstable : (prefixWord ++ tailWord_130140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130140).length < 2 ^ (prefixWord ++ tailWord_130140).sum := by decide
  have hdescent : baseEnd_130140 < baseStart_130140 := by decide
  rcases family_descends (prefixWord ++ tailWord_130140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130160 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 1, 6, 2]
def baseStart_130160 : Nat := 118140960795 + 130160 * 2 ^ 59
def prefixEnd_130160 : Nat := 4983230072969 + 3 ^ 40 * 130160 * 2
def baseEnd_130160 : Nat := 66834641989315982101411

theorem tailTrace_130160 : CollatzResearch.WordTrace tailWord_130160 prefixEnd_130160 66834641989315982101411 := by
  unfold tailWord_130160
  simp only [CollatzResearch.WordTrace]
  refine ⟨2373662604230012201661967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3164883472306682935549289 2373662604230012201661967)
  ·
    refine ⟨3560493906345018302492951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2373662604230012201661967 3560493906345018302492951)
    ·
      refine ⟨5340740859517527453739427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3560493906345018302492951 5340740859517527453739427)
      ·
        refine ⟨8011111289276291180609141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5340740859517527453739427 8011111289276291180609141)
        ·
          refine ⟨751041683369652298182107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8011111289276291180609141 751041683369652298182107)
          ·
            refine ⟨1126562525054478447273161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 751041683369652298182107 1126562525054478447273161)
            ·
              refine ⟨844921893790858835454871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1126562525054478447273161 844921893790858835454871)
              ·
                refine ⟨1267382840686288253182307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 844921893790858835454871 1267382840686288253182307)
                ·
                  refine ⟨1901074261029432379773461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1267382840686288253182307 1901074261029432379773461)
                  ·
                    refine ⟨89112855985754642801881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1901074261029432379773461 89112855985754642801881)
                    ·
                      refine ⟨66834641989315982101411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 89112855985754642801881 66834641989315982101411)
                      ·
                        rfl

theorem cell23_130160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 6, 2].length) (baseStart_130160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130160 prefixEnd_130160 := by exact prefixLift 130160
  have htrace : WordTrace (prefixWord ++ tailWord_130160) baseStart_130160 baseEnd_130160 := by
    simpa [prefixWord, tailWord_130160, baseEnd_130160] using wordTrace_append hprefix tailTrace_130160
  have hstable : (prefixWord ++ tailWord_130160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130160).length < 2 ^ (prefixWord ++ tailWord_130160).sum := by decide
  have hdescent : baseEnd_130160 < baseStart_130160 := by decide
  rcases family_descends (prefixWord ++ tailWord_130160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130177 : List Nat := [1, 2, 4, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_130177 : Nat := 118140960795 + 130177 * 2 ^ 59
def prefixEnd_130177 : Nat := 4983230072969 + 3 ^ 40 * 130177 * 2
def baseEnd_130177 : Nat := 66843371160442415588833

theorem tailTrace_130177 : CollatzResearch.WordTrace tailWord_130177 prefixEnd_130177 66843371160442415588833 := by
  unfold tailWord_130177
  simp only [CollatzResearch.WordTrace]
  refine ⟨4747945249398436306692785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3165296832932290871128523 4747945249398436306692785)
  ·
    refine ⟨3560958937048827230019589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4747945249398436306692785 3560958937048827230019589)
    ·
      refine ⟨667679800696655105628673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3560958937048827230019589 667679800696655105628673)
      ·
        refine ⟨500759850522491329221505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667679800696655105628673 500759850522491329221505)
        ·
          refine ⟨375569887891868496916129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500759850522491329221505 375569887891868496916129)
          ·
            refine ⟨281677415918901372687097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375569887891868496916129 281677415918901372687097)
            ·
              refine ⟨211258061939176029515323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281677415918901372687097 211258061939176029515323)
              ·
                refine ⟨316887092908764044272985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211258061939176029515323 316887092908764044272985)
                ·
                  refine ⟨237665319681573033204739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316887092908764044272985 237665319681573033204739)
                  ·
                    refine ⟨356497979522359549807109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 237665319681573033204739 356497979522359549807109)
                    ·
                      refine ⟨66843371160442415588833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 356497979522359549807109 66843371160442415588833)
                      ·
                        rfl

theorem cell23_130177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_130177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130177 prefixEnd_130177 := by exact prefixLift 130177
  have htrace : WordTrace (prefixWord ++ tailWord_130177) baseStart_130177 baseEnd_130177 := by
    simpa [prefixWord, tailWord_130177, baseEnd_130177] using wordTrace_append hprefix tailTrace_130177
  have hstable : (prefixWord ++ tailWord_130177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130177).length < 2 ^ (prefixWord ++ tailWord_130177).sum := by decide
  have hdescent : baseEnd_130177 < baseStart_130177 := by decide
  rcases family_descends (prefixWord ++ tailWord_130177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130200 : List Nat := [2, 1, 2, 4, 2, 1, 1, 4, 6]
def baseStart_130200 : Nat := 118140960795 + 130200 * 2 ^ 59
def prefixEnd_130200 : Nat := 4983230072969 + 3 ^ 40 * 130200 * 2
def baseEnd_130200 : Nat := 7428353468388425066803

theorem tailTrace_130200 : CollatzResearch.WordTrace tailWord_130200 prefixEnd_130200 7428353468388425066803 := by
  unfold tailWord_130200
  simp only [CollatzResearch.WordTrace]
  refine ⟨2374392064157555617390027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3165856085543407489853369 2374392064157555617390027)
  ·
    refine ⟨3561588096236333426085041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2374392064157555617390027 3561588096236333426085041)
    ·
      refine ⟨2671191072177250069563781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3561588096236333426085041 2671191072177250069563781)
      ·
        refine ⟨500848326033234388043209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2671191072177250069563781 500848326033234388043209)
        ·
          refine ⟨375636244524925791032407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500848326033234388043209 375636244524925791032407)
          ·
            refine ⟨563454366787388686548611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375636244524925791032407 563454366787388686548611)
            ·
              refine ⟨845181550181083029822917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563454366787388686548611 845181550181083029822917)
              ·
                refine ⟨158471540658953068091797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 845181550181083029822917 158471540658953068091797)
                ·
                  refine ⟨7428353468388425066803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158471540658953068091797 7428353468388425066803)
                  ·
                    rfl

theorem cell23_130200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 6].length) (baseStart_130200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130200 prefixEnd_130200 := by exact prefixLift 130200
  have htrace : WordTrace (prefixWord ++ tailWord_130200) baseStart_130200 baseEnd_130200 := by
    simpa [prefixWord, tailWord_130200, baseEnd_130200] using wordTrace_append hprefix tailTrace_130200
  have hstable : (prefixWord ++ tailWord_130200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130200).length < 2 ^ (prefixWord ++ tailWord_130200).sum := by decide
  have hdescent : baseEnd_130200 < baseStart_130200 := by decide
  rcases family_descends (prefixWord ++ tailWord_130200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130204 : List Nat := [2, 2, 3, 2, 1, 3, 1, 4, 1, 4]
def baseStart_130204 : Nat := 118140960795 + 130204 * 2 ^ 59
def prefixEnd_130204 : Nat := 4983230072969 + 3 ^ 40 * 130204 * 2
def baseEnd_130204 : Nat := 22285745046037936650403

theorem tailTrace_130204 : CollatzResearch.WordTrace tailWord_130204 prefixEnd_130204 22285745046037936650403 := by
  unfold tailWord_130204
  simp only [CollatzResearch.WordTrace]
  refine ⟨2374465010150309958962833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3165953346867079945283777 2374465010150309958962833)
  ·
    refine ⟨1780848757612732469222125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2374465010150309958962833 1780848757612732469222125)
    ·
      refine ⟨667818284104774675958297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1780848757612732469222125 667818284104774675958297)
      ·
        refine ⟨500863713078581006968723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 667818284104774675958297 500863713078581006968723)
        ·
          refine ⟨751295569617871510453085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500863713078581006968723 751295569617871510453085)
          ·
            refine ⟨281735838606701816419907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 751295569617871510453085 281735838606701816419907)
            ·
              refine ⟨422603757910052724629861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281735838606701816419907 422603757910052724629861)
              ·
                refine ⟨79238204608134885868099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 422603757910052724629861 79238204608134885868099)
                ·
                  refine ⟨118857306912202328802149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79238204608134885868099 118857306912202328802149)
                  ·
                    refine ⟨22285745046037936650403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118857306912202328802149 22285745046037936650403)
                    ·
                      rfl

theorem cell23_130204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_130204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130204 prefixEnd_130204 := by exact prefixLift 130204
  have htrace : WordTrace (prefixWord ++ tailWord_130204) baseStart_130204 baseEnd_130204 := by
    simpa [prefixWord, tailWord_130204, baseEnd_130204] using wordTrace_append hprefix tailTrace_130204
  have hstable : (prefixWord ++ tailWord_130204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130204).length < 2 ^ (prefixWord ++ tailWord_130204).sum := by decide
  have hdescent : baseEnd_130204 < baseStart_130204 := by decide
  rcases family_descends (prefixWord ++ tailWord_130204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130243 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 3, 6]
def baseStart_130243 : Nat := 118140960795 + 130243 * 2 ^ 59
def prefixEnd_130243 : Nat := 4983230072969 + 3 ^ 40 * 130243 * 2
def baseEnd_130243 : Nat := 22292420294546385787843

theorem tailTrace_130243 : CollatzResearch.WordTrace tailWord_130243 prefixEnd_130243 22292420294546385787843 := by
  unfold tailWord_130243
  simp only [CollatzResearch.WordTrace]
  refine ⟨4750352467159329578595383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3166901644772886385730255 4750352467159329578595383)
  ·
    refine ⟨7125528700738994367893075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4750352467159329578595383 7125528700738994367893075)
    ·
      refine ⟨10688293051108491551839613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7125528700738994367893075 10688293051108491551839613)
      ·
        refine ⟨4008109894165684331939855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10688293051108491551839613 4008109894165684331939855)
        ·
          refine ⟨6012164841248526497909783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4008109894165684331939855 6012164841248526497909783)
          ·
            refine ⟨9018247261872789746864675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6012164841248526497909783 9018247261872789746864675)
            ·
              refine ⟨13527370892809184620297013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9018247261872789746864675 13527370892809184620297013)
              ·
                refine ⟨1268191021200861058152845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13527370892809184620297013 1268191021200861058152845)
                ·
                  refine ⟨475571632950322896807317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1268191021200861058152845 475571632950322896807317)
                  ·
                    refine ⟨22292420294546385787843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 475571632950322896807317 22292420294546385787843)
                    ·
                      rfl

theorem cell23_130243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 6].length) (baseStart_130243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130243 prefixEnd_130243 := by exact prefixLift 130243
  have htrace : WordTrace (prefixWord ++ tailWord_130243) baseStart_130243 baseEnd_130243 := by
    simpa [prefixWord, tailWord_130243, baseEnd_130243] using wordTrace_append hprefix tailTrace_130243
  have hstable : (prefixWord ++ tailWord_130243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130243).length < 2 ^ (prefixWord ++ tailWord_130243).sum := by decide
  have hdescent : baseEnd_130243 < baseStart_130243 := by decide
  rcases family_descends (prefixWord ++ tailWord_130243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130261 : List Nat := [1, 3, 2, 4, 1, 1, 2, 4, 1, 1, 3]
def baseStart_130261 : Nat := 118140960795 + 130261 * 2 ^ 59
def prefixEnd_130261 : Nat := 4983230072969 + 3 ^ 40 * 130261 * 2
def baseEnd_130261 : Nat := 66886503535420086938447

theorem tailTrace_130261 : CollatzResearch.WordTrace tailWord_130261 prefixEnd_130261 66886503535420086938447 := by
  unfold tailWord_130261
  simp only [CollatzResearch.WordTrace]
  refine ⟨4751008981094118652750637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3167339320729412435167091 4751008981094118652750637)
  ·
    refine ⟨1781628367910294494781489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4751008981094118652750637 1781628367910294494781489)
    ·
      refine ⟨1336221275932720871086117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1781628367910294494781489 1336221275932720871086117)
      ·
        refine ⟨250541489237385163328647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1336221275932720871086117 250541489237385163328647)
        ·
          refine ⟨375812233856077744992971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250541489237385163328647 375812233856077744992971)
          ·
            refine ⟨563718350784116617489457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375812233856077744992971 563718350784116617489457)
            ·
              refine ⟨422788763088087463117093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563718350784116617489457 422788763088087463117093)
              ·
                refine ⟨79272893079016399334455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 422788763088087463117093 79272893079016399334455)
                ·
                  refine ⟨118909339618524599001683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79272893079016399334455 118909339618524599001683)
                  ·
                    refine ⟨178364009427786898502525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118909339618524599001683 178364009427786898502525)
                    ·
                      refine ⟨66886503535420086938447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 178364009427786898502525 66886503535420086938447)
                      ·
                        rfl

theorem cell23_130261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_130261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_130261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_130261 prefixEnd_130261 := by exact prefixLift 130261
  have htrace : WordTrace (prefixWord ++ tailWord_130261) baseStart_130261 baseEnd_130261 := by
    simpa [prefixWord, tailWord_130261, baseEnd_130261] using wordTrace_append hprefix tailTrace_130261
  have hstable : (prefixWord ++ tailWord_130261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130261).length < 2 ^ (prefixWord ++ tailWord_130261).sum := by decide
  have hdescent : baseEnd_130261 < baseStart_130261 := by decide
  rcases family_descends (prefixWord ++ tailWord_130261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
