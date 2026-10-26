import V185TrunkScan23Chunk1101

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6525705 : List Nat := [1, 2, 1, 1, 3, 2, 3, 3, 2, 3, 2]
def baseStart_6525705 : Nat := 118140960795 + 6525705 * 2 ^ 59
def prefixEnd_6525705 : Nat := 4983230072969 + 3 ^ 40 * 6525705 * 2
def baseEnd_6525705 : Nat := 3350823274448495882876335

theorem tailTrace_6525705 : CollatzResearch.WordTrace tailWord_6525705 prefixEnd_6525705 3350823274448495882876335 := by
  unfold tailWord_6525705
  simp only [CollatzResearch.WordTrace]
  refine ⟨238012014823492761529098569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158674676548995174352732379 238012014823492761529098569)
  ·
    refine ⟨178509011117619571146823927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238012014823492761529098569 178509011117619571146823927)
    ·
      refine ⟨267763516676429356720235891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178509011117619571146823927 267763516676429356720235891)
      ·
        refine ⟨401645275014644035080353837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267763516676429356720235891 401645275014644035080353837)
        ·
          refine ⟨150616978130491513155132689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401645275014644035080353837 150616978130491513155132689)
          ·
            refine ⟨112962733597868634866349517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150616978130491513155132689 112962733597868634866349517)
            ·
              refine ⟨42361025099200738074881069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112962733597868634866349517 42361025099200738074881069)
              ·
                refine ⟨15885384412200276778080401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42361025099200738074881069 15885384412200276778080401)
                ·
                  refine ⟨11914038309150207583560301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15885384412200276778080401 11914038309150207583560301)
                  ·
                    refine ⟨4467764365931327843835113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11914038309150207583560301 4467764365931327843835113)
                    ·
                      refine ⟨3350823274448495882876335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4467764365931327843835113 3350823274448495882876335)
                      ·
                        rfl

theorem cell23_6525705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 2, 3, 2].length) (baseStart_6525705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525705 prefixEnd_6525705 := by exact prefixLift 6525705
  have htrace : WordTrace (prefixWord ++ tailWord_6525705) baseStart_6525705 baseEnd_6525705 := by
    simpa [prefixWord, tailWord_6525705, baseEnd_6525705] using wordTrace_append hprefix tailTrace_6525705
  have hstable : (prefixWord ++ tailWord_6525705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525705).length < 2 ^ (prefixWord ++ tailWord_6525705).sum := by decide
  have hdescent : baseEnd_6525705 < baseStart_6525705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525715 : List Nat := [1, 1, 1, 2, 1, 3, 7, 1, 1, 5]
def baseStart_6525715 : Nat := 118140960795 + 6525715 * 2 ^ 59
def prefixEnd_6525715 : Nat := 4983230072969 + 3 ^ 40 * 6525715 * 2
def baseEnd_6525715 : Nat := 1116942803085013614583763

theorem tailTrace_6525715 : CollatzResearch.WordTrace tailWord_6525715 prefixEnd_6525715 1116942803085013614583763 := by
  unfold tailWord_6525715
  simp only [CollatzResearch.WordTrace]
  refine ⟨238012379553456533236962599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158674919702304355491308399 238012379553456533236962599)
  ·
    refine ⟨357018569330184799855443899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238012379553456533236962599 357018569330184799855443899)
    ·
      refine ⟨535527853995277199783165849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357018569330184799855443899 535527853995277199783165849)
      ·
        refine ⟨401645890496457899837374387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535527853995277199783165849 401645890496457899837374387)
        ·
          refine ⟨602468835744686849756061581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401645890496457899837374387 602468835744686849756061581)
          ·
            refine ⟨225925813404257568658523093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 602468835744686849756061581 225925813404257568658523093)
            ·
              refine ⟨5295136251662286765434135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 225925813404257568658523093 5295136251662286765434135)
              ·
                refine ⟨7942704377493430148151203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5295136251662286765434135 7942704377493430148151203)
                ·
                  refine ⟨11914056566240145222226805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7942704377493430148151203 11914056566240145222226805)
                  ·
                    refine ⟨1116942803085013614583763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11914056566240145222226805 1116942803085013614583763)
                    ·
                      rfl

theorem cell23_6525715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 1, 5].length) (baseStart_6525715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525715 prefixEnd_6525715 := by exact prefixLift 6525715
  have htrace : WordTrace (prefixWord ++ tailWord_6525715) baseStart_6525715 baseEnd_6525715 := by
    simpa [prefixWord, tailWord_6525715, baseEnd_6525715] using wordTrace_append hprefix tailTrace_6525715
  have hstable : (prefixWord ++ tailWord_6525715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525715).length < 2 ^ (prefixWord ++ tailWord_6525715).sum := by decide
  have hdescent : baseEnd_6525715 < baseStart_6525715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525745 : List Nat := [1, 2, 2, 3, 2, 1, 1, 5, 2, 4]
def baseStart_6525745 : Nat := 118140960795 + 6525745 * 2 ^ 59
def prefixEnd_6525745 : Nat := 4983230072969 + 3 ^ 40 * 6525745 * 2
def baseEnd_6525745 : Nat := 1116947937891558575458717

theorem tailTrace_6525745 : CollatzResearch.WordTrace tailWord_6525745 prefixEnd_6525745 1116947937891558575458717 := by
  unfold tailWord_6525745
  simp only [CollatzResearch.WordTrace]
  refine ⟨238013473743347848360554689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158675649162231898907036459 238013473743347848360554689)
  ·
    refine ⟨178510105307510886270416017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238013473743347848360554689 178510105307510886270416017)
    ·
      refine ⟨133882578980633164702812013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178510105307510886270416017 133882578980633164702812013)
      ·
        refine ⟨50205967117737436763554505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133882578980633164702812013 50205967117737436763554505)
        ·
          refine ⟨37654475338303077572665879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50205967117737436763554505 37654475338303077572665879)
          ·
            refine ⟨56481713007454616358998819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37654475338303077572665879 56481713007454616358998819)
            ·
              refine ⟨84722569511181924538498229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56481713007454616358998819 84722569511181924538498229)
              ·
                refine ⟨7942740891673305425484209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84722569511181924538498229 7942740891673305425484209)
                ·
                  refine ⟨5957055668754979069113157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7942740891673305425484209 5957055668754979069113157)
                  ·
                    refine ⟨1116947937891558575458717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5957055668754979069113157 1116947937891558575458717)
                    ·
                      rfl

theorem cell23_6525745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_6525745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525745 prefixEnd_6525745 := by exact prefixLift 6525745
  have htrace : WordTrace (prefixWord ++ tailWord_6525745) baseStart_6525745 baseEnd_6525745 := by
    simpa [prefixWord, tailWord_6525745, baseEnd_6525745] using wordTrace_append hprefix tailTrace_6525745
  have hstable : (prefixWord ++ tailWord_6525745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525745).length < 2 ^ (prefixWord ++ tailWord_6525745).sum := by decide
  have hdescent : baseEnd_6525745 < baseStart_6525745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525752 : List Nat := [2, 1, 2, 1, 3, 2, 3, 2, 3, 2, 2]
def baseStart_6525752 : Nat := 118140960795 + 6525752 * 2 ^ 59
def prefixEnd_6525752 : Nat := 4983230072969 + 3 ^ 40 * 6525752 * 2
def baseEnd_6525752 : Nat := 3350847408039257198988619

theorem tailTrace_6525752 : CollatzResearch.WordTrace tailWord_6525752 prefixEnd_6525752 3350847408039257198988619 := by
  unfold tailWord_6525752
  simp only [CollatzResearch.WordTrace]
  refine ⟨119006864527161244278029755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158675819369548325704039673 119006864527161244278029755)
  ·
    refine ⟨178510296790741866417044633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119006864527161244278029755 178510296790741866417044633)
    ·
      refine ⟨133882722593056399812783475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178510296790741866417044633 133882722593056399812783475)
      ·
        refine ⟨200824083889584599719175213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133882722593056399812783475 200824083889584599719175213)
        ·
          refine ⟨75309031458594224894690705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200824083889584599719175213 75309031458594224894690705)
          ·
            refine ⟨56481773593945668671018029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75309031458594224894690705 56481773593945668671018029)
            ·
              refine ⟨21180665097729625751631761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56481773593945668671018029 21180665097729625751631761)
              ·
                refine ⟨15885498823297219313723821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21180665097729625751631761 15885498823297219313723821)
                ·
                  refine ⟨5957062058736457242646433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15885498823297219313723821 5957062058736457242646433)
                  ·
                    refine ⟨4467796544052342931984825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5957062058736457242646433 4467796544052342931984825)
                    ·
                      refine ⟨3350847408039257198988619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4467796544052342931984825 3350847408039257198988619)
                      ·
                        rfl

theorem cell23_6525752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 3, 2, 2].length) (baseStart_6525752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525752 prefixEnd_6525752 := by exact prefixLift 6525752
  have htrace : WordTrace (prefixWord ++ tailWord_6525752) baseStart_6525752 baseEnd_6525752 := by
    simpa [prefixWord, tailWord_6525752, baseEnd_6525752] using wordTrace_append hprefix tailTrace_6525752
  have hstable : (prefixWord ++ tailWord_6525752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525752).length < 2 ^ (prefixWord ++ tailWord_6525752).sum := by decide
  have hdescent : baseEnd_6525752 < baseStart_6525752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525769 : List Nat := [1, 2, 1, 1, 2, 5, 1, 5, 1, 2, 2]
def baseStart_6525769 : Nat := 118140960795 + 6525769 * 2 ^ 59
def prefixEnd_6525769 : Nat := 4983230072969 + 3 ^ 40 * 6525769 * 2
def baseEnd_6525769 : Nat := 3350856137210383632476041

theorem tailTrace_6525769 : CollatzResearch.WordTrace tailWord_6525769 prefixEnd_6525769 3350856137210383632476041 := by
  unfold tailWord_6525769
  simp only [CollatzResearch.WordTrace]
  refine ⟨238014349095260900459428361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158676232730173933639618907 238014349095260900459428361)
  ·
    refine ⟨178510761821445675344571271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238014349095260900459428361 178510761821445675344571271)
    ·
      refine ⟨267766142732168513016856907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178510761821445675344571271 267766142732168513016856907)
      ·
        refine ⟨401649214098252769525285361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267766142732168513016856907 401649214098252769525285361)
        ·
          refine ⟨301236910573689577143964021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401649214098252769525285361 301236910573689577143964021)
          ·
            refine ⟨28240960366283397857246627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 301236910573689577143964021 28240960366283397857246627)
            ·
              refine ⟨42361440549425096785869941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28240960366283397857246627 42361440549425096785869941)
              ·
                refine ⟨3971385051508602823675307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42361440549425096785869941 3971385051508602823675307)
                ·
                  refine ⟨5957077577262904235512961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3971385051508602823675307 5957077577262904235512961)
                  ·
                    refine ⟨4467808182947178176634721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5957077577262904235512961 4467808182947178176634721)
                    ·
                      refine ⟨3350856137210383632476041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4467808182947178176634721 3350856137210383632476041)
                      ·
                        rfl

theorem cell23_6525769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 1, 2, 2].length) (baseStart_6525769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525769 prefixEnd_6525769 := by exact prefixLift 6525769
  have htrace : WordTrace (prefixWord ++ tailWord_6525769) baseStart_6525769 baseEnd_6525769 := by
    simpa [prefixWord, tailWord_6525769, baseEnd_6525769] using wordTrace_append hprefix tailTrace_6525769
  have hstable : (prefixWord ++ tailWord_6525769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525769).length < 2 ^ (prefixWord ++ tailWord_6525769).sum := by decide
  have hdescent : baseEnd_6525769 < baseStart_6525769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525772 : List Nat := [2, 2, 1, 3, 3, 2, 1, 3, 1, 2, 3]
def baseStart_6525772 : Nat := 118140960795 + 6525772 * 2 ^ 59
def prefixEnd_6525772 : Nat := 4983230072969 + 3 ^ 40 * 6525772 * 2
def baseEnd_6525772 : Nat := 3350857677652347120738527

theorem tailTrace_6525772 : CollatzResearch.WordTrace tailWord_6525772 prefixEnd_6525772 3350857677652347120738527 := by
  unfold tailWord_6525772
  simp only [CollatzResearch.WordTrace]
  refine ⟨119007229257125015985893785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158676305676166687981191713 119007229257125015985893785)
  ·
    refine ⟨89255421942843761989420339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119007229257125015985893785 89255421942843761989420339)
    ·
      refine ⟨133883132914265642984130509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89255421942843761989420339 133883132914265642984130509)
      ·
        refine ⟨50206174842849616119048941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133883132914265642984130509 50206174842849616119048941)
        ·
          refine ⟨18827315566068606044643353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50206174842849616119048941 18827315566068606044643353)
          ·
            refine ⟨14120486674551454533482515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18827315566068606044643353 14120486674551454533482515)
            ·
              refine ⟨21180730011827181800223773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14120486674551454533482515 21180730011827181800223773)
              ·
                refine ⟨7942773754435193175083915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21180730011827181800223773 7942773754435193175083915)
                ·
                  refine ⟨11914160631652789762625873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7942773754435193175083915 11914160631652789762625873)
                  ·
                    refine ⟨8935620473739592321969405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11914160631652789762625873 8935620473739592321969405)
                    ·
                      refine ⟨3350857677652347120738527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8935620473739592321969405 3350857677652347120738527)
                      ·
                        rfl

theorem cell23_6525772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_6525772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525772 prefixEnd_6525772 := by exact prefixLift 6525772
  have htrace : WordTrace (prefixWord ++ tailWord_6525772) baseStart_6525772 baseEnd_6525772 := by
    simpa [prefixWord, tailWord_6525772, baseEnd_6525772] using wordTrace_append hprefix tailTrace_6525772
  have hstable : (prefixWord ++ tailWord_6525772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525772).length < 2 ^ (prefixWord ++ tailWord_6525772).sum := by decide
  have hdescent : baseEnd_6525772 < baseStart_6525772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525808 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 4]
def baseStart_6525808 : Nat := 118140960795 + 6525808 * 2 ^ 59
def prefixEnd_6525808 : Nat := 4983230072969 + 3 ^ 40 * 6525808 * 2
def baseEnd_6525808 : Nat := 3350876162955908979888361

theorem tailTrace_6525808 : CollatzResearch.WordTrace tailWord_6525808 prefixEnd_6525808 3350876162955908979888361 := by
  unfold tailWord_6525808
  simp only [CollatzResearch.WordTrace]
  refine ⟨119007885771059805060049039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158677181028079740080065385 119007885771059805060049039)
  ·
    refine ⟨178511828656589707590073559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119007885771059805060049039 178511828656589707590073559)
    ·
      refine ⟨267767742984884561385110339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178511828656589707590073559 267767742984884561385110339)
      ·
        refine ⟨401651614477326842077665509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267767742984884561385110339 401651614477326842077665509)
        ·
          refine ⟨75309677714498782889562283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 401651614477326842077665509 75309677714498782889562283)
          ·
            refine ⟨112964516571748174334343425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75309677714498782889562283 112964516571748174334343425)
            ·
              refine ⟨84723387428811130750757569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112964516571748174334343425 84723387428811130750757569)
              ·
                refine ⟨63542540571608348063068177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84723387428811130750757569 63542540571608348063068177)
                ·
                  refine ⟨47656905428706261047301133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63542540571608348063068177 47656905428706261047301133)
                  ·
                    refine ⟨17871339535764847892737925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47656905428706261047301133 17871339535764847892737925)
                    ·
                      refine ⟨3350876162955908979888361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17871339535764847892737925 3350876162955908979888361)
                      ·
                        rfl

theorem cell23_6525808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_6525808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525808 prefixEnd_6525808 := by exact prefixLift 6525808
  have htrace : WordTrace (prefixWord ++ tailWord_6525808) baseStart_6525808 baseEnd_6525808 := by
    simpa [prefixWord, tailWord_6525808, baseEnd_6525808] using wordTrace_append hprefix tailTrace_6525808
  have hstable : (prefixWord ++ tailWord_6525808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525808).length < 2 ^ (prefixWord ++ tailWord_6525808).sum := by decide
  have hdescent : baseEnd_6525808 < baseStart_6525808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525863 : List Nat := [1, 1, 6, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_6525863 : Nat := 118140960795 + 6525863 * 2 ^ 59
def prefixEnd_6525863 : Nat := 4983230072969 + 3 ^ 40 * 6525863 * 2
def baseEnd_6525863 : Nat := 3350904404391906264700609

theorem tailTrace_6525863 : CollatzResearch.WordTrace tailWord_6525863 prefixEnd_6525863 3350904404391906264700609 := by
  unfold tailWord_6525863
  simp only [CollatzResearch.WordTrace]
  refine ⟨238017777556920354513350243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158678518371280236342233495 238017777556920354513350243)
  ·
    refine ⟨357026666335380531770025365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238017777556920354513350243 357026666335380531770025365)
    ·
      refine ⟨16735624984470962426719939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 357026666335380531770025365 16735624984470962426719939)
      ·
        refine ⟨25103437476706443640079909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16735624984470962426719939 25103437476706443640079909)
        ·
          refine ⟨4706894526882458182514983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25103437476706443640079909 4706894526882458182514983)
          ·
            refine ⟨7060341790323687273772475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4706894526882458182514983 7060341790323687273772475)
            ·
              refine ⟨10590512685485530910658713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7060341790323687273772475 10590512685485530910658713)
              ·
                refine ⟨7942884514114148182994035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10590512685485530910658713 7942884514114148182994035)
                ·
                  refine ⟨11914326771171222274491053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7942884514114148182994035 11914326771171222274491053)
                  ·
                    refine ⟨4467872539189208352934145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11914326771171222274491053 4467872539189208352934145)
                    ·
                      refine ⟨3350904404391906264700609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4467872539189208352934145 3350904404391906264700609)
                      ·
                        rfl

theorem cell23_6525863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_6525863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525863 prefixEnd_6525863 := by exact prefixLift 6525863
  have htrace : WordTrace (prefixWord ++ tailWord_6525863) baseStart_6525863 baseEnd_6525863 := by
    simpa [prefixWord, tailWord_6525863, baseEnd_6525863] using wordTrace_append hprefix tailTrace_6525863
  have hstable : (prefixWord ++ tailWord_6525863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525863).length < 2 ^ (prefixWord ++ tailWord_6525863).sum := by decide
  have hdescent : baseEnd_6525863 < baseStart_6525863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525876 : List Nat := [2, 5, 2, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_6525876 : Nat := 118140960795 + 6525876 * 2 ^ 59
def prefixEnd_6525876 : Nat := 4983230072969 + 3 ^ 40 * 6525876 * 2
def baseEnd_6525876 : Nat := 3350911079640414713838049

theorem tailTrace_6525876 : CollatzResearch.WordTrace tailWord_6525876 prefixEnd_6525876 3350911079640414713838049 := by
  unfold tailWord_6525876
  simp only [CollatzResearch.WordTrace]
  refine ⟨119009125852936628866786741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158678834470582171822382321 119009125852936628866786741)
  ·
    refine ⟨11157105548712808956261257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119009125852936628866786741 11157105548712808956261257)
    ·
      refine ⟨8367829161534606717195943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11157105548712808956261257 8367829161534606717195943)
      ·
        refine ⟨12551743742301910075793915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8367829161534606717195943 12551743742301910075793915)
        ·
          refine ⟨18827615613452865113690873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12551743742301910075793915 18827615613452865113690873)
          ·
            refine ⟨14120711710089648835268155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18827615613452865113690873 14120711710089648835268155)
            ·
              refine ⟨21181067565134473252902233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14120711710089648835268155 21181067565134473252902233)
              ·
                refine ⟨15885800673850854939676675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21181067565134473252902233 15885800673850854939676675)
                ·
                  refine ⟨23828701010776282409515013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15885800673850854939676675 23828701010776282409515013)
                  ·
                    refine ⟨4467881439520552951784065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23828701010776282409515013 4467881439520552951784065)
                    ·
                      refine ⟨3350911079640414713838049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4467881439520552951784065 3350911079640414713838049)
                      ·
                        rfl

theorem cell23_6525876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_6525876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525876 prefixEnd_6525876 := by exact prefixLift 6525876
  have htrace : WordTrace (prefixWord ++ tailWord_6525876) baseStart_6525876 baseEnd_6525876 := by
    simpa [prefixWord, tailWord_6525876, baseEnd_6525876] using wordTrace_append hprefix tailTrace_6525876
  have hstable : (prefixWord ++ tailWord_6525876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525876).length < 2 ^ (prefixWord ++ tailWord_6525876).sum := by decide
  have hdescent : baseEnd_6525876 < baseStart_6525876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525895 : List Nat := [1, 1, 4, 1, 1, 2, 4, 2, 2, 5]
def baseStart_6525895 : Nat := 118140960795 + 6525895 * 2 ^ 59
def prefixEnd_6525895 : Nat := 4983230072969 + 3 ^ 40 * 6525895 * 2
def baseEnd_6525895 : Nat := 1116973611924283379833487

theorem tailTrace_6525895 : CollatzResearch.WordTrace tailWord_6525895 prefixEnd_6525895 1116973611924283379833487 := by
  unfold tailWord_6525895
  simp only [CollatzResearch.WordTrace]
  refine ⟨238018944692804423978515139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158679296461869615985676759 238018944692804423978515139)
  ·
    refine ⟨357028417039206635967772709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238018944692804423978515139 357028417039206635967772709)
    ·
      refine ⟨66942828194851244243957383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 357028417039206635967772709 66942828194851244243957383)
      ·
        refine ⟨100414242292276866365936075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66942828194851244243957383 100414242292276866365936075)
        ·
          refine ⟨150621363438415299548904113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100414242292276866365936075 150621363438415299548904113)
          ·
            refine ⟨112966022578811474661678085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150621363438415299548904113 112966022578811474661678085)
            ·
              refine ⟨21181129233527151499064641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112966022578811474661678085 21181129233527151499064641)
              ·
                refine ⟨15885846925145363624298481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21181129233527151499064641 15885846925145363624298481)
                ·
                  refine ⟨11914385193859022718223861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15885846925145363624298481 11914385193859022718223861)
                  ·
                    refine ⟨1116973611924283379833487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11914385193859022718223861 1116973611924283379833487)
                    ·
                      rfl

theorem cell23_6525895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_6525895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525895 prefixEnd_6525895 := by exact prefixLift 6525895
  have htrace : WordTrace (prefixWord ++ tailWord_6525895) baseStart_6525895 baseEnd_6525895 := by
    simpa [prefixWord, tailWord_6525895, baseEnd_6525895] using wordTrace_append hprefix tailTrace_6525895
  have hstable : (prefixWord ++ tailWord_6525895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525895).length < 2 ^ (prefixWord ++ tailWord_6525895).sum := by decide
  have hdescent : baseEnd_6525895 < baseStart_6525895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525899 : List Nat := [1, 1, 1, 1, 3, 7, 2, 2, 5]
def baseStart_6525899 : Nat := 118140960795 + 6525899 * 2 ^ 59
def prefixEnd_6525899 : Nat := 4983230072969 + 3 ^ 40 * 6525899 * 2
def baseEnd_6525899 : Nat := 372324765521718680427827

theorem tailTrace_6525899 : CollatzResearch.WordTrace tailWord_6525899 prefixEnd_6525899 372324765521718680427827 := by
  unfold tailWord_6525899
  simp only [CollatzResearch.WordTrace]
  refine ⟨238019090584789932661660751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158679393723193288441107167 238019090584789932661660751)
  ·
    refine ⟨357028635877184898992491127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238019090584789932661660751 357028635877184898992491127)
    ·
      refine ⟨535542953815777348488736691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357028635877184898992491127 535542953815777348488736691)
      ·
        refine ⟨803314430723666022733105037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535542953815777348488736691 803314430723666022733105037)
        ·
          refine ⟨301242911521374758524914389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 803314430723666022733105037 301242911521374758524914389)
          ·
            refine ⟨7060380738782220902927681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 301242911521374758524914389 7060380738782220902927681)
            ·
              refine ⟨5295285554086665677195761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7060380738782220902927681 5295285554086665677195761)
              ·
                refine ⟨3971464165564999257896821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5295285554086665677195761 3971464165564999257896821)
                ·
                  refine ⟨372324765521718680427827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3971464165564999257896821 372324765521718680427827)
                  ·
                    rfl

theorem cell23_6525899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 5].length) (baseStart_6525899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525899 prefixEnd_6525899 := by exact prefixLift 6525899
  have htrace : WordTrace (prefixWord ++ tailWord_6525899) baseStart_6525899 baseEnd_6525899 := by
    simpa [prefixWord, tailWord_6525899, baseEnd_6525899] using wordTrace_append hprefix tailTrace_6525899
  have hstable : (prefixWord ++ tailWord_6525899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525899).length < 2 ^ (prefixWord ++ tailWord_6525899).sum := by decide
  have hdescent : baseEnd_6525899 < baseStart_6525899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525902 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2]
def baseStart_6525902 : Nat := 118140960795 + 6525902 * 2 ^ 59
def prefixEnd_6525902 : Nat := 4983230072969 + 3 ^ 40 * 6525902 * 2
def baseEnd_6525902 : Nat := 3350924430137431612112929

theorem tailTrace_6525902 : CollatzResearch.WordTrace tailWord_6525902 prefixEnd_6525902 3350924430137431612112929 := by
  unfold tailWord_6525902
  simp only [CollatzResearch.WordTrace]
  refine ⟨29752400000472383021752495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158679466669186042782679973 29752400000472383021752495)
  ·
    refine ⟨44628600000708574532628743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29752400000472383021752495 44628600000708574532628743)
    ·
      refine ⟨66942900001062861798943115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44628600000708574532628743 66942900001062861798943115)
      ·
        refine ⟨100414350001594292698414673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66942900001062861798943115 100414350001594292698414673)
        ·
          refine ⟨75310762501195719523811005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100414350001594292698414673 75310762501195719523811005)
          ·
            refine ⟨28241535937948394821429127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75310762501195719523811005 28241535937948394821429127)
            ·
              refine ⟨42362303906922592232143691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28241535937948394821429127 42362303906922592232143691)
              ·
                refine ⟨63543455860383888348215537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42362303906922592232143691 63543455860383888348215537)
                ·
                  refine ⟨47657591895287916261161653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63543455860383888348215537 47657591895287916261161653)
                  ·
                    refine ⟨4467899240183242149483905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47657591895287916261161653 4467899240183242149483905)
                    ·
                      refine ⟨3350924430137431612112929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4467899240183242149483905 3350924430137431612112929)
                      ·
                        rfl

theorem cell23_6525902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_6525902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525902 prefixEnd_6525902 := by exact prefixLift 6525902
  have htrace : WordTrace (prefixWord ++ tailWord_6525902) baseStart_6525902 baseEnd_6525902 := by
    simpa [prefixWord, tailWord_6525902, baseEnd_6525902] using wordTrace_append hprefix tailTrace_6525902
  have hstable : (prefixWord ++ tailWord_6525902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525902).length < 2 ^ (prefixWord ++ tailWord_6525902).sum := by decide
  have hdescent : baseEnd_6525902 < baseStart_6525902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6525959 : List Nat := [1, 1, 4, 3, 1, 1, 1, 6, 1, 4]
def baseStart_6525959 : Nat := 118140960795 + 6525959 * 2 ^ 59
def prefixEnd_6525959 : Nat := 4983230072969 + 3 ^ 40 * 6525959 * 2
def baseEnd_6525959 : Nat := 1116984566178245963033389

theorem tailTrace_6525959 : CollatzResearch.WordTrace tailWord_6525959 prefixEnd_6525959 1116984566178245963033389 := by
  unfold tailWord_6525959
  simp only [CollatzResearch.WordTrace]
  refine ⟨238021278964572562908844931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158680852643048375272563287 238021278964572562908844931)
  ·
    refine ⟨357031918446858844363267397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238021278964572562908844931 357031918446858844363267397)
    ·
      refine ⟨66943484708786033318112637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 357031918446858844363267397 66943484708786033318112637)
      ·
        refine ⟨25103806765794762494292239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66943484708786033318112637 25103806765794762494292239)
        ·
          refine ⟨37655710148692143741438359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25103806765794762494292239 37655710148692143741438359)
          ·
            refine ⟨56483565223038215612157539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37655710148692143741438359 56483565223038215612157539)
            ·
              refine ⟨84725347834557323418236309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56483565223038215612157539 84725347834557323418236309)
              ·
                refine ⟨3971500679744874535229827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84725347834557323418236309 3971500679744874535229827)
                ·
                  refine ⟨5957251019617311802844741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3971500679744874535229827 5957251019617311802844741)
                  ·
                    refine ⟨1116984566178245963033389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5957251019617311802844741 1116984566178245963033389)
                    ·
                      rfl

theorem cell23_6525959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_6525959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6525959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6525959 prefixEnd_6525959 := by exact prefixLift 6525959
  have htrace : WordTrace (prefixWord ++ tailWord_6525959) baseStart_6525959 baseEnd_6525959 := by
    simpa [prefixWord, tailWord_6525959, baseEnd_6525959] using wordTrace_append hprefix tailTrace_6525959
  have hstable : (prefixWord ++ tailWord_6525959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6525959).length < 2 ^ (prefixWord ++ tailWord_6525959).sum := by decide
  have hdescent : baseEnd_6525959 < baseStart_6525959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6525959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526002 : List Nat := [3, 2, 1, 1, 2, 2, 1, 5, 1, 5]
def baseStart_6526002 : Nat := 118140960795 + 6526002 * 2 ^ 59
def prefixEnd_6526002 : Nat := 4983230072969 + 3 ^ 40 * 6526002 * 2
def baseEnd_6526002 : Nat := 1116991926067627073620823

theorem tailTrace_6526002 : CollatzResearch.WordTrace tailWord_6526002 prefixEnd_6526002 1116991926067627073620823 := by
  unfold tailWord_6526002
  simp only [CollatzResearch.WordTrace]
  refine ⟨59505711825854195313165065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158681898202277854168440173 59505711825854195313165065)
  ·
    refine ⟨44629283869390646484873799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59505711825854195313165065 44629283869390646484873799)
    ·
      refine ⟨66943925804085969727310699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44629283869390646484873799 66943925804085969727310699)
      ·
        refine ⟨100415888706128954590966049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66943925804085969727310699 100415888706128954590966049)
        ·
          refine ⟨75311916529596715943224537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100415888706128954590966049 75311916529596715943224537)
          ·
            refine ⟨56483937397197536957418403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75311916529596715943224537 56483937397197536957418403)
            ·
              refine ⟨84725906095796305436127605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56483937397197536957418403 84725906095796305436127605)
              ·
                refine ⟨7943053696480903634636963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84725906095796305436127605 7943053696480903634636963)
                ·
                  refine ⟨11914580544721355451955445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7943053696480903634636963 11914580544721355451955445)
                  ·
                    refine ⟨1116991926067627073620823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11914580544721355451955445 1116991926067627073620823)
                    ·
                      rfl

theorem cell23_6526002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_6526002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526002 prefixEnd_6526002 := by exact prefixLift 6526002
  have htrace : WordTrace (prefixWord ++ tailWord_6526002) baseStart_6526002 baseEnd_6526002 := by
    simpa [prefixWord, tailWord_6526002, baseEnd_6526002] using wordTrace_append hprefix tailTrace_6526002
  have hstable : (prefixWord ++ tailWord_6526002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526002).length < 2 ^ (prefixWord ++ tailWord_6526002).sum := by decide
  have hdescent : baseEnd_6526002 < baseStart_6526002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526009 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 4, 3, 2]
def baseStart_6526009 : Nat := 118140960795 + 6526009 * 2 ^ 59
def prefixEnd_6526009 : Nat := 4983230072969 + 3 ^ 40 * 6526009 * 2
def baseEnd_6526009 : Nat := 3350979372567462693474937

theorem tailTrace_6526009 : CollatzResearch.WordTrace tailWord_6526009 prefixEnd_6526009 3350979372567462693474937 := by
  unfold tailWord_6526009
  simp only [CollatzResearch.WordTrace]
  refine ⟨238023102614391421448165081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158682068409594280965443387 238023102614391421448165081)
  ·
    refine ⟨178517326960793566086123811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238023102614391421448165081 178517326960793566086123811)
    ·
      refine ⟨267775990441190349129185717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178517326960793566086123811 267775990441190349129185717)
      ·
        refine ⟨25103999103861595230861161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 267775990441190349129185717 25103999103861595230861161)
        ·
          refine ⟨18827999327896196423145871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25103999103861595230861161 18827999327896196423145871)
          ·
            refine ⟨28241998991844294634718807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18827999327896196423145871 28241998991844294634718807)
            ·
              refine ⟨42362998487766441952078211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28241998991844294634718807 42362998487766441952078211)
              ·
                refine ⟨63544497731649662928117317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42362998487766441952078211 63544497731649662928117317)
                ·
                  refine ⟨11914593324684311799021997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63544497731649662928117317 11914593324684311799021997)
                  ·
                    refine ⟨4467972496756616924633249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11914593324684311799021997 4467972496756616924633249)
                    ·
                      refine ⟨3350979372567462693474937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4467972496756616924633249 3350979372567462693474937)
                      ·
                        rfl

theorem cell23_6526009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_6526009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526009 prefixEnd_6526009 := by exact prefixLift 6526009
  have htrace : WordTrace (prefixWord ++ tailWord_6526009) baseStart_6526009 baseEnd_6526009 := by
    simpa [prefixWord, tailWord_6526009, baseEnd_6526009] using wordTrace_append hprefix tailTrace_6526009
  have hstable : (prefixWord ++ tailWord_6526009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526009).length < 2 ^ (prefixWord ++ tailWord_6526009).sum := by decide
  have hdescent : baseEnd_6526009 < baseStart_6526009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526025 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 3, 1, 5]
def baseStart_6526025 : Nat := 118140960795 + 6526025 * 2 ^ 59
def prefixEnd_6526025 : Nat := 4983230072969 + 3 ^ 40 * 6526025 * 2
def baseEnd_6526025 : Nat := 3350987588257934630874863

theorem tailTrace_6526025 : CollatzResearch.WordTrace tailWord_6526025 prefixEnd_6526025 3350987588257934630874863 := by
  unfold tailWord_6526025
  simp only [CollatzResearch.WordTrace]
  refine ⟨238023686182333456180747529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158682457454888970787165019 238023686182333456180747529)
  ·
    refine ⟨178517764636750092135560647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238023686182333456180747529 178517764636750092135560647)
    ·
      refine ⟨267776646955125138203340971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178517764636750092135560647 267776646955125138203340971)
      ·
        refine ⟨401664970432687707305011457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267776646955125138203340971 401664970432687707305011457)
        ·
          refine ⟨301248727824515780478758593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401664970432687707305011457 301248727824515780478758593)
          ·
            refine ⟨225936545868386835359068945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301248727824515780478758593 225936545868386835359068945)
            ·
              refine ⟨169452409401290126519301709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225936545868386835359068945 169452409401290126519301709)
              ·
                refine ⟨63544653525483797444738141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169452409401290126519301709 63544653525483797444738141)
                ·
                  refine ⟨23829245072056424041776803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63544653525483797444738141 23829245072056424041776803)
                  ·
                    refine ⟨35743867608084636062665205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23829245072056424041776803 35743867608084636062665205)
                    ·
                      refine ⟨3350987588257934630874863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35743867608084636062665205 3350987588257934630874863)
                      ·
                        rfl

theorem cell23_6526025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_6526025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526025 prefixEnd_6526025 := by exact prefixLift 6526025
  have htrace : WordTrace (prefixWord ++ tailWord_6526025) baseStart_6526025 baseEnd_6526025 := by
    simpa [prefixWord, tailWord_6526025, baseEnd_6526025] using wordTrace_append hprefix tailTrace_6526025
  have hstable : (prefixWord ++ tailWord_6526025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526025).length < 2 ^ (prefixWord ++ tailWord_6526025).sum := by decide
  have hdescent : baseEnd_6526025 < baseStart_6526025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526039 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 5, 2, 2]
def baseStart_6526039 : Nat := 118140960795 + 6526039 * 2 ^ 59
def prefixEnd_6526039 : Nat := 4983230072969 + 3 ^ 40 * 6526039 * 2
def baseEnd_6526039 : Nat := 3350994776987097576099799

theorem tailTrace_6526039 : CollatzResearch.WordTrace tailWord_6526039 prefixEnd_6526039 3350994776987097576099799 := by
  unfold tailWord_6526039
  simp only [CollatzResearch.WordTrace]
  refine ⟨238024196804282736571757171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158682797869521824381171447 238024196804282736571757171)
  ·
    refine ⟨357036295206424104857635757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238024196804282736571757171 357036295206424104857635757)
    ·
      refine ⟨133888610702409039321613409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357036295206424104857635757 133888610702409039321613409)
      ·
        refine ⟨100416458026806779491210057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133888610702409039321613409 100416458026806779491210057)
        ·
          refine ⟨75312343520105084618407543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100416458026806779491210057 75312343520105084618407543)
          ·
            refine ⟨112968515280157626927611315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75312343520105084618407543 112968515280157626927611315)
            ·
              refine ⟨169452772920236440391416973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112968515280157626927611315 169452772920236440391416973)
              ·
                refine ⟨63544789845088665146781365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169452772920236440391416973 63544789845088665146781365)
                ·
                  refine ⟨5957324047977062357510753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63544789845088665146781365 5957324047977062357510753)
                  ·
                    refine ⟨4467993035982796768133065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5957324047977062357510753 4467993035982796768133065)
                    ·
                      refine ⟨3350994776987097576099799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4467993035982796768133065 3350994776987097576099799)
                      ·
                        rfl

theorem cell23_6526039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_6526039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526039 prefixEnd_6526039 := by exact prefixLift 6526039
  have htrace : WordTrace (prefixWord ++ tailWord_6526039) baseStart_6526039 baseEnd_6526039 := by
    simpa [prefixWord, tailWord_6526039, baseEnd_6526039] using wordTrace_append hprefix tailTrace_6526039
  have hstable : (prefixWord ++ tailWord_6526039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526039).length < 2 ^ (prefixWord ++ tailWord_6526039).sum := by decide
  have hdescent : baseEnd_6526039 < baseStart_6526039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526065 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 6]
def baseStart_6526065 : Nat := 118140960795 + 6526065 * 2 ^ 59
def prefixEnd_6526065 : Nat := 4983230072969 + 3 ^ 40 * 6526065 * 2
def baseEnd_6526065 : Nat := 3351008127484114474374679

theorem tailTrace_6526065 : CollatzResearch.WordTrace tailWord_6526065 prefixEnd_6526065 3351008127484114474374679 := by
  unfold tailWord_6526065
  simp only [CollatzResearch.WordTrace]
  refine ⟨238025145102188543012203649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158683430068125695341469099 238025145102188543012203649)
  ·
    refine ⟨178518858826641407259152737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238025145102188543012203649 178518858826641407259152737)
    ·
      refine ⟨133889144119981055444364553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178518858826641407259152737 133889144119981055444364553)
      ·
        refine ⟨100416858089985791583273415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133889144119981055444364553 100416858089985791583273415)
        ·
          refine ⟨150625287134978687374910123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100416858089985791583273415 150625287134978687374910123)
          ·
            refine ⟨225937930702468031062365185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150625287134978687374910123 225937930702468031062365185)
            ·
              refine ⟨169453448026851023296773889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225937930702468031062365185 169453448026851023296773889)
              ·
                refine ⟨127090086020138267472580417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169453448026851023296773889 127090086020138267472580417)
                ·
                  refine ⟨95317564515103700604435313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127090086020138267472580417 95317564515103700604435313)
                  ·
                    refine ⟨71488173386327775453326485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95317564515103700604435313 71488173386327775453326485)
                    ·
                      refine ⟨3351008127484114474374679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71488173386327775453326485 3351008127484114474374679)
                      ·
                        rfl

theorem cell23_6526065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_6526065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526065 prefixEnd_6526065 := by exact prefixLift 6526065
  have htrace : WordTrace (prefixWord ++ tailWord_6526065) baseStart_6526065 baseEnd_6526065 := by
    simpa [prefixWord, tailWord_6526065, baseEnd_6526065] using wordTrace_append hprefix tailTrace_6526065
  have hstable : (prefixWord ++ tailWord_6526065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526065).length < 2 ^ (prefixWord ++ tailWord_6526065).sum := by decide
  have hdescent : baseEnd_6526065 < baseStart_6526065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526089 : List Nat := [1, 2, 1, 1, 4, 4, 2, 1, 1, 3, 3]
def baseStart_6526089 : Nat := 118140960795 + 6526089 * 2 ^ 59
def prefixEnd_6526089 : Nat := 4983230072969 + 3 ^ 40 * 6526089 * 2
def baseEnd_6526089 : Nat := 3351020451019822380474569

theorem tailTrace_6526089 : CollatzResearch.WordTrace tailWord_6526089 prefixEnd_6526089 3351020451019822380474569 := by
  unfold tailWord_6526089
  simp only [CollatzResearch.WordTrace]
  refine ⟨238026020454101595111077321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158684013636067730074051547 238026020454101595111077321)
  ·
    refine ⟨178519515340576196333307991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238026020454101595111077321 178519515340576196333307991)
    ·
      refine ⟨267779273010864294499961987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178519515340576196333307991 267779273010864294499961987)
      ·
        refine ⟨401668909516296441749942981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267779273010864294499961987 401668909516296441749942981)
        ·
          refine ⟨75312920534305582828114309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 401668909516296441749942981 75312920534305582828114309)
          ·
            refine ⟨14121172600182296780271433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75312920534305582828114309 14121172600182296780271433)
            ·
              refine ⟨10590879450136722585203575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14121172600182296780271433 10590879450136722585203575)
              ·
                refine ⟨15886319175205083877805363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10590879450136722585203575 15886319175205083877805363)
                ·
                  refine ⟨23829478762807625816708045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15886319175205083877805363 23829478762807625816708045)
                  ·
                    refine ⟨8936054536052859681265517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23829478762807625816708045 8936054536052859681265517)
                    ·
                      refine ⟨3351020451019822380474569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8936054536052859681265517 3351020451019822380474569)
                      ·
                        rfl

theorem cell23_6526089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 3, 3].length) (baseStart_6526089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526089 prefixEnd_6526089 := by exact prefixLift 6526089
  have htrace : WordTrace (prefixWord ++ tailWord_6526089) baseStart_6526089 baseEnd_6526089 := by
    simpa [prefixWord, tailWord_6526089, baseEnd_6526089] using wordTrace_append hprefix tailTrace_6526089
  have hstable : (prefixWord ++ tailWord_6526089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526089).length < 2 ^ (prefixWord ++ tailWord_6526089).sum := by decide
  have hdescent : baseEnd_6526089 < baseStart_6526089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526099 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 3, 3, 2]
def baseStart_6526099 : Nat := 118140960795 + 6526099 * 2 ^ 59
def prefixEnd_6526099 : Nat := 4983230072969 + 3 ^ 40 * 6526099 * 2
def baseEnd_6526099 : Nat := 3351025585826367341349523

theorem tailTrace_6526099 : CollatzResearch.WordTrace tailWord_6526099 prefixEnd_6526099 3351025585826367341349523 := by
  unfold tailWord_6526099
  simp only [CollatzResearch.WordTrace]
  refine ⟨238026385184065366818941351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158684256789376911212627567 238026385184065366818941351)
  ·
    refine ⟨357039577776098050228412027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238026385184065366818941351 357039577776098050228412027)
    ·
      refine ⟨535559366664147075342618041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357039577776098050228412027 535559366664147075342618041)
      ·
        refine ⟨401669524998110306506963531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535559366664147075342618041 401669524998110306506963531)
        ·
          refine ⟨602504287497165459760445297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401669524998110306506963531 602504287497165459760445297)
          ·
            refine ⟨451878215622874094820333973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602504287497165459760445297 451878215622874094820333973)
            ·
              refine ⟨21181791357322223194703155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 451878215622874094820333973 21181791357322223194703155)
              ·
                refine ⟨31772687035983334792054733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21181791357322223194703155 31772687035983334792054733)
                ·
                  refine ⟨11914757638493750547020525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31772687035983334792054733 11914757638493750547020525)
                  ·
                    refine ⟨4468034114435156455132697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11914757638493750547020525 4468034114435156455132697)
                    ·
                      refine ⟨3351025585826367341349523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4468034114435156455132697 3351025585826367341349523)
                      ·
                        rfl

theorem cell23_6526099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 3, 2].length) (baseStart_6526099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526099 prefixEnd_6526099 := by exact prefixLift 6526099
  have htrace : WordTrace (prefixWord ++ tailWord_6526099) baseStart_6526099 baseEnd_6526099 := by
    simpa [prefixWord, tailWord_6526099, baseEnd_6526099] using wordTrace_append hprefix tailTrace_6526099
  have hstable : (prefixWord ++ tailWord_6526099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526099).length < 2 ^ (prefixWord ++ tailWord_6526099).sum := by decide
  have hdescent : baseEnd_6526099 < baseStart_6526099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526110 : List Nat := [4, 3, 1, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_6526110 : Nat := 118140960795 + 6526110 * 2 ^ 59
def prefixEnd_6526110 : Nat := 4983230072969 + 3 ^ 40 * 6526110 * 2
def baseEnd_6526110 : Nat := 3351031234113566798311973

theorem tailTrace_6526110 : CollatzResearch.WordTrace tailWord_6526110 prefixEnd_6526110 3351031234113566798311973 := by
  unfold tailWord_6526110
  simp only [CollatzResearch.WordTrace]
  refine ⟨29753348298378189462198973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158684524258017010465061189 29753348298378189462198973)
  ·
    refine ⟨11157505611891821048324615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29753348298378189462198973 11157505611891821048324615)
    ·
      refine ⟨16736258417837731572486923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11157505611891821048324615 16736258417837731572486923)
      ·
        refine ⟨25104387626756597358730385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16736258417837731572486923 25104387626756597358730385)
        ·
          refine ⟨18828290720067448019047789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25104387626756597358730385 18828290720067448019047789)
          ·
            refine ⟨7060609020025293007142921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18828290720067448019047789 7060609020025293007142921)
            ·
              refine ⟨5295456765018969755357191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7060609020025293007142921 5295456765018969755357191)
              ·
                refine ⟨7943185147528454633035787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5295456765018969755357191 7943185147528454633035787)
                ·
                  refine ⟨11914777721292681949553681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7943185147528454633035787 11914777721292681949553681)
                  ·
                    refine ⟨8936083290969511462165261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11914777721292681949553681 8936083290969511462165261)
                    ·
                      refine ⟨3351031234113566798311973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8936083290969511462165261 3351031234113566798311973)
                      ·
                        rfl

theorem cell23_6526110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_6526110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526110 prefixEnd_6526110 := by exact prefixLift 6526110
  have htrace : WordTrace (prefixWord ++ tailWord_6526110) baseStart_6526110 baseEnd_6526110 := by
    simpa [prefixWord, tailWord_6526110, baseEnd_6526110] using wordTrace_append hprefix tailTrace_6526110
  have hstable : (prefixWord ++ tailWord_6526110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526110).length < 2 ^ (prefixWord ++ tailWord_6526110).sum := by decide
  have hdescent : baseEnd_6526110 < baseStart_6526110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526152 : List Nat := [2, 1, 3, 1, 2, 1, 4, 2, 7]
def baseStart_6526152 : Nat := 118140960795 + 6526152 * 2 ^ 59
def prefixEnd_6526152 : Nat := 4983230072969 + 3 ^ 40 * 6526152 * 2
def baseEnd_6526152 : Nat := 372339200033450625998531

theorem tailTrace_6526152 : CollatzResearch.WordTrace tailWord_6526152 prefixEnd_6526152 372339200033450625998531 := by
  unfold tailWord_6526152
  simp only [CollatzResearch.WordTrace]
  refine ⟨119014159126436678435310355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158685545501915571247080473 119014159126436678435310355)
  ·
    refine ⟨178521238689655017652965533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119014159126436678435310355 178521238689655017652965533)
    ·
      refine ⟨66945464508620631619862075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178521238689655017652965533 66945464508620631619862075)
      ·
        refine ⟨100418196762930947429793113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66945464508620631619862075 100418196762930947429793113)
        ·
          refine ⟨75313647572198210572344835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100418196762930947429793113 75313647572198210572344835)
          ·
            refine ⟨112970471358297315858517253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75313647572198210572344835 112970471358297315858517253)
            ·
              refine ⟨21181963379680746723471985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112970471358297315858517253 21181963379680746723471985)
              ·
                refine ⟨15886472534760560042603989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21181963379680746723471985 15886472534760560042603989)
                ·
                  refine ⟨372339200033450625998531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15886472534760560042603989 372339200033450625998531)
                  ·
                    rfl

theorem cell23_6526152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 7].length) (baseStart_6526152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526152 prefixEnd_6526152 := by exact prefixLift 6526152
  have htrace : WordTrace (prefixWord ++ tailWord_6526152) baseStart_6526152 baseEnd_6526152 := by
    simpa [prefixWord, tailWord_6526152, baseEnd_6526152] using wordTrace_append hprefix tailTrace_6526152
  have hstable : (prefixWord ++ tailWord_6526152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526152).length < 2 ^ (prefixWord ++ tailWord_6526152).sum := by decide
  have hdescent : baseEnd_6526152 < baseStart_6526152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526216 : List Nat := [2, 1, 3, 2, 4, 1, 2, 1, 2, 5]
def baseStart_6526216 : Nat := 118140960795 + 6526216 * 2 ^ 59
def prefixEnd_6526216 : Nat := 4983230072969 + 3 ^ 40 * 6526216 * 2
def baseEnd_6526216 : Nat := 1117028554354314461195495

theorem tailTrace_6526216 : CollatzResearch.WordTrace tailWord_6526216 prefixEnd_6526216 1117028554354314461195495 := by
  unfold tailWord_6526216
  simp only [CollatzResearch.WordTrace]
  refine ⟨119015326262320747900475251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158687101683094330533967001 119015326262320747900475251)
  ·
    refine ⟨178522989393481121850712877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119015326262320747900475251 178522989393481121850712877)
    ·
      refine ⟨66946121022555420694017329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178522989393481121850712877 66946121022555420694017329)
      ·
        refine ⟨50209590766916565520512997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66946121022555420694017329 50209590766916565520512997)
        ·
          refine ⟨9414298268796856035096187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50209590766916565520512997 9414298268796856035096187)
          ·
            refine ⟨14121447403195284052644281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9414298268796856035096187 14121447403195284052644281)
            ·
              refine ⟨10591085552396463039483211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14121447403195284052644281 10591085552396463039483211)
              ·
                refine ⟨15886628328594694559224817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10591085552396463039483211 15886628328594694559224817)
                ·
                  refine ⟨11914971246446020919418613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15886628328594694559224817 11914971246446020919418613)
                  ·
                    refine ⟨1117028554354314461195495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11914971246446020919418613 1117028554354314461195495)
                    ·
                      rfl

theorem cell23_6526216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_6526216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526216 prefixEnd_6526216 := by exact prefixLift 6526216
  have htrace : WordTrace (prefixWord ++ tailWord_6526216) baseStart_6526216 baseEnd_6526216 := by
    simpa [prefixWord, tailWord_6526216, baseEnd_6526216] using wordTrace_append hprefix tailTrace_6526216
  have hstable : (prefixWord ++ tailWord_6526216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526216).length < 2 ^ (prefixWord ++ tailWord_6526216).sum := by decide
  have hdescent : baseEnd_6526216 < baseStart_6526216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526219 : List Nat := [1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 4]
def baseStart_6526219 : Nat := 118140960795 + 6526219 * 2 ^ 59
def prefixEnd_6526219 : Nat := 4983230072969 + 3 ^ 40 * 6526219 * 2
def baseEnd_6526219 : Nat := 3351087203504906871848971

theorem tailTrace_6526219 : CollatzResearch.WordTrace tailWord_6526219 prefixEnd_6526219 3351087203504906871848971 := by
  unfold tailWord_6526219
  simp only [CollatzResearch.WordTrace]
  refine ⟨238030761943630627313309711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158687174629087084875539807 238030761943630627313309711)
  ·
    refine ⟨357046142915445940969964567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238030761943630627313309711 357046142915445940969964567)
    ·
      refine ⟨535569214373168911454946851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357046142915445940969964567 535569214373168911454946851)
      ·
        refine ⟨803353821559753367182420277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535569214373168911454946851 803353821559753367182420277)
        ·
          refine ⟨75314420771226878173351901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 803353821559753367182420277 75314420771226878173351901)
          ·
            refine ⟨28242907789210079315006963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75314420771226878173351901 28242907789210079315006963)
            ·
              refine ⟨42364361683815118972510445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28242907789210079315006963 42364361683815118972510445)
              ·
                refine ⟨15886635631430669614691417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42364361683815118972510445 15886635631430669614691417)
                ·
                  refine ⟨11914976723573002211018563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15886635631430669614691417 11914976723573002211018563)
                  ·
                    refine ⟨17872465085359503316527845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11914976723573002211018563 17872465085359503316527845)
                    ·
                      refine ⟨3351087203504906871848971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17872465085359503316527845 3351087203504906871848971)
                      ·
                        rfl

theorem cell23_6526219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 4].length) (baseStart_6526219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526219 prefixEnd_6526219 := by exact prefixLift 6526219
  have htrace : WordTrace (prefixWord ++ tailWord_6526219) baseStart_6526219 baseEnd_6526219 := by
    simpa [prefixWord, tailWord_6526219, baseEnd_6526219] using wordTrace_append hprefix tailTrace_6526219
  have hstable : (prefixWord ++ tailWord_6526219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526219).length < 2 ^ (prefixWord ++ tailWord_6526219).sum := by decide
  have hdescent : baseEnd_6526219 < baseStart_6526219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526253 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_6526253 : Nat := 118140960795 + 6526253 * 2 ^ 59
def prefixEnd_6526253 : Nat := 4983230072969 + 3 ^ 40 * 6526253 * 2
def baseEnd_6526253 : Nat := 3351104661847159738823815

theorem tailTrace_6526253 : CollatzResearch.WordTrace tailWord_6526253 prefixEnd_6526253 3351104661847159738823815 := by
  unfold tailWord_6526253
  simp only [CollatzResearch.WordTrace]
  refine ⟨238032002025507451120047413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158688001350338300746698275 238032002025507451120047413)
  ·
    refine ⟨22315500189891323542504445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 238032002025507451120047413 22315500189891323542504445)
    ·
      refine ⟨8368312571209246328439167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22315500189891323542504445 8368312571209246328439167)
      ·
        refine ⟨12552468856813869492658751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8368312571209246328439167 12552468856813869492658751)
        ·
          refine ⟨18828703285220804238988127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12552468856813869492658751 18828703285220804238988127)
          ·
            refine ⟨28243054927831206358482191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18828703285220804238988127 28243054927831206358482191)
            ·
              refine ⟨42364582391746809537723287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28243054927831206358482191 42364582391746809537723287)
              ·
                refine ⟨63546873587620214306584931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42364582391746809537723287 63546873587620214306584931)
                ·
                  refine ⟨95320310381430321459877397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63546873587620214306584931 95320310381430321459877397)
                  ·
                    refine ⟨4468139549129546318431753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95320310381430321459877397 4468139549129546318431753)
                    ·
                      refine ⟨3351104661847159738823815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4468139549129546318431753 3351104661847159738823815)
                      ·
                        rfl

theorem cell23_6526253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_6526253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526253 prefixEnd_6526253 := by exact prefixLift 6526253
  have htrace : WordTrace (prefixWord ++ tailWord_6526253) baseStart_6526253 baseEnd_6526253 := by
    simpa [prefixWord, tailWord_6526253, baseEnd_6526253] using wordTrace_append hprefix tailTrace_6526253
  have hstable : (prefixWord ++ tailWord_6526253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526253).length < 2 ^ (prefixWord ++ tailWord_6526253).sum := by decide
  have hdescent : baseEnd_6526253 < baseStart_6526253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526259 : List Nat := [1, 1, 1, 2, 5, 2, 2, 3, 6]
def baseStart_6526259 : Nat := 118140960795 + 6526259 * 2 ^ 59
def prefixEnd_6526259 : Nat := 4983230072969 + 3 ^ 40 * 6526259 * 2
def baseEnd_6526259 : Nat := 372345304747898523927643

theorem tailTrace_6526259 : CollatzResearch.WordTrace tailWord_6526259 prefixEnd_6526259 372345304747898523927643 := by
  unfold tailWord_6526259
  simp only [CollatzResearch.WordTrace]
  refine ⟨238032220863485714144765831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158688147242323809429843887 238032220863485714144765831)
  ·
    refine ⟨357048331295228571217148747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238032220863485714144765831 357048331295228571217148747)
    ·
      refine ⟨535572496942842856825723121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357048331295228571217148747 535572496942842856825723121)
      ·
        refine ⟨401679372707132142619292341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535572496942842856825723121 401679372707132142619292341)
        ·
          refine ⟨37657441191293638370558657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 401679372707132142619292341 37657441191293638370558657)
          ·
            refine ⟨28243080893470228777918993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37657441191293638370558657 28243080893470228777918993)
            ·
              refine ⟨21182310670102671583439245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28243080893470228777918993 21182310670102671583439245)
              ·
                refine ⟨7943366501288501843789717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21182310670102671583439245 7943366501288501843789717)
                ·
                  refine ⟨372345304747898523927643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7943366501288501843789717 372345304747898523927643)
                  ·
                    rfl

theorem cell23_6526259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 6].length) (baseStart_6526259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526259 prefixEnd_6526259 := by exact prefixLift 6526259
  have htrace : WordTrace (prefixWord ++ tailWord_6526259) baseStart_6526259 baseEnd_6526259 := by
    simpa [prefixWord, tailWord_6526259, baseEnd_6526259] using wordTrace_append hprefix tailTrace_6526259
  have hstable : (prefixWord ++ tailWord_6526259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526259).length < 2 ^ (prefixWord ++ tailWord_6526259).sum := by decide
  have hdescent : baseEnd_6526259 < baseStart_6526259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526273 : List Nat := [1, 2, 5, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_6526273 : Nat := 118140960795 + 6526273 * 2 ^ 59
def prefixEnd_6526273 : Nat := 4983230072969 + 3 ^ 40 * 6526273 * 2
def baseEnd_6526273 : Nat := 3351114931460249660573723

theorem tailTrace_6526273 : CollatzResearch.WordTrace tailWord_6526273 prefixEnd_6526273 3351114931460249660573723 := by
  unfold tailWord_6526273
  simp only [CollatzResearch.WordTrace]
  refine ⟨238032731485434994535775473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158688487656956663023850315 238032731485434994535775473)
  ·
    refine ⟨178524548614076245901831605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238032731485434994535775473 178524548614076245901831605)
    ·
      refine ⟨16736676432569648053296713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178524548614076245901831605 16736676432569648053296713)
      ·
        refine ⟨12552507324427236039972535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16736676432569648053296713 12552507324427236039972535)
        ·
          refine ⟨18828760986640854059958803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12552507324427236039972535 18828760986640854059958803)
          ·
            refine ⟨28243141479961281089938205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18828760986640854059958803 28243141479961281089938205)
            ·
              refine ⟨10591178054985480408726827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28243141479961281089938205 10591178054985480408726827)
              ·
                refine ⟨15886767082478220613090241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10591178054985480408726827 15886767082478220613090241)
                ·
                  refine ⟨11915075311858665459817681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15886767082478220613090241 11915075311858665459817681)
                  ·
                    refine ⟨8936306483893999094863261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11915075311858665459817681 8936306483893999094863261)
                    ·
                      refine ⟨3351114931460249660573723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8936306483893999094863261 3351114931460249660573723)
                      ·
                        rfl

theorem cell23_6526273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_6526273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526273 prefixEnd_6526273 := by exact prefixLift 6526273
  have htrace : WordTrace (prefixWord ++ tailWord_6526273) baseStart_6526273 baseEnd_6526273 := by
    simpa [prefixWord, tailWord_6526273, baseEnd_6526273] using wordTrace_append hprefix tailTrace_6526273
  have hstable : (prefixWord ++ tailWord_6526273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526273).length < 2 ^ (prefixWord ++ tailWord_6526273).sum := by decide
  have hdescent : baseEnd_6526273 < baseStart_6526273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526286 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3]
def baseStart_6526286 : Nat := 118140960795 + 6526286 * 2 ^ 59
def prefixEnd_6526286 : Nat := 4983230072969 + 3 ^ 40 * 6526286 * 2
def baseEnd_6526286 : Nat := 3351121606708758109711163

theorem tailTrace_6526286 : CollatzResearch.WordTrace tailWord_6526286 prefixEnd_6526286 3351121606708758109711163 := by
  unfold tailWord_6526286
  simp only [CollatzResearch.WordTrace]
  refine ⟨29754150704298487219499839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158688803756258598503999141 29754150704298487219499839)
  ·
    refine ⟨44631226056447730829249759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29754150704298487219499839 44631226056447730829249759)
    ·
      refine ⟨66946839084671596243874639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44631226056447730829249759 66946839084671596243874639)
      ·
        refine ⟨100420258627007394365811959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66946839084671596243874639 100420258627007394365811959)
        ·
          refine ⟨150630387940511091548717939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100420258627007394365811959 150630387940511091548717939)
          ·
            refine ⟨225945581910766637323076909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150630387940511091548717939 225945581910766637323076909)
            ·
              refine ⟨84729593216537488996153841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225945581910766637323076909 84729593216537488996153841)
              ·
                refine ⟨63547194912403116747115381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84729593216537488996153841 63547194912403116747115381)
                ·
                  refine ⟨5957549523037792195042067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63547194912403116747115381 5957549523037792195042067)
                  ·
                    refine ⟨8936324284556688292563101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5957549523037792195042067 8936324284556688292563101)
                    ·
                      refine ⟨3351121606708758109711163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8936324284556688292563101 3351121606708758109711163)
                      ·
                        rfl

theorem cell23_6526286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_6526286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526286 prefixEnd_6526286 := by exact prefixLift 6526286
  have htrace : WordTrace (prefixWord ++ tailWord_6526286) baseStart_6526286 baseEnd_6526286 := by
    simpa [prefixWord, tailWord_6526286, baseEnd_6526286] using wordTrace_append hprefix tailTrace_6526286
  have hstable : (prefixWord ++ tailWord_6526286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526286).length < 2 ^ (prefixWord ++ tailWord_6526286).sum := by decide
  have hdescent : baseEnd_6526286 < baseStart_6526286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526296 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 4, 3, 2]
def baseStart_6526296 : Nat := 118140960795 + 6526296 * 2 ^ 59
def prefixEnd_6526296 : Nat := 4983230072969 + 3 ^ 40 * 6526296 * 2
def baseEnd_6526296 : Nat := 3351126741515303070586117

theorem tailTrace_6526296 : CollatzResearch.WordTrace tailWord_6526296 prefixEnd_6526296 3351126741515303070586117 := by
  unfold tailWord_6526296
  simp only [CollatzResearch.WordTrace]
  refine ⟨119016785182175834731931371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158689046909567779642575161 119016785182175834731931371)
  ·
    refine ⟨178525177773263752097897057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119016785182175834731931371 178525177773263752097897057)
    ·
      refine ⟨133893883329947814073422793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178525177773263752097897057 133893883329947814073422793)
      ·
        refine ⟨100420412497460860555067095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133893883329947814073422793 100420412497460860555067095)
        ·
          refine ⟨150630618746191290832600643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100420412497460860555067095 150630618746191290832600643)
          ·
            refine ⟨225945928119286936248900965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150630618746191290832600643 225945928119286936248900965)
            ·
              refine ⟨42364861522366300546668931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225945928119286936248900965 42364861522366300546668931)
              ·
                refine ⟨63547292283549450820003397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42364861522366300546668931 63547292283549450820003397)
                ·
                  refine ⟨11915117303165522028750637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63547292283549450820003397 11915117303165522028750637)
                  ·
                    refine ⟨4468168988687070760781489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11915117303165522028750637 4468168988687070760781489)
                    ·
                      refine ⟨3351126741515303070586117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4468168988687070760781489 3351126741515303070586117)
                      ·
                        rfl

theorem cell23_6526296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_6526296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526296 prefixEnd_6526296 := by exact prefixLift 6526296
  have htrace : WordTrace (prefixWord ++ tailWord_6526296) baseStart_6526296 baseEnd_6526296 := by
    simpa [prefixWord, tailWord_6526296, baseEnd_6526296] using wordTrace_append hprefix tailTrace_6526296
  have hstable : (prefixWord ++ tailWord_6526296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526296).length < 2 ^ (prefixWord ++ tailWord_6526296).sum := by decide
  have hdescent : baseEnd_6526296 < baseStart_6526296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526354 : List Nat := [3, 2, 3, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_6526354 : Nat := 118140960795 + 6526354 * 2 ^ 59
def prefixEnd_6526354 : Nat := 4983230072969 + 3 ^ 40 * 6526354 * 2
def baseEnd_6526354 : Nat := 3351156523393263843660851

theorem tailTrace_6526354 : CollatzResearch.WordTrace tailWord_6526354 prefixEnd_6526354 3351156523393263843660851 := by
  unfold tailWord_6526354
  simp only [CollatzResearch.WordTrace]
  refine ⟨59508921449535386342368529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158690457198761030246316077 59508921449535386342368529)
  ·
    refine ⟨44631691087151539756776397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59508921449535386342368529 44631691087151539756776397)
    ·
      refine ⟨16736884157681827408791149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44631691087151539756776397 16736884157681827408791149)
      ·
        refine ⟨6276331559130685278296681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16736884157681827408791149 6276331559130685278296681)
        ·
          refine ⟨4707248669348013958722511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6276331559130685278296681 4707248669348013958722511)
          ·
            refine ⟨7060873004022020938083767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4707248669348013958722511 7060873004022020938083767)
            ·
              refine ⟨10591309506033031407125651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7060873004022020938083767 10591309506033031407125651)
              ·
                refine ⟨15886964259049547110688477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10591309506033031407125651 15886964259049547110688477)
                ·
                  refine ⟨5957611597143580166508179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15886964259049547110688477 5957611597143580166508179)
                  ·
                    refine ⟨8936417395715370249762269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5957611597143580166508179 8936417395715370249762269)
                    ·
                      refine ⟨3351156523393263843660851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8936417395715370249762269 3351156523393263843660851)
                      ·
                        rfl

theorem cell23_6526354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_6526354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526354 prefixEnd_6526354 := by exact prefixLift 6526354
  have htrace : WordTrace (prefixWord ++ tailWord_6526354) baseStart_6526354 baseEnd_6526354 := by
    simpa [prefixWord, tailWord_6526354, baseEnd_6526354] using wordTrace_append hprefix tailTrace_6526354
  have hstable : (prefixWord ++ tailWord_6526354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526354).length < 2 ^ (prefixWord ++ tailWord_6526354).sum := by decide
  have hdescent : baseEnd_6526354 < baseStart_6526354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526356 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_6526356 : Nat := 118140960795 + 6526356 * 2 ^ 59
def prefixEnd_6526356 : Nat := 4983230072969 + 3 ^ 40 * 6526356 * 2
def baseEnd_6526356 : Nat := 3351157550354572835835841

theorem tailTrace_6526356 : CollatzResearch.WordTrace tailWord_6526356 prefixEnd_6526356 3351157550354572835835841 := by
  unfold tailWord_6526356
  simp only [CollatzResearch.WordTrace]
  refine ⟨119017879372067149855523461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158690505829422866474031281 119017879372067149855523461)
  ·
    refine ⟨22315852382262590597910649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119017879372067149855523461 22315852382262590597910649)
    ·
      refine ⟨16736889286696942948432987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22315852382262590597910649 16736889286696942948432987)
      ·
        refine ⟨25105333930045414422649481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16736889286696942948432987 25105333930045414422649481)
        ·
          refine ⟨18829000447534060816987111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25105333930045414422649481 18829000447534060816987111)
          ·
            refine ⟨28243500671301091225480667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18829000447534060816987111 28243500671301091225480667)
            ·
              refine ⟨42365251006951636838221001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28243500671301091225480667 42365251006951636838221001)
              ·
                refine ⟨31773938255213727628665751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42365251006951636838221001 31773938255213727628665751)
                ·
                  refine ⟨47660907382820591442998627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31773938255213727628665751 47660907382820591442998627)
                  ·
                    refine ⟨71491361074230887164497941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47660907382820591442998627 71491361074230887164497941)
                    ·
                      refine ⟨3351157550354572835835841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71491361074230887164497941 3351157550354572835835841)
                      ·
                        rfl

theorem cell23_6526356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_6526356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526356 prefixEnd_6526356 := by exact prefixLift 6526356
  have htrace : WordTrace (prefixWord ++ tailWord_6526356) baseStart_6526356 baseEnd_6526356 := by
    simpa [prefixWord, tailWord_6526356, baseEnd_6526356] using wordTrace_append hprefix tailTrace_6526356
  have hstable : (prefixWord ++ tailWord_6526356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526356).length < 2 ^ (prefixWord ++ tailWord_6526356).sum := by decide
  have hdescent : baseEnd_6526356 < baseStart_6526356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526370 : List Nat := [3, 3, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_6526370 : Nat := 118140960795 + 6526370 * 2 ^ 59
def prefixEnd_6526370 : Nat := 4983230072969 + 3 ^ 40 * 6526370 * 2
def baseEnd_6526370 : Nat := 1117054913027911927020259

theorem tailTrace_6526370 : CollatzResearch.WordTrace tailWord_6526370 prefixEnd_6526370 1117054913027911927020259 := by
  unfold tailWord_6526370
  simp only [CollatzResearch.WordTrace]
  refine ⟨59509067341520895025514141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158690846244055720068037709 59509067341520895025514141)
  ·
    refine ⟨22315900253070335634567803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59509067341520895025514141 22315900253070335634567803)
    ·
      refine ⟨33473850379605503451851705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22315900253070335634567803 33473850379605503451851705)
      ·
        refine ⟨25105387784704127588888779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33473850379605503451851705 25105387784704127588888779)
        ·
          refine ⟨37658081677056191383333169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25105387784704127588888779 37658081677056191383333169)
          ·
            refine ⟨28243561257792143537499877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37658081677056191383333169 28243561257792143537499877)
            ·
              refine ⟨5295667735836026913281227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28243561257792143537499877 5295667735836026913281227)
              ·
                refine ⟨7943501603754040369921841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5295667735836026913281227 7943501603754040369921841)
                ·
                  refine ⟨5957626202815530277441381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7943501603754040369921841 5957626202815530277441381)
                  ·
                    refine ⟨1117054913027911927020259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5957626202815530277441381 1117054913027911927020259)
                    ·
                      rfl

theorem cell23_6526370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_6526370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526370 prefixEnd_6526370 := by exact prefixLift 6526370
  have htrace : WordTrace (prefixWord ++ tailWord_6526370) baseStart_6526370 baseEnd_6526370 := by
    simpa [prefixWord, tailWord_6526370, baseEnd_6526370] using wordTrace_append hprefix tailTrace_6526370
  have hstable : (prefixWord ++ tailWord_6526370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526370).length < 2 ^ (prefixWord ++ tailWord_6526370).sum := by decide
  have hdescent : baseEnd_6526370 < baseStart_6526370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526393 : List Nat := [1, 2, 1, 4, 4, 1, 1, 2, 1, 3, 3]
def baseStart_6526393 : Nat := 118140960795 + 6526393 * 2 ^ 59
def prefixEnd_6526393 : Nat := 4983230072969 + 3 ^ 40 * 6526393 * 2
def baseEnd_6526393 : Nat := 3351176549138789191073171

theorem tailTrace_6526393 : CollatzResearch.WordTrace tailWord_6526393 prefixEnd_6526393 3351176549138789191073171 := by
  unfold tailWord_6526393
  simp only [CollatzResearch.WordTrace]
  refine ⟨238037108245000255030143833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158691405496666836686762555 238037108245000255030143833)
  ·
    refine ⟨178527831183750191272607875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238037108245000255030143833 178527831183750191272607875)
    ·
      refine ⟨267791746775625286908911813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178527831183750191272607875 267791746775625286908911813)
      ·
        refine ⟨50210952520429741295420965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267791746775625286908911813 50210952520429741295420965)
        ·
          refine ⟨9414553597580576492891431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50210952520429741295420965 9414553597580576492891431)
          ·
            refine ⟨14121830396370864739337147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9414553597580576492891431 14121830396370864739337147)
            ·
              refine ⟨21182745594556297109005721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14121830396370864739337147 21182745594556297109005721)
              ·
                refine ⟨15887059195917222831754291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21182745594556297109005721 15887059195917222831754291)
                ·
                  refine ⟨23830588793875834247631437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15887059195917222831754291 23830588793875834247631437)
                  ·
                    refine ⟨8936470797703437842861789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23830588793875834247631437 8936470797703437842861789)
                    ·
                      refine ⟨3351176549138789191073171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8936470797703437842861789 3351176549138789191073171)
                      ·
                        rfl

theorem cell23_6526393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_6526393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526393 prefixEnd_6526393 := by exact prefixLift 6526393
  have htrace : WordTrace (prefixWord ++ tailWord_6526393) baseStart_6526393 baseEnd_6526393 := by
    simpa [prefixWord, tailWord_6526393, baseEnd_6526393] using wordTrace_append hprefix tailTrace_6526393
  have hstable : (prefixWord ++ tailWord_6526393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526393).length < 2 ^ (prefixWord ++ tailWord_6526393).sum := by decide
  have hdescent : baseEnd_6526393 < baseStart_6526393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526399 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 4]
def baseStart_6526399 : Nat := 118140960795 + 6526399 * 2 ^ 59
def prefixEnd_6526399 : Nat := 4983230072969 + 3 ^ 40 * 6526399 * 2
def baseEnd_6526399 : Nat := 3351179630022716167598143

theorem tailTrace_6526399 : CollatzResearch.WordTrace tailWord_6526399 prefixEnd_6526399 3351179630022716167598143 := by
  unfold tailWord_6526399
  simp only [CollatzResearch.WordTrace]
  refine ⟨238037327082978518054862251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158691551388652345369908167 238037327082978518054862251)
  ·
    refine ⟨357055990624467777082293377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238037327082978518054862251 357055990624467777082293377)
    ·
      refine ⟨267791992968350832811720033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357055990624467777082293377 267791992968350832811720033)
      ·
        refine ⟨200843994726263124608790025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267791992968350832811720033 200843994726263124608790025)
        ·
          refine ⟨150632996044697343456592519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200843994726263124608790025 150632996044697343456592519)
          ·
            refine ⟨225949494067046015184888779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150632996044697343456592519 225949494067046015184888779)
            ·
              refine ⟨338924241100569022777333169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225949494067046015184888779 338924241100569022777333169)
              ·
                refine ⟨254193180825426767082999877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338924241100569022777333169 254193180825426767082999877)
                ·
                  refine ⟨47661221404767518828062477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 254193180825426767082999877 47661221404767518828062477)
                  ·
                    refine ⟨17872958026787819560523429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47661221404767518828062477 17872958026787819560523429)
                    ·
                      refine ⟨3351179630022716167598143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17872958026787819560523429 3351179630022716167598143)
                      ·
                        rfl

theorem cell23_6526399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_6526399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526399 prefixEnd_6526399 := by exact prefixLift 6526399
  have htrace : WordTrace (prefixWord ++ tailWord_6526399) baseStart_6526399 baseEnd_6526399 := by
    simpa [prefixWord, tailWord_6526399, baseEnd_6526399] using wordTrace_append hprefix tailTrace_6526399
  have hstable : (prefixWord ++ tailWord_6526399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526399).length < 2 ^ (prefixWord ++ tailWord_6526399).sum := by decide
  have hdescent : baseEnd_6526399 < baseStart_6526399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526403 : List Nat := [1, 1, 1, 3, 1, 1, 4, 5, 1, 3, 2]
def baseStart_6526403 : Nat := 118140960795 + 6526403 * 2 ^ 59
def prefixEnd_6526403 : Nat := 4983230072969 + 3 ^ 40 * 6526403 * 2
def baseEnd_6526403 : Nat := 3351181683945334151948125

theorem tailTrace_6526403 : CollatzResearch.WordTrace tailWord_6526403 prefixEnd_6526403 3351181683945334151948125 := by
  unfold tailWord_6526403
  simp only [CollatzResearch.WordTrace]
  refine ⟨238037472974964026738007863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158691648649976017825338575 238037472974964026738007863)
  ·
    refine ⟨357056209462446040107011795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238037472974964026738007863 357056209462446040107011795)
    ·
      refine ⟨535584314193669060160517693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357056209462446040107011795 535584314193669060160517693)
      ·
        refine ⟨200844117822625897560194135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 535584314193669060160517693 200844117822625897560194135)
        ·
          refine ⟨301266176733938846340291203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200844117822625897560194135 301266176733938846340291203)
          ·
            refine ⟨451899265100908269510436805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301266176733938846340291203 451899265100908269510436805)
            ·
              refine ⟨84731112206420300533206901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 451899265100908269510436805 84731112206420300533206901)
              ·
                refine ⟨7943541769351903174988147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84731112206420300533206901 7943541769351903174988147)
                ·
                  refine ⟨11915312654027854762482221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7943541769351903174988147 11915312654027854762482221)
                  ·
                    refine ⟨4468242245260445535930833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11915312654027854762482221 4468242245260445535930833)
                    ·
                      refine ⟨3351181683945334151948125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4468242245260445535930833 3351181683945334151948125)
                      ·
                        rfl

theorem cell23_6526403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 3, 2].length) (baseStart_6526403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526403 prefixEnd_6526403 := by exact prefixLift 6526403
  have htrace : WordTrace (prefixWord ++ tailWord_6526403) baseStart_6526403 baseEnd_6526403 := by
    simpa [prefixWord, tailWord_6526403, baseEnd_6526403] using wordTrace_append hprefix tailTrace_6526403
  have hstable : (prefixWord ++ tailWord_6526403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526403).length < 2 ^ (prefixWord ++ tailWord_6526403).sum := by decide
  have hdescent : baseEnd_6526403 < baseStart_6526403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526409 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 2, 6]
def baseStart_6526409 : Nat := 118140960795 + 6526409 * 2 ^ 59
def prefixEnd_6526409 : Nat := 4983230072969 + 3 ^ 40 * 6526409 * 2
def baseEnd_6526409 : Nat := 1117061588276420376157699

theorem tailTrace_6526409 : CollatzResearch.WordTrace tailWord_6526409 prefixEnd_6526409 1117061588276420376157699 := by
  unfold tailWord_6526409
  simp only [CollatzResearch.WordTrace]
  refine ⟨238037691812942289762726281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158691794541961526508484187 238037691812942289762726281)
  ·
    refine ⟨178528268859706717322044711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238037691812942289762726281 178528268859706717322044711)
    ·
      refine ⟨267792403289560075983067067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178528268859706717322044711 267792403289560075983067067)
      ·
        refine ⟨401688604934340113974600601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267792403289560075983067067 401688604934340113974600601)
        ·
          refine ⟨301266453700755085480950451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401688604934340113974600601 301266453700755085480950451)
          ·
            refine ⟨451899680551132628221425677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301266453700755085480950451 451899680551132628221425677)
            ·
              refine ⟨169462380206674735583034629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 451899680551132628221425677 169462380206674735583034629)
              ·
                refine ⟨31774196288751512921818993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169462380206674735583034629 31774196288751512921818993)
                ·
                  refine ⟨23830647216563634691364245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31774196288751512921818993 23830647216563634691364245)
                  ·
                    refine ⟨1117061588276420376157699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23830647216563634691364245 1117061588276420376157699)
                    ·
                      rfl

theorem cell23_6526409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 6].length) (baseStart_6526409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526409 prefixEnd_6526409 := by exact prefixLift 6526409
  have htrace : WordTrace (prefixWord ++ tailWord_6526409) baseStart_6526409 baseEnd_6526409 := by
    simpa [prefixWord, tailWord_6526409, baseEnd_6526409] using wordTrace_append hprefix tailTrace_6526409
  have hstable : (prefixWord ++ tailWord_6526409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526409).length < 2 ^ (prefixWord ++ tailWord_6526409).sum := by decide
  have hdescent : baseEnd_6526409 < baseStart_6526409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526410 : List Nat := [3, 1, 2, 1, 2, 4, 2, 2, 2, 1, 3]
def baseStart_6526410 : Nat := 118140960795 + 6526410 * 2 ^ 59
def prefixEnd_6526410 : Nat := 4983230072969 + 3 ^ 40 * 6526410 * 2
def baseEnd_6526410 : Nat := 3351185278309915624560593

theorem tailTrace_6526410 : CollatzResearch.WordTrace tailWord_6526410 prefixEnd_6526410 3351185278309915624560593 := by
  unfold tailWord_6526410
  simp only [CollatzResearch.WordTrace]
  refine ⟨59509432071484666733378171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158691818857292444622341789 59509432071484666733378171)
  ·
    refine ⟨89264148107227000100067257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59509432071484666733378171 89264148107227000100067257)
    ·
      refine ⟨66948111080420250075050443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89264148107227000100067257 66948111080420250075050443)
      ·
        refine ⟨100422166620630375112575665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66948111080420250075050443 100422166620630375112575665)
        ·
          refine ⟨75316624965472781334431749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100422166620630375112575665 75316624965472781334431749)
          ·
            refine ⟨14121867181026146500205953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75316624965472781334431749 14121867181026146500205953)
            ·
              refine ⟨10591400385769609875154465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14121867181026146500205953 10591400385769609875154465)
              ·
                refine ⟨7943550289327207406365849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10591400385769609875154465 7943550289327207406365849)
                ·
                  refine ⟨5957662716995405554774387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7943550289327207406365849 5957662716995405554774387)
                  ·
                    refine ⟨8936494075493108332161581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5957662716995405554774387 8936494075493108332161581)
                    ·
                      refine ⟨3351185278309915624560593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8936494075493108332161581 3351185278309915624560593)
                      ·
                        rfl

theorem cell23_6526410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_6526410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526410 prefixEnd_6526410 := by exact prefixLift 6526410
  have htrace : WordTrace (prefixWord ++ tailWord_6526410) baseStart_6526410 baseEnd_6526410 := by
    simpa [prefixWord, tailWord_6526410, baseEnd_6526410] using wordTrace_append hprefix tailTrace_6526410
  have hstable : (prefixWord ++ tailWord_6526410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526410).length < 2 ^ (prefixWord ++ tailWord_6526410).sum := by decide
  have hdescent : baseEnd_6526410 < baseStart_6526410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526426 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 2, 6]
def baseStart_6526426 : Nat := 118140960795 + 6526426 * 2 ^ 59
def prefixEnd_6526426 : Nat := 4983230072969 + 3 ^ 40 * 6526426 * 2
def baseEnd_6526426 : Nat := 1117064498000129187320173

theorem tailTrace_6526426 : CollatzResearch.WordTrace tailWord_6526426 prefixEnd_6526426 1117064498000129187320173 := by
  unfold tailWord_6526426
  simp only [CollatzResearch.WordTrace]
  refine ⟨59509577963470175416523783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158692207902587134444063421 59509577963470175416523783)
  ·
    refine ⟨89264366945205263124785675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59509577963470175416523783 89264366945205263124785675)
    ·
      refine ⟨133896550417807894687178513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89264366945205263124785675 133896550417807894687178513)
      ·
        refine ⟨100422412813355921015383885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133896550417807894687178513 100422412813355921015383885)
        ·
          refine ⟨37658404805008470380768957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100422412813355921015383885 37658404805008470380768957)
          ·
            refine ⟨14121901801878176392788359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37658404805008470380768957 14121901801878176392788359)
            ·
              refine ⟨21182852702817264589182539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14121901801878176392788359 21182852702817264589182539)
              ·
                refine ⟨31774279054225896883773809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21182852702817264589182539 31774279054225896883773809)
                ·
                  refine ⟨23830709290669422662830357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31774279054225896883773809 23830709290669422662830357)
                  ·
                    refine ⟨1117064498000129187320173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23830709290669422662830357 1117064498000129187320173)
                    ·
                      rfl

theorem cell23_6526426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_6526426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526426 prefixEnd_6526426 := by exact prefixLift 6526426
  have htrace : WordTrace (prefixWord ++ tailWord_6526426) baseStart_6526426 baseEnd_6526426 := by
    simpa [prefixWord, tailWord_6526426, baseEnd_6526426] using wordTrace_append hprefix tailTrace_6526426
  have hstable : (prefixWord ++ tailWord_6526426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526426).length < 2 ^ (prefixWord ++ tailWord_6526426).sum := by decide
  have hdescent : baseEnd_6526426 < baseStart_6526426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526433 : List Nat := [1, 2, 3, 1, 2, 3, 1, 3, 1, 4, 2]
def baseStart_6526433 : Nat := 118140960795 + 6526433 * 2 ^ 59
def prefixEnd_6526433 : Nat := 4983230072969 + 3 ^ 40 * 6526433 * 2
def baseEnd_6526433 : Nat := 3351197088364969034572987

theorem tailTrace_6526433 : CollatzResearch.WordTrace tailWord_6526433 prefixEnd_6526433 3351197088364969034572987 := by
  unfold tailWord_6526433
  simp only [CollatzResearch.WordTrace]
  refine ⟨238038567164855341861599953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158692378109903561241066635 238038567164855341861599953)
  ·
    refine ⟨178528925373641506396199965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238038567164855341861599953 178528925373641506396199965)
    ·
      refine ⟨66948347015115564898574987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178528925373641506396199965 66948347015115564898574987)
      ·
        refine ⟨100422520522673347347862481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66948347015115564898574987 100422520522673347347862481)
        ·
          refine ⟨75316890392005010510896861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100422520522673347347862481 75316890392005010510896861)
          ·
            refine ⟨28243833897001878941586323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75316890392005010510896861 28243833897001878941586323)
            ·
              refine ⟨42365750845502818412379485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28243833897001878941586323 42365750845502818412379485)
              ·
                refine ⟨15887156567063556904642307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42365750845502818412379485 15887156567063556904642307)
                ·
                  refine ⟨23830734850595335356963461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15887156567063556904642307 23830734850595335356963461)
                  ·
                    refine ⟨4468262784486625379430649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23830734850595335356963461 4468262784486625379430649)
                    ·
                      refine ⟨3351197088364969034572987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4468262784486625379430649 3351197088364969034572987)
                      ·
                        rfl

theorem cell23_6526433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_6526433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526433 prefixEnd_6526433 := by exact prefixLift 6526433
  have htrace : WordTrace (prefixWord ++ tailWord_6526433) baseStart_6526433 baseEnd_6526433 := by
    simpa [prefixWord, tailWord_6526433, baseEnd_6526433] using wordTrace_append hprefix tailTrace_6526433
  have hstable : (prefixWord ++ tailWord_6526433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526433).length < 2 ^ (prefixWord ++ tailWord_6526433).sum := by decide
  have hdescent : baseEnd_6526433 < baseStart_6526433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526446 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_6526446 : Nat := 118140960795 + 6526446 * 2 ^ 59
def prefixEnd_6526446 : Nat := 4983230072969 + 3 ^ 40 * 6526446 * 2
def baseEnd_6526446 : Nat := 3351203763613477483710427

theorem tailTrace_6526446 : CollatzResearch.WordTrace tailWord_6526446 prefixEnd_6526446 3351203763613477483710427 := by
  unfold tailWord_6526446
  simp only [CollatzResearch.WordTrace]
  refine ⟨29754880164226030635227899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158692694209205496721215461 29754880164226030635227899)
  ·
    refine ⟨44632320246339045952841849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29754880164226030635227899 44632320246339045952841849)
    ·
      refine ⟨33474240184754284464631387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44632320246339045952841849 33474240184754284464631387)
      ·
        refine ⟨50211360277131426696947081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33474240184754284464631387 50211360277131426696947081)
        ·
          refine ⟨37658520207848570022710311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50211360277131426696947081 37658520207848570022710311)
          ·
            refine ⟨56487780311772855034065467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37658520207848570022710311 56487780311772855034065467)
            ·
              refine ⟨84731670467659282551098201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56487780311772855034065467 84731670467659282551098201)
              ·
                refine ⟨63548752850744461913323651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84731670467659282551098201 63548752850744461913323651)
                ·
                  refine ⟨95323129276116692869985477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63548752850744461913323651 95323129276116692869985477)
                  ·
                    refine ⟨17873086739271879913122277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95323129276116692869985477 17873086739271879913122277)
                    ·
                      refine ⟨3351203763613477483710427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17873086739271879913122277 3351203763613477483710427)
                      ·
                        rfl

theorem cell23_6526446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_6526446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526446 prefixEnd_6526446 := by exact prefixLift 6526446
  have htrace : WordTrace (prefixWord ++ tailWord_6526446) baseStart_6526446 baseEnd_6526446 := by
    simpa [prefixWord, tailWord_6526446, baseEnd_6526446] using wordTrace_append hprefix tailTrace_6526446
  have hstable : (prefixWord ++ tailWord_6526446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526446).length < 2 ^ (prefixWord ++ tailWord_6526446).sum := by decide
  have hdescent : baseEnd_6526446 < baseStart_6526446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526450 : List Nat := [3, 2, 1, 4, 1, 1, 2, 2, 1, 4, 2]
def baseStart_6526450 : Nat := 118140960795 + 6526450 * 2 ^ 59
def prefixEnd_6526450 : Nat := 4983230072969 + 3 ^ 40 * 6526450 * 2
def baseEnd_6526450 : Nat := 3351205817536095468060409

theorem tailTrace_6526450 : CollatzResearch.WordTrace tailWord_6526450 prefixEnd_6526450 3351205817536095468060409 := by
  unfold tailWord_6526450
  simp only [CollatzResearch.WordTrace]
  refine ⟨59509796801448438441242201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158692791470529169176645869 59509796801448438441242201)
  ·
    refine ⟨44632347601086328830931651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59509796801448438441242201 44632347601086328830931651)
    ·
      refine ⟨66948521401629493246397477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44632347601086328830931651 66948521401629493246397477)
      ·
        refine ⟨12552847762805529983699527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66948521401629493246397477 12552847762805529983699527)
        ·
          refine ⟨18829271644208294975549291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12552847762805529983699527 18829271644208294975549291)
          ·
            refine ⟨28243907466312442463323937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18829271644208294975549291 28243907466312442463323937)
            ·
              refine ⟨21182930599734331847492953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28243907466312442463323937 21182930599734331847492953)
              ·
                refine ⟨15887197949800748885619715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21182930599734331847492953 15887197949800748885619715)
                ·
                  refine ⟨23830796924701123328429573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15887197949800748885619715 23830796924701123328429573)
                  ·
                    refine ⟨4468274423381460624080545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23830796924701123328429573 4468274423381460624080545)
                    ·
                      refine ⟨3351205817536095468060409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4468274423381460624080545 3351205817536095468060409)
                      ·
                        rfl

theorem cell23_6526450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_6526450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526450 prefixEnd_6526450 := by exact prefixLift 6526450
  have htrace : WordTrace (prefixWord ++ tailWord_6526450) baseStart_6526450 baseEnd_6526450 := by
    simpa [prefixWord, tailWord_6526450, baseEnd_6526450] using wordTrace_append hprefix tailTrace_6526450
  have hstable : (prefixWord ++ tailWord_6526450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526450).length < 2 ^ (prefixWord ++ tailWord_6526450).sum := by decide
  have hdescent : baseEnd_6526450 < baseStart_6526450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526454 : List Nat := [5, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2]
def baseStart_6526454 : Nat := 118140960795 + 6526454 * 2 ^ 59
def prefixEnd_6526454 : Nat := 4983230072969 + 3 ^ 40 * 6526454 * 2
def baseEnd_6526454 : Nat := 3351207871458713452410391

theorem tailTrace_6526454 : CollatzResearch.WordTrace tailWord_6526454 prefixEnd_6526454 3351207871458713452410391 := by
  unfold tailWord_6526454
  simp only [CollatzResearch.WordTrace]
  refine ⟨14877458318611203903007151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158692888731852841632076277 14877458318611203903007151)
  ·
    refine ⟨22316187477916805854510727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14877458318611203903007151 22316187477916805854510727)
    ·
      refine ⟨33474281216875208781766091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22316187477916805854510727 33474281216875208781766091)
      ·
        refine ⟨50211421825312813172649137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33474281216875208781766091 50211421825312813172649137)
        ·
          refine ⟨37658566368984609879486853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50211421825312813172649137 37658566368984609879486853)
          ·
            refine ⟨7060981194184614352403785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37658566368984609879486853 7060981194184614352403785)
            ·
              refine ⟨5295735895638460764302839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7060981194184614352403785 5295735895638460764302839)
              ·
                refine ⟨7943603843457691146454259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5295735895638460764302839 7943603843457691146454259)
                ·
                  refine ⟨11915405765186536719681389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7943603843457691146454259 11915405765186536719681389)
                  ·
                    refine ⟨4468277161944951269880521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11915405765186536719681389 4468277161944951269880521)
                    ·
                      refine ⟨3351207871458713452410391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4468277161944951269880521 3351207871458713452410391)
                      ·
                        rfl

theorem cell23_6526454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_6526454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526454 prefixEnd_6526454 := by exact prefixLift 6526454
  have htrace : WordTrace (prefixWord ++ tailWord_6526454) baseStart_6526454 baseEnd_6526454 := by
    simpa [prefixWord, tailWord_6526454, baseEnd_6526454] using wordTrace_append hprefix tailTrace_6526454
  have hstable : (prefixWord ++ tailWord_6526454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526454).length < 2 ^ (prefixWord ++ tailWord_6526454).sum := by decide
  have hdescent : baseEnd_6526454 < baseStart_6526454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526484 : List Nat := [2, 4, 3, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_6526484 : Nat := 118140960795 + 6526484 * 2 ^ 59
def prefixEnd_6526484 : Nat := 4983230072969 + 3 ^ 40 * 6526484 * 2
def baseEnd_6526484 : Nat := 3351223275878348335035253

theorem tailTrace_6526484 : CollatzResearch.WordTrace tailWord_6526484 prefixEnd_6526484 3351223275878348335035253 := by
  unfold tailWord_6526484
  simp only [CollatzResearch.WordTrace]
  refine ⟨119020213643835288785853253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158693618191780385047804337 119020213643835288785853253)
  ·
    refine ⟨22316290058219116647347485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119020213643835288785853253 22316290058219116647347485)
    ·
      refine ⟨8368608771832168742755307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22316290058219116647347485 8368608771832168742755307)
      ·
        refine ⟨12552913157748253114132961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8368608771832168742755307 12552913157748253114132961)
        ·
          refine ⟨9414684868311189835599721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12552913157748253114132961 9414684868311189835599721)
          ·
            refine ⟨7061013651233392376699791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9414684868311189835599721 7061013651233392376699791)
            ·
              refine ⟨10591520476850088565049687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7061013651233392376699791 10591520476850088565049687)
              ·
                refine ⟨15887280715275132847574531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10591520476850088565049687 15887280715275132847574531)
                ·
                  refine ⟨23830921072912699271361797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15887280715275132847574531 23830921072912699271361797)
                  ·
                    refine ⟨4468297701171131113380337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23830921072912699271361797 4468297701171131113380337)
                    ·
                      refine ⟨3351223275878348335035253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4468297701171131113380337 3351223275878348335035253)
                      ·
                        rfl

theorem cell23_6526484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_6526484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526484 prefixEnd_6526484 := by exact prefixLift 6526484
  have htrace : WordTrace (prefixWord ++ tailWord_6526484) baseStart_6526484 baseEnd_6526484 := by
    simpa [prefixWord, tailWord_6526484, baseEnd_6526484] using wordTrace_append hprefix tailTrace_6526484
  have hstable : (prefixWord ++ tailWord_6526484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526484).length < 2 ^ (prefixWord ++ tailWord_6526484).sum := by decide
  have hdescent : baseEnd_6526484 < baseStart_6526484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526583 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 3, 5, 2]
def baseStart_6526583 : Nat := 118140960795 + 6526583 * 2 ^ 59
def prefixEnd_6526583 : Nat := 4983230072969 + 3 ^ 40 * 6526583 * 2
def baseEnd_6526583 : Nat := 3351274110463143447697297

theorem tailTrace_6526583 : CollatzResearch.WordTrace tailWord_6526583 prefixEnd_6526583 3351274110463143447697297 := by
  unfold tailWord_6526583
  simp only [CollatzResearch.WordTrace]
  refine ⟨238044038114311917479560403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158696025409541278319706935 238044038114311917479560403)
  ·
    refine ⟨357066057171467876219340605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238044038114311917479560403 357066057171467876219340605)
    ·
      refine ⟨133899771439300453582252727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357066057171467876219340605 133899771439300453582252727)
      ·
        refine ⟨200849657158950680373379091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133899771439300453582252727 200849657158950680373379091)
        ·
          refine ⟨301274485738426020560068637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200849657158950680373379091 301274485738426020560068637)
          ·
            refine ⟨112977932151909757710025739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301274485738426020560068637 112977932151909757710025739)
            ·
              refine ⟨169466898227864636565038609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112977932151909757710025739 169466898227864636565038609)
              ·
                refine ⟨127100173670898477423778957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169466898227864636565038609 127100173670898477423778957)
                ·
                  refine ⟨47662565126586929033917109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127100173670898477423778957 47662565126586929033917109)
                  ·
                    refine ⟨4468365480617524596929729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47662565126586929033917109 4468365480617524596929729)
                    ·
                      refine ⟨3351274110463143447697297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4468365480617524596929729 3351274110463143447697297)
                      ·
                        rfl

theorem cell23_6526583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 5, 2].length) (baseStart_6526583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526583 prefixEnd_6526583 := by exact prefixLift 6526583
  have htrace : WordTrace (prefixWord ++ tailWord_6526583) baseStart_6526583 baseEnd_6526583 := by
    simpa [prefixWord, tailWord_6526583, baseEnd_6526583] using wordTrace_append hprefix tailTrace_6526583
  have hstable : (prefixWord ++ tailWord_6526583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526583).length < 2 ^ (prefixWord ++ tailWord_6526583).sum := by decide
  have hdescent : baseEnd_6526583 < baseStart_6526583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526593 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 3, 5]
def baseStart_6526593 : Nat := 118140960795 + 6526593 * 2 ^ 59
def prefixEnd_6526593 : Nat := 4983230072969 + 3 ^ 40 * 6526593 * 2
def baseEnd_6526593 : Nat := 1117093081756562802857417

theorem tailTrace_6526593 : CollatzResearch.WordTrace tailWord_6526593 prefixEnd_6526593 1117093081756562802857417 := by
  unfold tailWord_6526593
  simp only [CollatzResearch.WordTrace]
  refine ⟨238044402844275689187424433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158696268562850459458282955 238044402844275689187424433)
  ·
    refine ⟨178533302133206766890568325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238044402844275689187424433 178533302133206766890568325)
    ·
      refine ⟨33474994149976268791981561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178533302133206766890568325 33474994149976268791981561)
      ·
        refine ⟨25106245612482201593986171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33474994149976268791981561 25106245612482201593986171)
        ·
          refine ⟨37659368418723302390979257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25106245612482201593986171 37659368418723302390979257)
          ·
            refine ⟨28244526314042476793234443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37659368418723302390979257 28244526314042476793234443)
            ·
              refine ⟨42366789471063715189851665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28244526314042476793234443 42366789471063715189851665)
              ·
                refine ⟨31775092103297786392388749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42366789471063715189851665 31775092103297786392388749)
                ·
                  refine ⟨11915659538736669897145781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31775092103297786392388749 11915659538736669897145781)
                  ·
                    refine ⟨1117093081756562802857417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11915659538736669897145781 1117093081756562802857417)
                    ·
                      rfl

theorem cell23_6526593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_6526593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526593 prefixEnd_6526593 := by exact prefixLift 6526593
  have htrace : WordTrace (prefixWord ++ tailWord_6526593) baseStart_6526593 baseEnd_6526593 := by
    simpa [prefixWord, tailWord_6526593, baseEnd_6526593] using wordTrace_append hprefix tailTrace_6526593
  have hstable : (prefixWord ++ tailWord_6526593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526593).length < 2 ^ (prefixWord ++ tailWord_6526593).sum := by decide
  have hdescent : baseEnd_6526593 < baseStart_6526593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526624 : List Nat := [2, 1, 1, 4, 3, 2, 2, 3, 1, 1, 3]
def baseStart_6526624 : Nat := 118140960795 + 6526624 * 2 ^ 59
def prefixEnd_6526624 : Nat := 4983230072969 + 3 ^ 40 * 6526624 * 2
def baseEnd_6526624 : Nat := 3351295163169977787284609

theorem tailTrace_6526624 : CollatzResearch.WordTrace tailWord_6526624 prefixEnd_6526624 3351295163169977787284609 := by
  unfold tailWord_6526624
  simp only [CollatzResearch.WordTrace]
  refine ⟨119022766753581690740901463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158697022338108920987868617 119022766753581690740901463)
  ·
    refine ⟨178534150130372536111352195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119022766753581690740901463 178534150130372536111352195)
    ·
      refine ⟨267801225195558804167028293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178534150130372536111352195 267801225195558804167028293)
      ·
        refine ⟨50212729724167275781317805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267801225195558804167028293 50212729724167275781317805)
        ·
          refine ⟨18829773646562728417994177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50212729724167275781317805 18829773646562728417994177)
          ·
            refine ⟨14122330234922046313495633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18829773646562728417994177 14122330234922046313495633)
            ·
              refine ⟨10591747676191534735121725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14122330234922046313495633 10591747676191534735121725)
              ·
                refine ⟨3971905378571825525670647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10591747676191534735121725 3971905378571825525670647)
                ·
                  refine ⟨5957858067857738288505971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3971905378571825525670647 5957858067857738288505971)
                  ·
                    refine ⟨8936787101786607432758957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5957858067857738288505971 8936787101786607432758957)
                    ·
                      refine ⟨3351295163169977787284609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8936787101786607432758957 3351295163169977787284609)
                      ·
                        rfl

theorem cell23_6526624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_6526624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526624 prefixEnd_6526624 := by exact prefixLift 6526624
  have htrace : WordTrace (prefixWord ++ tailWord_6526624) baseStart_6526624 baseEnd_6526624 := by
    simpa [prefixWord, tailWord_6526624, baseEnd_6526624] using wordTrace_append hprefix tailTrace_6526624
  have hstable : (prefixWord ++ tailWord_6526624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526624).length < 2 ^ (prefixWord ++ tailWord_6526624).sum := by decide
  have hdescent : baseEnd_6526624 < baseStart_6526624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526640 : List Nat := [2, 1, 1, 1, 2, 1, 7, 2, 2, 4]
def baseStart_6526640 : Nat := 118140960795 + 6526640 * 2 ^ 59
def prefixEnd_6526640 : Nat := 4983230072969 + 3 ^ 40 * 6526640 * 2
def baseEnd_6526640 : Nat := 1117101126286816574894845

theorem tailTrace_6526640 : CollatzResearch.WordTrace tailWord_6526640 prefixEnd_6526640 1117101126286816574894845 := by
  unfold tailWord_6526640
  simp only [CollatzResearch.WordTrace]
  refine ⟨119023058537552708107192687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158697411383403610809590249 119023058537552708107192687)
  ·
    refine ⟨178534587806329062160789031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119023058537552708107192687 178534587806329062160789031)
    ·
      refine ⟨267801881709493593241183547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178534587806329062160789031 267801881709493593241183547)
      ·
        refine ⟨401702822564240389861775321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267801881709493593241183547 401702822564240389861775321)
        ·
          refine ⟨301277116923180292396331491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401702822564240389861775321 301277116923180292396331491)
          ·
            refine ⟨451915675384770438594497237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301277116923180292396331491 451915675384770438594497237)
            ·
              refine ⟨10591773641830557154558529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 451915675384770438594497237 10591773641830557154558529)
              ·
                refine ⟨7943830231372917865918897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10591773641830557154558529 7943830231372917865918897)
                ·
                  refine ⟨5957872673529688399439173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7943830231372917865918897 5957872673529688399439173)
                  ·
                    refine ⟨1117101126286816574894845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5957872673529688399439173 1117101126286816574894845)
                    ·
                      rfl

theorem cell23_6526640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 2, 4].length) (baseStart_6526640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526640 prefixEnd_6526640 := by exact prefixLift 6526640
  have htrace : WordTrace (prefixWord ++ tailWord_6526640) baseStart_6526640 baseEnd_6526640 := by
    simpa [prefixWord, tailWord_6526640, baseEnd_6526640] using wordTrace_append hprefix tailTrace_6526640
  have hstable : (prefixWord ++ tailWord_6526640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526640).length < 2 ^ (prefixWord ++ tailWord_6526640).sum := by decide
  have hdescent : baseEnd_6526640 < baseStart_6526640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526647 : List Nat := [1, 1, 3, 1, 5, 1, 1, 3, 3, 2, 2]
def baseStart_6526647 : Nat := 118140960795 + 6526647 * 2 ^ 59
def prefixEnd_6526647 : Nat := 4983230072969 + 3 ^ 40 * 6526647 * 2
def baseEnd_6526647 : Nat := 3351306973225031197297003

theorem tailTrace_6526647 : CollatzResearch.WordTrace tailWord_6526647 prefixEnd_6526647 3351306973225031197297003 := by
  unfold tailWord_6526647
  simp only [CollatzResearch.WordTrace]
  refine ⟨238046372386080056409890195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158697581590720037606593463 238046372386080056409890195)
  ·
    refine ⟨357069558579120084614835293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238046372386080056409890195 357069558579120084614835293)
    ·
      refine ⟨133901084467170031730563235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357069558579120084614835293 133901084467170031730563235)
      ·
        refine ⟨200851626700755047595844853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133901084467170031730563235 200851626700755047595844853)
        ·
          refine ⟨18829840003195785712110455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200851626700755047595844853 18829840003195785712110455)
          ·
            refine ⟨28244760004793678568165683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18829840003195785712110455 28244760004793678568165683)
            ·
              refine ⟨42367140007190517852248525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28244760004793678568165683 42367140007190517852248525)
              ·
                refine ⟨15887677502696444194593197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42367140007190517852248525 15887677502696444194593197)
                ·
                  refine ⟨5957879063511166572972449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15887677502696444194593197 5957879063511166572972449)
                  ·
                    refine ⟨4468409297633374929729337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5957879063511166572972449 4468409297633374929729337)
                    ·
                      refine ⟨3351306973225031197297003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4468409297633374929729337 3351306973225031197297003)
                      ·
                        rfl

theorem cell23_6526647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 2, 2].length) (baseStart_6526647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526647 prefixEnd_6526647 := by exact prefixLift 6526647
  have htrace : WordTrace (prefixWord ++ tailWord_6526647) baseStart_6526647 baseEnd_6526647 := by
    simpa [prefixWord, tailWord_6526647, baseEnd_6526647] using wordTrace_append hprefix tailTrace_6526647
  have hstable : (prefixWord ++ tailWord_6526647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526647).length < 2 ^ (prefixWord ++ tailWord_6526647).sum := by decide
  have hdescent : baseEnd_6526647 < baseStart_6526647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526680 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 6, 1, 3]
def baseStart_6526680 : Nat := 118140960795 + 6526680 * 2 ^ 59
def prefixEnd_6526680 : Nat := 4983230072969 + 3 ^ 40 * 6526680 * 2
def baseEnd_6526680 : Nat := 3351323918086629568184351

theorem tailTrace_6526680 : CollatzResearch.WordTrace tailWord_6526680 prefixEnd_6526680 3351323918086629568184351 := by
  unfold tailWord_6526680
  simp only [CollatzResearch.WordTrace]
  refine ⟨119023787997480251522920747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158698383996640335363894329 119023787997480251522920747)
  ·
    refine ⟨178535681996220377284381121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119023787997480251522920747 178535681996220377284381121)
    ·
      refine ⟨133901761497165282963285841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178535681996220377284381121 133901761497165282963285841)
      ·
        refine ⟨100426321122873962222464381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133901761497165282963285841 100426321122873962222464381)
        ·
          refine ⟨37659870421077735833424143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100426321122873962222464381 37659870421077735833424143)
          ·
            refine ⟨56489805631616603750136215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37659870421077735833424143 56489805631616603750136215)
            ·
              refine ⟨84734708447424905625204323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56489805631616603750136215 84734708447424905625204323)
              ·
                refine ⟨127102062671137358437806485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84734708447424905625204323 127102062671137358437806485)
                ·
                  refine ⟨5957909187709563676772179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127102062671137358437806485 5957909187709563676772179)
                  ·
                    refine ⟨8936863781564345515158269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5957909187709563676772179 8936863781564345515158269)
                    ·
                      refine ⟨3351323918086629568184351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8936863781564345515158269 3351323918086629568184351)
                      ·
                        rfl

theorem cell23_6526680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_6526680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526680 prefixEnd_6526680 := by exact prefixLift 6526680
  have htrace : WordTrace (prefixWord ++ tailWord_6526680) baseStart_6526680 baseEnd_6526680 := by
    simpa [prefixWord, tailWord_6526680, baseEnd_6526680] using wordTrace_append hprefix tailTrace_6526680
  have hstable : (prefixWord ++ tailWord_6526680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526680).length < 2 ^ (prefixWord ++ tailWord_6526680).sum := by decide
  have hdescent : baseEnd_6526680 < baseStart_6526680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526681 : List Nat := [1, 2, 1, 2, 3, 5, 1, 3, 1, 2, 2]
def baseStart_6526681 : Nat := 118140960795 + 6526681 * 2 ^ 59
def prefixEnd_6526681 : Nat := 4983230072969 + 3 ^ 40 * 6526681 * 2
def baseEnd_6526681 : Nat := 3351324431567284064271847

theorem tailTrace_6526681 : CollatzResearch.WordTrace tailWord_6526681 prefixEnd_6526681 3351324431567284064271847 := by
  unfold tailWord_6526681
  simp only [CollatzResearch.WordTrace]
  refine ⟨238047612467956880216627897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158698408311971253477751931 238047612467956880216627897)
  ·
    refine ⟨178535709350967660162470923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238047612467956880216627897 178535709350967660162470923)
    ·
      refine ⟨267803564026451490243706385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178535709350967660162470923 267803564026451490243706385)
      ·
        refine ⟨200852673019838617682779789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267803564026451490243706385 200852673019838617682779789)
        ·
          refine ⟨75319752382439481631042421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200852673019838617682779789 75319752382439481631042421)
          ·
            refine ⟨7061226785853701402910227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75319752382439481631042421 7061226785853701402910227)
            ·
              refine ⟨10591840178780552104365341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7061226785853701402910227 10591840178780552104365341)
              ·
                refine ⟨3971940067042707039137003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10591840178780552104365341 3971940067042707039137003)
                ·
                  refine ⟨5957910100564060558705505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3971940067042707039137003 5957910100564060558705505)
                  ·
                    refine ⟨4468432575423045419029129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5957910100564060558705505 4468432575423045419029129)
                    ·
                      refine ⟨3351324431567284064271847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4468432575423045419029129 3351324431567284064271847)
                      ·
                        rfl

theorem cell23_6526681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 1, 2, 2].length) (baseStart_6526681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526681 prefixEnd_6526681 := by exact prefixLift 6526681
  have htrace : WordTrace (prefixWord ++ tailWord_6526681) baseStart_6526681 baseEnd_6526681 := by
    simpa [prefixWord, tailWord_6526681, baseEnd_6526681] using wordTrace_append hprefix tailTrace_6526681
  have hstable : (prefixWord ++ tailWord_6526681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526681).length < 2 ^ (prefixWord ++ tailWord_6526681).sum := by decide
  have hdescent : baseEnd_6526681 < baseStart_6526681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526693 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 2, 2, 5]
def baseStart_6526693 : Nat := 118140960795 + 6526693 * 2 ^ 59
def prefixEnd_6526693 : Nat := 4983230072969 + 3 ^ 40 * 6526693 * 2
def baseEnd_6526693 : Nat := 3351330593335138017321791

theorem tailTrace_6526693 : CollatzResearch.WordTrace tailWord_6526693 prefixEnd_6526693 3351330593335138017321791 := by
  unfold tailWord_6526693
  simp only [CollatzResearch.WordTrace]
  refine ⟨238048050143913406266064733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158698700095942270844043155 238048050143913406266064733)
  ·
    refine ⟨89268018803967527349774275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238048050143913406266064733 89268018803967527349774275)
    ·
      refine ⟨133902028205951291024661413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89268018803967527349774275 133902028205951291024661413)
      ·
        refine ⟨25106630288615867067124015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133902028205951291024661413 25106630288615867067124015)
        ·
          refine ⟨37659945432923800600686023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25106630288615867067124015 37659945432923800600686023)
          ·
            refine ⟨56489918149385700901029035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37659945432923800600686023 56489918149385700901029035)
            ·
              refine ⟨84734877224078551351543553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56489918149385700901029035 84734877224078551351543553)
              ·
                refine ⟨63551157918058913513657665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84734877224078551351543553 63551157918058913513657665)
                ·
                  refine ⟨47663368438544185135243249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63551157918058913513657665 47663368438544185135243249)
                  ·
                    refine ⟨35747526328908138851432437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47663368438544185135243249 35747526328908138851432437)
                    ·
                      refine ⟨3351330593335138017321791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35747526328908138851432437 3351330593335138017321791)
                      ·
                        rfl

theorem cell23_6526693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_6526693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526693 prefixEnd_6526693 := by exact prefixLift 6526693
  have htrace : WordTrace (prefixWord ++ tailWord_6526693) baseStart_6526693 baseEnd_6526693 := by
    simpa [prefixWord, tailWord_6526693, baseEnd_6526693] using wordTrace_append hprefix tailTrace_6526693
  have hstable : (prefixWord ++ tailWord_6526693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526693).length < 2 ^ (prefixWord ++ tailWord_6526693).sum := by decide
  have hdescent : baseEnd_6526693 < baseStart_6526693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526703 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 4]
def baseStart_6526703 : Nat := 118140960795 + 6526703 * 2 ^ 59
def prefixEnd_6526703 : Nat := 4983230072969 + 3 ^ 40 * 6526703 * 2
def baseEnd_6526703 : Nat := 3351335728141682978196745

theorem tailTrace_6526703 : CollatzResearch.WordTrace tailWord_6526703 prefixEnd_6526703 3351335728141682978196745 := by
  unfold tailWord_6526703
  simp only [CollatzResearch.WordTrace]
  refine ⟨238048414873877177973928763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158698943249251451982619175 238048414873877177973928763)
  ·
    refine ⟨357072622310815766960893145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238048414873877177973928763 357072622310815766960893145)
    ·
      refine ⟨267804466733111825220669859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357072622310815766960893145 267804466733111825220669859)
      ·
        refine ⟨401706700099667737831004789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267804466733111825220669859 401706700099667737831004789)
        ·
          refine ⟨37660003134343850421656699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 401706700099667737831004789 37660003134343850421656699)
          ·
            refine ⟨56490004701515775632485049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37660003134343850421656699 56490004701515775632485049)
            ·
              refine ⟨42367503526136831724363787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56490004701515775632485049 42367503526136831724363787)
              ·
                refine ⟨63551255289205247586545681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42367503526136831724363787 63551255289205247586545681)
                ·
                  refine ⟨47663441466903935689909261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63551255289205247586545681 47663441466903935689909261)
                  ·
                    refine ⟨17873790550088975883715973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47663441466903935689909261 17873790550088975883715973)
                    ·
                      refine ⟨3351335728141682978196745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17873790550088975883715973 3351335728141682978196745)
                      ·
                        rfl

theorem cell23_6526703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_6526703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526703 prefixEnd_6526703 := by exact prefixLift 6526703
  have htrace : WordTrace (prefixWord ++ tailWord_6526703) baseStart_6526703 baseEnd_6526703 := by
    simpa [prefixWord, tailWord_6526703, baseEnd_6526703] using wordTrace_append hprefix tailTrace_6526703
  have hstable : (prefixWord ++ tailWord_6526703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526703).length < 2 ^ (prefixWord ++ tailWord_6526703).sum := by decide
  have hdescent : baseEnd_6526703 < baseStart_6526703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526708 : List Nat := [2, 6, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_6526708 : Nat := 118140960795 + 6526708 * 2 ^ 59
def prefixEnd_6526708 : Nat := 4983230072969 + 3 ^ 40 * 6526708 * 2
def baseEnd_6526708 : Nat := 1117112765181651819544741

theorem tailTrace_6526708 : CollatzResearch.WordTrace tailWord_6526708 prefixEnd_6526708 1117112765181651819544741 := by
  unfold tailWord_6526708
  simp only [CollatzResearch.WordTrace]
  refine ⟨119024298619429531913930389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158699064825906042551907185 119024298619429531913930389)
  ·
    refine ⟨5579263997785759308465487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 119024298619429531913930389 5579263997785759308465487)
    ·
      refine ⟨8368895996678638962698231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5579263997785759308465487 8368895996678638962698231)
      ·
        refine ⟨12553343995017958444047347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8368895996678638962698231 12553343995017958444047347)
        ·
          refine ⟨18830015992526937666071021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12553343995017958444047347 18830015992526937666071021)
          ·
            refine ⟨7061255997197601624776633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18830015992526937666071021 7061255997197601624776633)
            ·
              refine ⟨5295941997898201218582475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7061255997197601624776633 5295941997898201218582475)
              ·
                refine ⟨7943912996847301827873713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5295941997898201218582475 7943912996847301827873713)
                ·
                  refine ⟨5957934747635476370905285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7943912996847301827873713 5957934747635476370905285)
                  ·
                    refine ⟨1117112765181651819544741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5957934747635476370905285 1117112765181651819544741)
                    ·
                      rfl

theorem cell23_6526708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_6526708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526708 prefixEnd_6526708 := by exact prefixLift 6526708
  have htrace : WordTrace (prefixWord ++ tailWord_6526708) baseStart_6526708 baseEnd_6526708 := by
    simpa [prefixWord, tailWord_6526708, baseEnd_6526708] using wordTrace_append hprefix tailTrace_6526708
  have hstable : (prefixWord ++ tailWord_6526708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526708).length < 2 ^ (prefixWord ++ tailWord_6526708).sum := by decide
  have hdescent : baseEnd_6526708 < baseStart_6526708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526723 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 5]
def baseStart_6526723 : Nat := 118140960795 + 6526723 * 2 ^ 59
def prefixEnd_6526723 : Nat := 4983230072969 + 3 ^ 40 * 6526723 * 2
def baseEnd_6526723 : Nat := 3351345997754772899946653

theorem tailTrace_6526723 : CollatzResearch.WordTrace tailWord_6526723 prefixEnd_6526723 3351345997754772899946653 := by
  unfold tailWord_6526723
  simp only [CollatzResearch.WordTrace]
  refine ⟨238049144333804721389656823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158699429555869814259771215 238049144333804721389656823)
  ·
    refine ⟨357073716500707082084485235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238049144333804721389656823 357073716500707082084485235)
    ·
      refine ⟨535610574751060623126727853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357073716500707082084485235 535610574751060623126727853)
      ·
        refine ⟨200853965531647733672522945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 535610574751060623126727853 200853965531647733672522945)
        ·
          refine ⟨150640474148735800254392209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200853965531647733672522945 150640474148735800254392209)
          ·
            refine ⟨112980355611551850190794157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150640474148735800254392209 112980355611551850190794157)
            ·
              refine ⟨42367633354331943821547809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112980355611551850190794157 42367633354331943821547809)
              ·
                refine ⟨31775725015748957866160857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42367633354331943821547809 31775725015748957866160857)
                ·
                  refine ⟨23831793761811718399620643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31775725015748957866160857 23831793761811718399620643)
                  ·
                    refine ⟨35747690642717577599430965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23831793761811718399620643 35747690642717577599430965)
                    ·
                      refine ⟨3351345997754772899946653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35747690642717577599430965 3351345997754772899946653)
                      ·
                        rfl

theorem cell23_6526723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_6526723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526723 prefixEnd_6526723 := by exact prefixLift 6526723
  have htrace : WordTrace (prefixWord ++ tailWord_6526723) baseStart_6526723 baseEnd_6526723 := by
    simpa [prefixWord, tailWord_6526723, baseEnd_6526723] using wordTrace_append hprefix tailTrace_6526723
  have hstable : (prefixWord ++ tailWord_6526723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526723).length < 2 ^ (prefixWord ++ tailWord_6526723).sum := by decide
  have hdescent : baseEnd_6526723 < baseStart_6526723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526724 : List Nat := [2, 3, 2, 2, 1, 2, 3, 2, 1, 3, 2]
def baseStart_6526724 : Nat := 118140960795 + 6526724 * 2 ^ 59
def prefixEnd_6526724 : Nat := 4983230072969 + 3 ^ 40 * 6526724 * 2
def baseEnd_6526724 : Nat := 3351346511235427396034149

theorem tailTrace_6526724 : CollatzResearch.WordTrace tailWord_6526724 prefixEnd_6526724 3351346511235427396034149 := by
  unfold tailWord_6526724
  simp only [CollatzResearch.WordTrace]
  refine ⟨119024590403400549280221613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158699453871200732373628817 119024590403400549280221613)
  ·
    refine ⟨44634221401275205980083105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119024590403400549280221613 44634221401275205980083105)
    ·
      refine ⟨33475666050956404485062329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44634221401275205980083105 33475666050956404485062329)
      ·
        refine ⟨25106749538217303363796747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33475666050956404485062329 25106749538217303363796747)
        ·
          refine ⟨37660124307325955045695121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25106749538217303363796747 37660124307325955045695121)
          ·
            refine ⟨28245093230494466284271341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37660124307325955045695121 28245093230494466284271341)
            ·
              refine ⟨10591909961435424856601753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28245093230494466284271341 10591909961435424856601753)
              ·
                refine ⟨7943932471076568642451315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10591909961435424856601753 7943932471076568642451315)
                ·
                  refine ⟨11915898706614852963676973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7943932471076568642451315 11915898706614852963676973)
                  ·
                    refine ⟨4468462014980569861378865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11915898706614852963676973 4468462014980569861378865)
                    ·
                      refine ⟨3351346511235427396034149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4468462014980569861378865 3351346511235427396034149)
                      ·
                        rfl

theorem cell23_6526724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_6526724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526724 prefixEnd_6526724 := by exact prefixLift 6526724
  have htrace : WordTrace (prefixWord ++ tailWord_6526724) baseStart_6526724 baseEnd_6526724 := by
    simpa [prefixWord, tailWord_6526724, baseEnd_6526724] using wordTrace_append hprefix tailTrace_6526724
  have hstable : (prefixWord ++ tailWord_6526724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526724).length < 2 ^ (prefixWord ++ tailWord_6526724).sum := by decide
  have hdescent : baseEnd_6526724 < baseStart_6526724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526770 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3]
def baseStart_6526770 : Nat := 118140960795 + 6526770 * 2 ^ 59
def prefixEnd_6526770 : Nat := 4983230072969 + 3 ^ 40 * 6526770 * 2
def baseEnd_6526770 : Nat := 3351370131345534216058937

theorem tailTrace_6526770 : CollatzResearch.WordTrace tailWord_6526770 prefixEnd_6526770 3351370131345534216058937 := by
  unfold tailWord_6526770
  simp only [CollatzResearch.WordTrace]
  refine ⟨59512714641158612104154441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158700572376422965611078509 59512714641158612104154441)
  ·
    refine ⟨44634535980868959078115831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59512714641158612104154441 44634535980868959078115831)
    ·
      refine ⟨66951803971303438617173747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44634535980868959078115831 66951803971303438617173747)
      ·
        refine ⟨100427705956955157925760621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66951803971303438617173747 100427705956955157925760621)
        ·
          refine ⟨37660389733858184222160233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100427705956955157925760621 37660389733858184222160233)
          ·
            refine ⟨28245292300393638166620175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37660389733858184222160233 28245292300393638166620175)
            ·
              refine ⟨42367938450590457249930263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28245292300393638166620175 42367938450590457249930263)
              ·
                refine ⟨63551907675885685874895395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42367938450590457249930263 63551907675885685874895395)
                ·
                  refine ⟨95327861513828528812343093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63551907675885685874895395 95327861513828528812343093)
                  ·
                    refine ⟨8936987016921424576157165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95327861513828528812343093 8936987016921424576157165)
                    ·
                      refine ⟨3351370131345534216058937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8936987016921424576157165 3351370131345534216058937)
                      ·
                        rfl

theorem cell23_6526770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_6526770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526770 prefixEnd_6526770 := by exact prefixLift 6526770
  have htrace : WordTrace (prefixWord ++ tailWord_6526770) baseStart_6526770 baseEnd_6526770 := by
    simpa [prefixWord, tailWord_6526770, baseEnd_6526770] using wordTrace_append hprefix tailTrace_6526770
  have hstable : (prefixWord ++ tailWord_6526770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526770).length < 2 ^ (prefixWord ++ tailWord_6526770).sum := by decide
  have hdescent : baseEnd_6526770 < baseStart_6526770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526777 : List Nat := [1, 2, 1, 7, 1, 1, 1, 2, 7]
def baseStart_6526777 : Nat := 118140960795 + 6526777 * 2 ^ 59
def prefixEnd_6526777 : Nat := 4983230072969 + 3 ^ 40 * 6526777 * 2
def baseEnd_6526777 : Nat := 372374858412235076519045

theorem tailTrace_6526777 : CollatzResearch.WordTrace tailWord_6526777 prefixEnd_6526777 372374858412235076519045 := by
  unfold tailWord_6526777
  simp only [CollatzResearch.WordTrace]
  refine ⟨238051113875609088612122585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158700742583739392408081723 238051113875609088612122585)
  ·
    refine ⟨178538335406706816459091939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238051113875609088612122585 178538335406706816459091939)
    ·
      refine ⟨267807503110060224688637909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178538335406706816459091939 267807503110060224688637909)
      ·
        refine ⟨6276738354142036516139951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 267807503110060224688637909 6276738354142036516139951)
        ·
          refine ⟨9415107531213054774209927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6276738354142036516139951 9415107531213054774209927)
          ·
            refine ⟨14122661296819582161314891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9415107531213054774209927 14122661296819582161314891)
            ·
              refine ⟨21183991945229373241972337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14122661296819582161314891 21183991945229373241972337)
              ·
                refine ⟨15887993958922029931479253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21183991945229373241972337 15887993958922029931479253)
                ·
                  refine ⟨372374858412235076519045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15887993958922029931479253 372374858412235076519045)
                  ·
                    rfl

theorem cell23_6526777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 7].length) (baseStart_6526777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526777 prefixEnd_6526777 := by exact prefixLift 6526777
  have htrace : WordTrace (prefixWord ++ tailWord_6526777) baseStart_6526777 baseEnd_6526777 := by
    simpa [prefixWord, tailWord_6526777, baseEnd_6526777] using wordTrace_append hprefix tailTrace_6526777
  have hstable : (prefixWord ++ tailWord_6526777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526777).length < 2 ^ (prefixWord ++ tailWord_6526777).sum := by decide
  have hdescent : baseEnd_6526777 < baseStart_6526777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526810 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4]
def baseStart_6526810 : Nat := 118140960795 + 6526810 * 2 ^ 59
def prefixEnd_6526810 : Nat := 4983230072969 + 3 ^ 40 * 6526810 * 2
def baseEnd_6526810 : Nat := 3351390670571714059558753

theorem tailTrace_6526810 : CollatzResearch.WordTrace tailWord_6526810 prefixEnd_6526810 3351390670571714059558753 := by
  unfold tailWord_6526810
  simp only [CollatzResearch.WordTrace]
  refine ⟨59513079371122383812018471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158701544989659690165382589 59513079371122383812018471)
  ·
    refine ⟨89269619056683575718027707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59513079371122383812018471 89269619056683575718027707)
    ·
      refine ⟨133904428585025363577041561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89269619056683575718027707 133904428585025363577041561)
      ·
        refine ⟨100428321438769022682781171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133904428585025363577041561 100428321438769022682781171)
        ·
          refine ⟨150642482158153534024171757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100428321438769022682781171 150642482158153534024171757)
          ·
            refine ⟨56490930809307575259064409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150642482158153534024171757 56490930809307575259064409)
            ·
              refine ⟨42368198106980681444298307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56490930809307575259064409 42368198106980681444298307)
              ·
                refine ⟨63552297160471022166447461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42368198106980681444298307 63552297160471022166447461)
                ·
                  refine ⟨11916055717588316656208899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63552297160471022166447461 11916055717588316656208899)
                  ·
                    refine ⟨17874083576382474984313349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11916055717588316656208899 17874083576382474984313349)
                    ·
                      refine ⟨3351390670571714059558753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17874083576382474984313349 3351390670571714059558753)
                      ·
                        rfl

theorem cell23_6526810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_6526810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526810 prefixEnd_6526810 := by exact prefixLift 6526810
  have htrace : WordTrace (prefixWord ++ tailWord_6526810) baseStart_6526810 baseEnd_6526810 := by
    simpa [prefixWord, tailWord_6526810, baseEnd_6526810] using wordTrace_append hprefix tailTrace_6526810
  have hstable : (prefixWord ++ tailWord_6526810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526810).length < 2 ^ (prefixWord ++ tailWord_6526810).sum := by decide
  have hdescent : baseEnd_6526810 < baseStart_6526810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526837 : List Nat := [1, 3, 4, 1, 1, 1, 1, 4, 3, 4]
def baseStart_6526837 : Nat := 118140960795 + 6526837 * 2 ^ 59
def prefixEnd_6526837 : Nat := 4983230072969 + 3 ^ 40 * 6526837 * 2
def baseEnd_6526837 : Nat := 1117134844849795151307043

theorem tailTrace_6526837 : CollatzResearch.WordTrace tailWord_6526837 prefixEnd_6526837 1117134844849795151307043 := by
  unfold tailWord_6526837
  simp only [CollatzResearch.WordTrace]
  refine ⟨238053302255391718859306765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158702201503594479239537843 238053302255391718859306765)
  ·
    refine ⟨89269988345771894572240037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238053302255391718859306765 89269988345771894572240037)
    ·
      refine ⟨16738122814832230232295007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89269988345771894572240037 16738122814832230232295007)
      ·
        refine ⟨25107184222248345348442511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16738122814832230232295007 25107184222248345348442511)
        ·
          refine ⟨37660776333372518022663767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25107184222248345348442511 37660776333372518022663767)
          ·
            refine ⟨56491164500058777033995651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37660776333372518022663767 56491164500058777033995651)
            ·
              refine ⟨84736746750088165550993477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56491164500058777033995651 84736746750088165550993477)
              ·
                refine ⟨15888140015641531040811277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84736746750088165550993477 15888140015641531040811277)
                ·
                  refine ⟨5958052505865574140304229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15888140015641531040811277 5958052505865574140304229)
                  ·
                    refine ⟨1117134844849795151307043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5958052505865574140304229 1117134844849795151307043)
                    ·
                      rfl

theorem cell23_6526837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_6526837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526837 prefixEnd_6526837 := by exact prefixLift 6526837
  have htrace : WordTrace (prefixWord ++ tailWord_6526837) baseStart_6526837 baseEnd_6526837 := by
    simpa [prefixWord, tailWord_6526837, baseEnd_6526837] using wordTrace_append hprefix tailTrace_6526837
  have hstable : (prefixWord ++ tailWord_6526837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526837).length < 2 ^ (prefixWord ++ tailWord_6526837).sum := by decide
  have hdescent : baseEnd_6526837 < baseStart_6526837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526863 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 3, 11]
def baseStart_6526863 : Nat := 118140960795 + 6526863 * 2 ^ 59
def prefixEnd_6526863 : Nat := 4983230072969 + 3 ^ 40 * 6526863 * 2
def baseEnd_6526863 : Nat := 1117139295015467450732003

theorem tailTrace_6526863 : CollatzResearch.WordTrace tailWord_6526863 prefixEnd_6526863 1117139295015467450732003 := by
  unfold tailWord_6526863
  simp only [CollatzResearch.WordTrace]
  refine ⟨238054250553297525299753243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158702833702198350199835495 238054250553297525299753243)
  ·
    refine ⟨357081375829946287949629865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238054250553297525299753243 357081375829946287949629865)
    ·
      refine ⟨267811031872459715962222399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357081375829946287949629865 267811031872459715962222399)
      ·
        refine ⟨401716547808689573943333599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267811031872459715962222399 401716547808689573943333599)
        ·
          refine ⟨602574821713034360915000399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401716547808689573943333599 602574821713034360915000399)
          ·
            refine ⟨903862232569551541372500599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602574821713034360915000399 903862232569551541372500599)
            ·
              refine ⟨1355793348854327312058750899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903862232569551541372500599 1355793348854327312058750899)
              ·
                refine ⟨2033690023281490968088126349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355793348854327312058750899 2033690023281490968088126349)
                ·
                  refine ⟨762633758730559113033047381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2033690023281490968088126349 762633758730559113033047381)
                  ·
                    refine ⟨1117139295015467450732003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 762633758730559113033047381 1117139295015467450732003)
                    ·
                      rfl

theorem cell23_6526863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 11].length) (baseStart_6526863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526863 prefixEnd_6526863 := by exact prefixLift 6526863
  have htrace : WordTrace (prefixWord ++ tailWord_6526863) baseStart_6526863 baseEnd_6526863 := by
    simpa [prefixWord, tailWord_6526863, baseEnd_6526863] using wordTrace_append hprefix tailTrace_6526863
  have hstable : (prefixWord ++ tailWord_6526863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526863).length < 2 ^ (prefixWord ++ tailWord_6526863).sum := by decide
  have hdescent : baseEnd_6526863 < baseStart_6526863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526871 : List Nat := [1, 1, 3, 3, 1, 4, 3, 2, 1, 4]
def baseStart_6526871 : Nat := 118140960795 + 6526871 * 2 ^ 59
def prefixEnd_6526871 : Nat := 4983230072969 + 3 ^ 40 * 6526871 * 2
def baseEnd_6526871 : Nat := 1117140664297212773631991

theorem tailTrace_6526871 : CollatzResearch.WordTrace tailWord_6526871 prefixEnd_6526871 1117140664297212773631991 := by
  unfold tailWord_6526871
  simp only [CollatzResearch.WordTrace]
  refine ⟨238054542337268542666044467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158703028224845695110696311 238054542337268542666044467)
  ·
    refine ⟨357081813505902813999066701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238054542337268542666044467 357081813505902813999066701)
    ·
      refine ⟨133905680064713555249650013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357081813505902813999066701 133905680064713555249650013)
      ·
        refine ⟨50214630024267583218618755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133905680064713555249650013 50214630024267583218618755)
        ·
          refine ⟨75321945036401374827928133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50214630024267583218618755 75321945036401374827928133)
          ·
            refine ⟨14122864694325257780236525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75321945036401374827928133 14122864694325257780236525)
            ·
              refine ⟨5296074260371971667588697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14122864694325257780236525 5296074260371971667588697)
              ·
                refine ⟨3972055695278978750691523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5296074260371971667588697 3972055695278978750691523)
                ·
                  refine ⟨5958083542918468126037285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3972055695278978750691523 5958083542918468126037285)
                  ·
                    refine ⟨1117140664297212773631991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5958083542918468126037285 1117140664297212773631991)
                    ·
                      rfl

theorem cell23_6526871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 1, 4].length) (baseStart_6526871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526871 prefixEnd_6526871 := by exact prefixLift 6526871
  have htrace : WordTrace (prefixWord ++ tailWord_6526871) baseStart_6526871 baseEnd_6526871 := by
    simpa [prefixWord, tailWord_6526871, baseEnd_6526871] using wordTrace_append hprefix tailTrace_6526871
  have hstable : (prefixWord ++ tailWord_6526871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526871).length < 2 ^ (prefixWord ++ tailWord_6526871).sum := by decide
  have hdescent : baseEnd_6526871 < baseStart_6526871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526880 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 3, 5]
def baseStart_6526880 : Nat := 118140960795 + 6526880 * 2 ^ 59
def prefixEnd_6526880 : Nat := 4983230072969 + 3 ^ 40 * 6526880 * 2
def baseEnd_6526880 : Nat := 1117142204739176261894477

theorem tailTrace_6526880 : CollatzResearch.WordTrace tailWord_6526880 prefixEnd_6526880 1117142204739176261894477 := by
  unfold tailWord_6526880
  simp only [CollatzResearch.WordTrace]
  refine ⟨119027435297117968601561047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158703247062823958135414729 119027435297117968601561047)
  ·
    refine ⟨178541152945676952902341571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119027435297117968601561047 178541152945676952902341571)
    ·
      refine ⟨267811729418515429353512357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178541152945676952902341571 267811729418515429353512357)
      ·
        refine ⟨50214699265971643003783567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267811729418515429353512357 50214699265971643003783567)
        ·
          refine ⟨75322048898957464505675351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50214699265971643003783567 75322048898957464505675351)
          ·
            refine ⟨112983073348436196758513027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75322048898957464505675351 112983073348436196758513027)
            ·
              refine ⟨169474610022654295137769541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112983073348436196758513027 169474610022654295137769541)
              ·
                refine ⟨31776489379247680338331789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169474610022654295137769541 31776489379247680338331789)
                ·
                  refine ⟨11916183517217880126874421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31776489379247680338331789 11916183517217880126874421)
                  ·
                    refine ⟨1117142204739176261894477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11916183517217880126874421 1117142204739176261894477)
                    ·
                      rfl

theorem cell23_6526880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 3, 5].length) (baseStart_6526880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526880 prefixEnd_6526880 := by exact prefixLift 6526880
  have htrace : WordTrace (prefixWord ++ tailWord_6526880) baseStart_6526880 baseEnd_6526880 := by
    simpa [prefixWord, tailWord_6526880, baseEnd_6526880] using wordTrace_append hprefix tailTrace_6526880
  have hstable : (prefixWord ++ tailWord_6526880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526880).length < 2 ^ (prefixWord ++ tailWord_6526880).sum := by decide
  have hdescent : baseEnd_6526880 < baseStart_6526880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526884 : List Nat := [2, 3, 1, 2, 1, 5, 2, 1, 6]
def baseStart_6526884 : Nat := 118140960795 + 6526884 * 2 ^ 59
def prefixEnd_6526884 : Nat := 4983230072969 + 3 ^ 40 * 6526884 * 2
def baseEnd_6526884 : Nat := 372380963126682974448157

theorem tailTrace_6526884 : CollatzResearch.WordTrace tailWord_6526884 prefixEnd_6526884 372380963126682974448157 := by
  unfold tailWord_6526884
  simp only [CollatzResearch.WordTrace]
  refine ⟨119027508243110722943133853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158703344324147630590845137 119027508243110722943133853)
  ·
    refine ⟨44635315591166521103675195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119027508243110722943133853 44635315591166521103675195)
    ·
      refine ⟨66952973386749781655512793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44635315591166521103675195 66952973386749781655512793)
      ·
        refine ⟨50214730040062336241634595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66952973386749781655512793 50214730040062336241634595)
        ·
          refine ⟨75322095060093504362451893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50214730040062336241634595 75322095060093504362451893)
          ·
            refine ⟨7061446411883766033979865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75322095060093504362451893 7061446411883766033979865)
            ·
              refine ⟨5296084808912824525484899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7061446411883766033979865 5296084808912824525484899)
              ·
                refine ⟨7944127213369236788227349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5296084808912824525484899 7944127213369236788227349)
                ·
                  refine ⟨372380963126682974448157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7944127213369236788227349 372380963126682974448157)
                  ·
                    rfl

theorem cell23_6526884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_6526884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526884 prefixEnd_6526884 := by exact prefixLift 6526884
  have htrace : WordTrace (prefixWord ++ tailWord_6526884) baseStart_6526884 baseEnd_6526884 := by
    simpa [prefixWord, tailWord_6526884, baseEnd_6526884] using wordTrace_append hprefix tailTrace_6526884
  have hstable : (prefixWord ++ tailWord_6526884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526884).length < 2 ^ (prefixWord ++ tailWord_6526884).sum := by decide
  have hdescent : baseEnd_6526884 < baseStart_6526884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526897 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 3, 5]
def baseStart_6526897 : Nat := 118140960795 + 6526897 * 2 ^ 59
def prefixEnd_6526897 : Nat := 4983230072969 + 3 ^ 40 * 6526897 * 2
def baseEnd_6526897 : Nat := 1117145114462885073056951

theorem tailTrace_6526897 : CollatzResearch.WordTrace tailWord_6526897 prefixEnd_6526897 1117145114462885073056951 := by
  unfold tailWord_6526897
  simp only [CollatzResearch.WordTrace]
  refine ⟨238055490635174349106490945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158703660423449566070993963 238055490635174349106490945)
  ·
    refine ⟨178541617976380761829868209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238055490635174349106490945 178541617976380761829868209)
    ·
      refine ⟨133906213482285571372401157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178541617976380761829868209 133906213482285571372401157)
      ·
        refine ⟨25107415027928544632325217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133906213482285571372401157 25107415027928544632325217)
        ·
          refine ⟨18830561270946408474243913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25107415027928544632325217 18830561270946408474243913)
          ·
            refine ⟨14122920953209806355682935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18830561270946408474243913 14122920953209806355682935)
            ·
              refine ⟨21184381429814709533524403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14122920953209806355682935 21184381429814709533524403)
              ·
                refine ⟨31776572144722064300286605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21184381429814709533524403 31776572144722064300286605)
                ·
                  refine ⟨11916214554270774112607477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31776572144722064300286605 11916214554270774112607477)
                  ·
                    refine ⟨1117145114462885073056951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11916214554270774112607477 1117145114462885073056951)
                    ·
                      rfl

theorem cell23_6526897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_6526897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526897 prefixEnd_6526897 := by exact prefixLift 6526897
  have htrace : WordTrace (prefixWord ++ tailWord_6526897) baseStart_6526897 baseEnd_6526897 := by
    simpa [prefixWord, tailWord_6526897, baseEnd_6526897] using wordTrace_append hprefix tailTrace_6526897
  have hstable : (prefixWord ++ tailWord_6526897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526897).length < 2 ^ (prefixWord ++ tailWord_6526897).sum := by decide
  have hdescent : baseEnd_6526897 < baseStart_6526897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526904 : List Nat := [2, 1, 2, 1, 2, 3, 4, 1, 2, 3, 2]
def baseStart_6526904 : Nat := 118140960795 + 6526904 * 2 ^ 59
def prefixEnd_6526904 : Nat := 4983230072969 + 3 ^ 40 * 6526904 * 2
def baseEnd_6526904 : Nat := 3351438937753236691783321

theorem tailTrace_6526904 : CollatzResearch.WordTrace tailWord_6526904 prefixEnd_6526904 3351438937753236691783321 := by
  unfold tailWord_6526904
  simp only [CollatzResearch.WordTrace]
  refine ⟨119027872973074494650997883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158703830630765992867997177 119027872973074494650997883)
  ·
    refine ⟨178541809459611741976496825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119027872973074494650997883 178541809459611741976496825)
    ·
      refine ⟨133906357094708806482372619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178541809459611741976496825 133906357094708806482372619)
      ·
        refine ⟨200859535642063209723558929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133906357094708806482372619 200859535642063209723558929)
        ·
          refine ⟨150644651731547407292669197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200859535642063209723558929 150644651731547407292669197)
          ·
            refine ⟨56491744399330277734750949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150644651731547407292669197 56491744399330277734750949)
            ·
              refine ⟨10592202074874427075265803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56491744399330277734750949 10592202074874427075265803)
              ·
                refine ⟨15888303112311640612898705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10592202074874427075265803 15888303112311640612898705)
                ·
                  refine ⟨11916227334233730459674029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15888303112311640612898705 11916227334233730459674029)
                  ·
                    refine ⟨4468585250337648922377761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11916227334233730459674029 4468585250337648922377761)
                    ·
                      refine ⟨3351438937753236691783321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4468585250337648922377761 3351438937753236691783321)
                      ·
                        rfl

theorem cell23_6526904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 2, 3, 2].length) (baseStart_6526904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526904 prefixEnd_6526904 := by exact prefixLift 6526904
  have htrace : WordTrace (prefixWord ++ tailWord_6526904) baseStart_6526904 baseEnd_6526904 := by
    simpa [prefixWord, tailWord_6526904, baseEnd_6526904] using wordTrace_append hprefix tailTrace_6526904
  have hstable : (prefixWord ++ tailWord_6526904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526904).length < 2 ^ (prefixWord ++ tailWord_6526904).sum := by decide
  have hdescent : baseEnd_6526904 < baseStart_6526904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526947 : List Nat := [1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 4]
def baseStart_6526947 : Nat := 118140960795 + 6526947 * 2 ^ 59
def prefixEnd_6526947 : Nat := 4983230072969 + 3 ^ 40 * 6526947 * 2
def baseEnd_6526947 : Nat := 3351461017421380023545623

theorem tailTrace_6526947 : CollatzResearch.WordTrace tailWord_6526947 prefixEnd_6526947 3351461017421380023545623 := by
  unfold tailWord_6526947
  simp only [CollatzResearch.WordTrace]
  refine ⟨238057314284993207645811095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158704876189995471763874063 238057314284993207645811095)
  ·
    refine ⟨357085971427489811468716643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238057314284993207645811095 357085971427489811468716643)
    ·
      refine ⟨535628957141234717203074965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357085971427489811468716643 535628957141234717203074965)
      ·
        refine ⟨25107607365995377368894139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 535628957141234717203074965 25107607365995377368894139)
        ·
          refine ⟨37661411048993066053341209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25107607365995377368894139 37661411048993066053341209)
          ·
            refine ⟨28246058286744799540005907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37661411048993066053341209 28246058286744799540005907)
            ·
              refine ⟨42369087430117199310008861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28246058286744799540005907 42369087430117199310008861)
              ·
                refine ⟨15888407786293949741253323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42369087430117199310008861 15888407786293949741253323)
                ·
                  refine ⟨23832611679440924611879985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15888407786293949741253323 23832611679440924611879985)
                  ·
                    refine ⟨17874458759580693458909989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23832611679440924611879985 17874458759580693458909989)
                    ·
                      refine ⟨3351461017421380023545623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17874458759580693458909989 3351461017421380023545623)
                      ·
                        rfl

theorem cell23_6526947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_6526947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526947 prefixEnd_6526947 := by exact prefixLift 6526947
  have htrace : WordTrace (prefixWord ++ tailWord_6526947) baseStart_6526947 baseEnd_6526947 := by
    simpa [prefixWord, tailWord_6526947, baseEnd_6526947] using wordTrace_append hprefix tailTrace_6526947
  have hstable : (prefixWord ++ tailWord_6526947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526947).length < 2 ^ (prefixWord ++ tailWord_6526947).sum := by decide
  have hdescent : baseEnd_6526947 < baseStart_6526947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526954 : List Nat := [3, 1, 3, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_6526954 : Nat := 118140960795 + 6526954 * 2 ^ 59
def prefixEnd_6526954 : Nat := 4983230072969 + 3 ^ 40 * 6526954 * 2
def baseEnd_6526954 : Nat := 3351464611785961496158091

theorem tailTrace_6526954 : CollatzResearch.WordTrace tailWord_6526954 prefixEnd_6526954 3351464611785961496158091 := by
  unfold tailWord_6526954
  simp only [CollatzResearch.WordTrace]
  refine ⟨59514392398991961960328979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158705046397311898560877277 59514392398991961960328979)
  ·
    refine ⟨89271588598487942940493469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59514392398991961960328979 89271588598487942940493469)
    ·
      refine ⟨33476845724432978602685051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89271588598487942940493469 33476845724432978602685051)
      ·
        refine ⟨50215268586649467904027577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33476845724432978602685051 50215268586649467904027577)
        ·
          refine ⟨37661451439987100928020683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50215268586649467904027577 37661451439987100928020683)
          ·
            refine ⟨56492177159980651392031025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37661451439987100928020683 56492177159980651392031025)
            ·
              refine ⟨42369132869985488544023269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56492177159980651392031025 42369132869985488544023269)
              ·
                refine ⟨7944212413122279102004363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42369132869985488544023269 7944212413122279102004363)
                ·
                  refine ⟨11916318619683418653006545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7944212413122279102004363 11916318619683418653006545)
                  ·
                    refine ⟨8937238964762563989754909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11916318619683418653006545 8937238964762563989754909)
                    ·
                      refine ⟨3351464611785961496158091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8937238964762563989754909 3351464611785961496158091)
                      ·
                        rfl

theorem cell23_6526954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_6526954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526954 prefixEnd_6526954 := by exact prefixLift 6526954
  have htrace : WordTrace (prefixWord ++ tailWord_6526954) baseStart_6526954 baseEnd_6526954 := by
    simpa [prefixWord, tailWord_6526954, baseEnd_6526954] using wordTrace_append hprefix tailTrace_6526954
  have hstable : (prefixWord ++ tailWord_6526954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526954).length < 2 ^ (prefixWord ++ tailWord_6526954).sum := by decide
  have hdescent : baseEnd_6526954 < baseStart_6526954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6526984 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 4, 1, 3]
def baseStart_6526984 : Nat := 118140960795 + 6526984 * 2 ^ 59
def prefixEnd_6526984 : Nat := 4983230072969 + 3 ^ 40 * 6526984 * 2
def baseEnd_6526984 : Nat := 3351480016205596378782953

theorem tailTrace_6526984 : CollatzResearch.WordTrace tailWord_6526984 prefixEnd_6526984 3351480016205596378782953 := by
  unfold tailWord_6526984
  simp only [CollatzResearch.WordTrace]
  refine ⟨119029331892929581482454003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158705775857239441976605337 119029331892929581482454003)
  ·
    refine ⟨178543997839394372223681005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119029331892929581482454003 178543997839394372223681005)
    ·
      refine ⟨66953999189772889583880377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178543997839394372223681005 66953999189772889583880377)
      ·
        refine ⟨50215499392329667187910283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66953999189772889583880377 50215499392329667187910283)
        ·
          refine ⟨75323249088494500781865425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50215499392329667187910283 75323249088494500781865425)
          ·
            refine ⟨56492436816370875586399069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75323249088494500781865425 56492436816370875586399069)
            ·
              refine ⟨21184663806139078344899651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56492436816370875586399069 21184663806139078344899651)
              ·
                refine ⟨31776995709208617517349477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21184663806139078344899651 31776995709208617517349477)
                ·
                  refine ⟨5958186695476615784503027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31776995709208617517349477 5958186695476615784503027)
                  ·
                    refine ⟨8937280043214923676754541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5958186695476615784503027 8937280043214923676754541)
                    ·
                      refine ⟨3351480016205596378782953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8937280043214923676754541 3351480016205596378782953)
                      ·
                        rfl

theorem cell23_6526984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_6526984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6526984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6526984 prefixEnd_6526984 := by exact prefixLift 6526984
  have htrace : WordTrace (prefixWord ++ tailWord_6526984) baseStart_6526984 baseEnd_6526984 := by
    simpa [prefixWord, tailWord_6526984, baseEnd_6526984] using wordTrace_append hprefix tailTrace_6526984
  have hstable : (prefixWord ++ tailWord_6526984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6526984).length < 2 ^ (prefixWord ++ tailWord_6526984).sum := by decide
  have hdescent : baseEnd_6526984 < baseStart_6526984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6526984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527011 : List Nat := [1, 1, 1, 4, 3, 1, 4, 2, 1, 3, 2]
def baseStart_6527011 : Nat := 118140960795 + 6527011 * 2 ^ 59
def prefixEnd_6527011 : Nat := 4983230072969 + 3 ^ 40 * 6527011 * 2
def baseEnd_6527011 : Nat := 3351493880183267773145329

theorem tailTrace_6527011 : CollatzResearch.WordTrace tailWord_6527011 prefixEnd_6527011 3351493880183267773145329 := by
  unfold tailWord_6527011
  simp only [CollatzResearch.WordTrace]
  refine ⟨238059648556761346576140887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158706432371174231050760591 238059648556761346576140887)
  ·
    refine ⟨357089472835142019864211331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238059648556761346576140887 357089472835142019864211331)
    ·
      refine ⟨535634209252713029796316997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357089472835142019864211331 535634209252713029796316997)
      ·
        refine ⟨100431414234883693086809437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 535634209252713029796316997 100431414234883693086809437)
        ·
          refine ⟨37661780338081384907553539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100431414234883693086809437 37661780338081384907553539)
          ·
            refine ⟨56492670507122077361330309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37661780338081384907553539 56492670507122077361330309)
            ·
              refine ⟨10592375720085389505249433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56492670507122077361330309 10592375720085389505249433)
              ·
                refine ⟨7944281790064042128937075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10592375720085389505249433 7944281790064042128937075)
                ·
                  refine ⟨11916422685096063193405613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7944281790064042128937075 11916422685096063193405613)
                  ·
                    refine ⟨4468658506911023697527105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11916422685096063193405613 4468658506911023697527105)
                    ·
                      refine ⟨3351493880183267773145329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4468658506911023697527105 3351493880183267773145329)
                      ·
                        rfl

theorem cell23_6527011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_6527011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527011 prefixEnd_6527011 := by exact prefixLift 6527011
  have htrace : WordTrace (prefixWord ++ tailWord_6527011) baseStart_6527011 baseEnd_6527011 := by
    simpa [prefixWord, tailWord_6527011, baseEnd_6527011] using wordTrace_append hprefix tailTrace_6527011
  have hstable : (prefixWord ++ tailWord_6527011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527011).length < 2 ^ (prefixWord ++ tailWord_6527011).sum := by decide
  have hdescent : baseEnd_6527011 < baseStart_6527011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527057 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 1, 5, 3]
def baseStart_6527057 : Nat := 118140960795 + 6527057 * 2 ^ 59
def prefixEnd_6527057 : Nat := 4983230072969 + 3 ^ 40 * 6527057 * 2
def baseEnd_6527057 : Nat := 3351517500293374593170117

theorem tailTrace_6527057 : CollatzResearch.WordTrace tailWord_6527057 prefixEnd_6527057 3351517500293374593170117 := by
  unfold tailWord_6527057
  simp only [CollatzResearch.WordTrace]
  refine ⟨238061326314594696432315425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158707550876396464288210283 238061326314594696432315425)
  ·
    refine ⟨178545994735946022324236569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238061326314594696432315425 178545994735946022324236569)
    ·
      refine ⟨133909496051959516743177427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178545994735946022324236569 133909496051959516743177427)
      ·
        refine ⟨200864244077939275114766141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133909496051959516743177427 200864244077939275114766141)
        ·
          refine ⟨75324091529227228168037303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200864244077939275114766141 75324091529227228168037303)
          ·
            refine ⟨112986137293840842252055955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75324091529227228168037303 112986137293840842252055955)
            ·
              refine ⟨169479205940761263378083933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112986137293840842252055955 169479205940761263378083933)
              ·
                refine ⟨63554702227785473766781475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169479205940761263378083933 63554702227785473766781475)
                ·
                  refine ⟨95332053341678210650172213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63554702227785473766781475 95332053341678210650172213)
                  ·
                    refine ⟨8937380000782332248453645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95332053341678210650172213 8937380000782332248453645)
                    ·
                      refine ⟨3351517500293374593170117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8937380000782332248453645 3351517500293374593170117)
                      ·
                        rfl

theorem cell23_6527057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_6527057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527057 prefixEnd_6527057 := by exact prefixLift 6527057
  have htrace : WordTrace (prefixWord ++ tailWord_6527057) baseStart_6527057 baseEnd_6527057 := by
    simpa [prefixWord, tailWord_6527057, baseEnd_6527057] using wordTrace_append hprefix tailTrace_6527057
  have hstable : (prefixWord ++ tailWord_6527057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527057).length < 2 ^ (prefixWord ++ tailWord_6527057).sum := by decide
  have hdescent : baseEnd_6527057 < baseStart_6527057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527062 : List Nat := [5, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_6527062 : Nat := 118140960795 + 6527062 * 2 ^ 59
def prefixEnd_6527062 : Nat := 4983230072969 + 3 ^ 40 * 6527062 * 2
def baseEnd_6527062 : Nat := 3351520067696647073607595

theorem tailTrace_6527062 : CollatzResearch.WordTrace tailWord_6527062 prefixEnd_6527062 3351520067696647073607595 := by
  unfold tailWord_6527062
  simp only [CollatzResearch.WordTrace]
  refine ⟨14878844292473536392890465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158707672453051054857498293 14878844292473536392890465)
  ·
    refine ⟨11159133219355152294667849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14878844292473536392890465 11159133219355152294667849)
    ·
      refine ⟨8369349914516364221000887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11159133219355152294667849 8369349914516364221000887)
      ·
        refine ⟨12554024871774546331501331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8369349914516364221000887 12554024871774546331501331)
        ·
          refine ⟨18831037307661819497251997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12554024871774546331501331 18831037307661819497251997)
          ·
            refine ⟨7061638990373182311469499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18831037307661819497251997 7061638990373182311469499)
            ·
              refine ⟨10592458485559773467204249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7061638990373182311469499 10592458485559773467204249)
              ·
                refine ⟨7944343864169830100403187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10592458485559773467204249 7944343864169830100403187)
                ·
                  refine ⟨11916515796254745150604781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7944343864169830100403187 11916515796254745150604781)
                  ·
                    refine ⟨4468693423595529431476793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11916515796254745150604781 4468693423595529431476793)
                    ·
                      refine ⟨3351520067696647073607595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4468693423595529431476793 3351520067696647073607595)
                      ·
                        rfl

theorem cell23_6527062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_6527062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527062 prefixEnd_6527062 := by exact prefixLift 6527062
  have htrace : WordTrace (prefixWord ++ tailWord_6527062) baseStart_6527062 baseEnd_6527062 := by
    simpa [prefixWord, tailWord_6527062, baseEnd_6527062] using wordTrace_append hprefix tailTrace_6527062
  have hstable : (prefixWord ++ tailWord_6527062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527062).length < 2 ^ (prefixWord ++ tailWord_6527062).sum := by decide
  have hdescent : baseEnd_6527062 < baseStart_6527062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527087 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 5]
def baseStart_6527087 : Nat := 118140960795 + 6527087 * 2 ^ 59
def prefixEnd_6527087 : Nat := 4983230072969 + 3 ^ 40 * 6527087 * 2
def baseEnd_6527087 : Nat := 3351532904713009475794979

theorem tailTrace_6527087 : CollatzResearch.WordTrace tailWord_6527087 prefixEnd_6527087 3351532904713009475794979 := by
  unfold tailWord_6527087
  simp only [CollatzResearch.WordTrace]
  refine ⟨238062420504486011555907515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158708280336324007703938343 238062420504486011555907515)
  ·
    refine ⟨357093630756729017333861273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238062420504486011555907515 357093630756729017333861273)
    ·
      refine ⟨267820223067546763000395955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357093630756729017333861273 267820223067546763000395955)
      ·
        refine ⟨401730334601320144500593933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267820223067546763000395955 401730334601320144500593933)
        ·
          refine ⟨150648875475495054187722725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401730334601320144500593933 150648875475495054187722725)
          ·
            refine ⟨28246664151655322660198011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150648875475495054187722725 28246664151655322660198011)
            ·
              refine ⟨42369996227482983990297017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28246664151655322660198011 42369996227482983990297017)
              ·
                refine ⟨31777497170612237992722763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42369996227482983990297017 31777497170612237992722763)
                ·
                  refine ⟨47666245755918356989084145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31777497170612237992722763 47666245755918356989084145)
                  ·
                    refine ⟨35749684316938767741813109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47666245755918356989084145 35749684316938767741813109)
                    ·
                      refine ⟨3351532904713009475794979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35749684316938767741813109 3351532904713009475794979)
                      ·
                        rfl

theorem cell23_6527087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_6527087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527087 prefixEnd_6527087 := by exact prefixLift 6527087
  have htrace : WordTrace (prefixWord ++ tailWord_6527087) baseStart_6527087 baseEnd_6527087 := by
    simpa [prefixWord, tailWord_6527087, baseEnd_6527087] using wordTrace_append hprefix tailTrace_6527087
  have hstable : (prefixWord ++ tailWord_6527087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527087).length < 2 ^ (prefixWord ++ tailWord_6527087).sum := by decide
  have hdescent : baseEnd_6527087 < baseStart_6527087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527128 : List Nat := [2, 1, 2, 4, 4, 1, 1, 1, 2, 5]
def baseStart_6527128 : Nat := 118140960795 + 6527128 * 2 ^ 59
def prefixEnd_6527128 : Nat := 4983230072969 + 3 ^ 40 * 6527128 * 2
def baseEnd_6527128 : Nat := 1117184652473281271794097

theorem tailTrace_6527128 : CollatzResearch.WordTrace tailWord_6527128 prefixEnd_6527128 1117184652473281271794097 := by
  unfold tailWord_6527128
  simp only [CollatzResearch.WordTrace]
  refine ⟨119031957948668737779075019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158709277264891650372100025 119031957948668737779075019)
  ·
    refine ⟨178547936923003106668612529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119031957948668737779075019 178547936923003106668612529)
    ·
      refine ⟨133910952692252330001459397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178547936923003106668612529 133910952692252330001459397)
      ·
        refine ⟨25108303629797311875273637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133910952692252330001459397 25108303629797311875273637)
        ·
          refine ⟨4707806930586995976613807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25108303629797311875273637 4707806930586995976613807)
          ·
            refine ⟨7061710395880493964920711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4707806930586995976613807 7061710395880493964920711)
            ·
              refine ⟨10592565593820740947381067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7061710395880493964920711 10592565593820740947381067)
              ·
                refine ⟨15888848390731111421071601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10592565593820740947381067 15888848390731111421071601)
                ·
                  refine ⟨11916636293048333565803701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15888848390731111421071601 11916636293048333565803701)
                  ·
                    refine ⟨1117184652473281271794097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11916636293048333565803701 1117184652473281271794097)
                    ·
                      rfl

theorem cell23_6527128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 2, 5].length) (baseStart_6527128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527128 prefixEnd_6527128 := by exact prefixLift 6527128
  have htrace : WordTrace (prefixWord ++ tailWord_6527128) baseStart_6527128 baseEnd_6527128 := by
    simpa [prefixWord, tailWord_6527128, baseEnd_6527128] using wordTrace_append hprefix tailTrace_6527128
  have hstable : (prefixWord ++ tailWord_6527128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527128).length < 2 ^ (prefixWord ++ tailWord_6527128).sum := by decide
  have hdescent : baseEnd_6527128 < baseStart_6527128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527191 : List Nat := [1, 1, 3, 2, 1, 2, 1, 5, 2, 3, 2]
def baseStart_6527191 : Nat := 118140960795 + 6527191 * 2 ^ 59
def prefixEnd_6527191 : Nat := 4983230072969 + 3 ^ 40 * 6527191 * 2
def baseEnd_6527191 : Nat := 3351586306701077068894501

theorem tailTrace_6527191 : CollatzResearch.WordTrace tailWord_6527191 prefixEnd_6527191 3351586306701077068894501 := by
  unfold tailWord_6527191
  simp only [CollatzResearch.WordTrace]
  refine ⟨238066213696109237317693427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158710809130739491545128951 238066213696109237317693427)
  ·
    refine ⟨357099320544163855976540141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238066213696109237317693427 357099320544163855976540141)
    ·
      refine ⟨133912245204061445991202553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357099320544163855976540141 133912245204061445991202553)
      ·
        refine ⟨100434183903046084493401915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133912245204061445991202553 100434183903046084493401915)
        ·
          refine ⟨150651275854569126740102873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100434183903046084493401915 150651275854569126740102873)
          ·
            refine ⟨112988456890926845055077155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150651275854569126740102873 112988456890926845055077155)
            ·
              refine ⟨169482685336390267582615733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112988456890926845055077155 169482685336390267582615733)
              ·
                refine ⟨15889001750286587585870225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169482685336390267582615733 15889001750286587585870225)
                ·
                  refine ⟨11916751312714940689402669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15889001750286587585870225 11916751312714940689402669)
                  ·
                    refine ⟨4468781742268102758526001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11916751312714940689402669 4468781742268102758526001)
                    ·
                      refine ⟨3351586306701077068894501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4468781742268102758526001 3351586306701077068894501)
                      ·
                        rfl

theorem cell23_6527191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_6527191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527191 prefixEnd_6527191 := by exact prefixLift 6527191
  have htrace : WordTrace (prefixWord ++ tailWord_6527191) baseStart_6527191 baseEnd_6527191 := by
    simpa [prefixWord, tailWord_6527191, baseEnd_6527191] using wordTrace_append hprefix tailTrace_6527191
  have hstable : (prefixWord ++ tailWord_6527191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527191).length < 2 ^ (prefixWord ++ tailWord_6527191).sum := by decide
  have hdescent : baseEnd_6527191 < baseStart_6527191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527202 : List Nat := [3, 3, 4, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_6527202 : Nat := 118140960795 + 6527202 * 2 ^ 59
def prefixEnd_6527202 : Nat := 4983230072969 + 3 ^ 40 * 6527202 * 2
def baseEnd_6527202 : Nat := 3351591954988276525856951

theorem tailTrace_6527202 : CollatzResearch.WordTrace tailWord_6527202 prefixEnd_6527202 3351591954988276525856951 := by
  unfold tailWord_6527202
  simp only [CollatzResearch.WordTrace]
  refine ⟨59516653724767346549085965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158711076599379590797562573 59516653724767346549085965)
  ·
    refine ⟨22318745146787754955907237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59516653724767346549085965 22318745146787754955907237)
    ·
      refine ⟨4184764715022704054232607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22318745146787754955907237 4184764715022704054232607)
      ·
        refine ⟨6277147072534056081348911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4184764715022704054232607 6277147072534056081348911)
        ·
          refine ⟨9415720608801084122023367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6277147072534056081348911 9415720608801084122023367)
          ·
            refine ⟨14123580913201626183035051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9415720608801084122023367 14123580913201626183035051)
            ·
              refine ⟨21185371369802439274552577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14123580913201626183035051 21185371369802439274552577)
              ·
                refine ⟨15889028527351829455914433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21185371369802439274552577 15889028527351829455914433)
                ·
                  refine ⟨11916771395513872091935825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15889028527351829455914433 11916771395513872091935825)
                  ·
                    refine ⟨8937578546635404068951869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11916771395513872091935825 8937578546635404068951869)
                    ·
                      refine ⟨3351591954988276525856951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8937578546635404068951869 3351591954988276525856951)
                      ·
                        rfl

theorem cell23_6527202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_6527202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527202 prefixEnd_6527202 := by exact prefixLift 6527202
  have htrace : WordTrace (prefixWord ++ tailWord_6527202) baseStart_6527202 baseEnd_6527202 := by
    simpa [prefixWord, tailWord_6527202, baseEnd_6527202] using wordTrace_append hprefix tailTrace_6527202
  have hstable : (prefixWord ++ tailWord_6527202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527202).length < 2 ^ (prefixWord ++ tailWord_6527202).sum := by decide
  have hdescent : baseEnd_6527202 < baseStart_6527202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527204 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_6527204 : Nat := 118140960795 + 6527204 * 2 ^ 59
def prefixEnd_6527204 : Nat := 4983230072969 + 3 ^ 40 * 6527204 * 2
def baseEnd_6527204 : Nat := 3351592981949585518031941

theorem tailTrace_6527204 : CollatzResearch.WordTrace tailWord_6527204 prefixEnd_6527204 3351592981949585518031941 := by
  unfold tailWord_6527204
  simp only [CollatzResearch.WordTrace]
  refine ⟨119033343922531070268958333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158711125230041427025277777 119033343922531070268958333)
  ·
    refine ⟨44637503970949151350859375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119033343922531070268958333 44637503970949151350859375)
    ·
      refine ⟨66956255956423727026289063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44637503970949151350859375 66956255956423727026289063)
      ·
        refine ⟨100434383934635590539433595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66956255956423727026289063 100434383934635590539433595)
        ·
          refine ⟨150651575901953385809150393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100434383934635590539433595 150651575901953385809150393)
          ·
            refine ⟨112988681926465039356862795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150651575901953385809150393 112988681926465039356862795)
            ·
              refine ⟨169483022889697559035294193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112988681926465039356862795 169483022889697559035294193)
              ·
                refine ⟨127112267167273169276470645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169483022889697559035294193 127112267167273169276470645)
                ·
                  refine ⟨11916775046931859619669123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127112267167273169276470645 11916775046931859619669123)
                  ·
                    refine ⟨17875162570397789429503685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11916775046931859619669123 17875162570397789429503685)
                    ·
                      refine ⟨3351592981949585518031941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17875162570397789429503685 3351592981949585518031941)
                      ·
                        rfl

theorem cell23_6527204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_6527204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527204 prefixEnd_6527204 := by exact prefixLift 6527204
  have htrace : WordTrace (prefixWord ++ tailWord_6527204) baseStart_6527204 baseEnd_6527204 := by
    simpa [prefixWord, tailWord_6527204, baseEnd_6527204] using wordTrace_append hprefix tailTrace_6527204
  have hstable : (prefixWord ++ tailWord_6527204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527204).length < 2 ^ (prefixWord ++ tailWord_6527204).sum := by decide
  have hdescent : baseEnd_6527204 < baseStart_6527204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527208 : List Nat := [2, 1, 4, 1, 2, 3, 1, 2, 2, 3, 2]
def baseStart_6527208 : Nat := 118140960795 + 6527208 * 2 ^ 59
def prefixEnd_6527208 : Nat := 4983230072969 + 3 ^ 40 * 6527208 * 2
def baseEnd_6527208 : Nat := 3351595035872203502381923

theorem tailTrace_6527208 : CollatzResearch.WordTrace tailWord_6527208 prefixEnd_6527208 3351595035872203502381923 := by
  unfold tailWord_6527208
  simp only [CollatzResearch.WordTrace]
  refine ⟨119033416868523824610531139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158711222491365099480708185 119033416868523824610531139)
  ·
    refine ⟨178550125302785736915796709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119033416868523824610531139 178550125302785736915796709)
    ·
      refine ⟨33478148494272325671711883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178550125302785736915796709 33478148494272325671711883)
      ·
        refine ⟨50217222741408488507567825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33478148494272325671711883 50217222741408488507567825)
        ·
          refine ⟨37662917056056366380675869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50217222741408488507567825 37662917056056366380675869)
          ·
            refine ⟨14123593896021137392753451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37662917056056366380675869 14123593896021137392753451)
            ·
              refine ⟨21185390844031706089130177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14123593896021137392753451 21185390844031706089130177)
              ·
                refine ⟨15889043133023779566847633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21185390844031706089130177 15889043133023779566847633)
                ·
                  refine ⟨11916782349767834675135725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15889043133023779566847633 11916782349767834675135725)
                  ·
                    refine ⟨4468793381162938003175897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11916782349767834675135725 4468793381162938003175897)
                    ·
                      refine ⟨3351595035872203502381923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4468793381162938003175897 3351595035872203502381923)
                      ·
                        rfl

theorem cell23_6527208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_6527208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527208 prefixEnd_6527208 := by exact prefixLift 6527208
  have htrace : WordTrace (prefixWord ++ tailWord_6527208) baseStart_6527208 baseEnd_6527208 := by
    simpa [prefixWord, tailWord_6527208, baseEnd_6527208] using wordTrace_append hprefix tailTrace_6527208
  have hstable : (prefixWord ++ tailWord_6527208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527208).length < 2 ^ (prefixWord ++ tailWord_6527208).sum := by decide
  have hdescent : baseEnd_6527208 < baseStart_6527208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527231 : List Nat := [1, 1, 2, 2, 1, 4, 3, 3, 2, 4]
def baseStart_6527231 : Nat := 118140960795 + 6527231 * 2 ^ 59
def prefixEnd_6527231 : Nat := 4983230072969 + 3 ^ 40 * 6527231 * 2
def baseEnd_6527231 : Nat := 1117202281975752304131439

theorem tailTrace_6527231 : CollatzResearch.WordTrace tailWord_6527231 prefixEnd_6527231 1117202281975752304131439 := by
  unfold tailWord_6527231
  simp only [CollatzResearch.WordTrace]
  refine ⟨238067672615964324149149547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158711781743976216099433031 238067672615964324149149547)
  ·
    refine ⟨357101508923946486223724321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238067672615964324149149547 357101508923946486223724321)
    ·
      refine ⟨267826131692959864667793241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357101508923946486223724321 267826131692959864667793241)
      ·
        refine ⟨200869598769719898500844931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267826131692959864667793241 200869598769719898500844931)
        ·
          refine ⟨301304398154579847751267397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200869598769719898500844931 301304398154579847751267397)
          ·
            refine ⟨56494574653983721453362637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 301304398154579847751267397 56494574653983721453362637)
            ·
              refine ⟨21185465495243895545010989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56494574653983721453362637 21185465495243895545010989)
              ·
                refine ⟨7944549560716460829379121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21185465495243895545010989 7944549560716460829379121)
                ·
                  refine ⟨5958412170537345622034341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7944549560716460829379121 5958412170537345622034341)
                  ·
                    refine ⟨1117202281975752304131439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5958412170537345622034341 1117202281975752304131439)
                    ·
                      rfl

theorem cell23_6527231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 4].length) (baseStart_6527231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527231 prefixEnd_6527231 := by exact prefixLift 6527231
  have htrace : WordTrace (prefixWord ++ tailWord_6527231) baseStart_6527231 baseEnd_6527231 := by
    simpa [prefixWord, tailWord_6527231, baseEnd_6527231] using wordTrace_append hprefix tailTrace_6527231
  have hstable : (prefixWord ++ tailWord_6527231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527231).length < 2 ^ (prefixWord ++ tailWord_6527231).sum := by decide
  have hdescent : baseEnd_6527231 < baseStart_6527231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527241 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 3, 2, 3]
def baseStart_6527241 : Nat := 118140960795 + 6527241 * 2 ^ 59
def prefixEnd_6527241 : Nat := 4983230072969 + 3 ^ 40 * 6527241 * 2
def baseEnd_6527241 : Nat := 3351611980733801873269271

theorem tailTrace_6527241 : CollatzResearch.WordTrace tailWord_6527241 prefixEnd_6527241 3351611980733801873269271 := by
  unfold tailWord_6527241
  simp only [CollatzResearch.WordTrace]
  refine ⟨238068037345928095857013577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158712024897285397238009051 238068037345928095857013577)
  ·
    refine ⟨178551028009446071892760183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238068037345928095857013577 178551028009446071892760183)
    ·
      refine ⟨267826542014169107839140275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178551028009446071892760183 267826542014169107839140275)
      ·
        refine ⟨401739813021253661758710413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267826542014169107839140275 401739813021253661758710413)
        ·
          refine ⟨150652429882970123159516405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401739813021253661758710413 150652429882970123159516405)
          ·
            refine ⟨14123665301528449046204663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150652429882970123159516405 14123665301528449046204663)
            ·
              refine ⟨21185497952292673569306995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14123665301528449046204663 21185497952292673569306995)
              ·
                refine ⟨31778246928439010353960493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21185497952292673569306995 31778246928439010353960493)
                ·
                  refine ⟨11916842598164628882735185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31778246928439010353960493 11916842598164628882735185)
                  ·
                    refine ⟨8937631948623471662051389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11916842598164628882735185 8937631948623471662051389)
                    ·
                      refine ⟨3351611980733801873269271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8937631948623471662051389 3351611980733801873269271)
                      ·
                        rfl

theorem cell23_6527241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 2, 3].length) (baseStart_6527241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527241 prefixEnd_6527241 := by exact prefixLift 6527241
  have htrace : WordTrace (prefixWord ++ tailWord_6527241) baseStart_6527241 baseEnd_6527241 := by
    simpa [prefixWord, tailWord_6527241, baseEnd_6527241] using wordTrace_append hprefix tailTrace_6527241
  have hstable : (prefixWord ++ tailWord_6527241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527241).length < 2 ^ (prefixWord ++ tailWord_6527241).sum := by decide
  have hdescent : baseEnd_6527241 < baseStart_6527241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527258 : List Nat := [3, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5]
def baseStart_6527258 : Nat := 118140960795 + 6527258 * 2 ^ 59
def prefixEnd_6527258 : Nat := 4983230072969 + 3 ^ 40 * 6527258 * 2
def baseEnd_6527258 : Nat := 3351620709904928306756693

theorem tailTrace_6527258 : CollatzResearch.WordTrace tailWord_6527258 prefixEnd_6527258 3351620709904928306756693 := by
  unfold tailWord_6527258
  simp only [CollatzResearch.WordTrace]
  refine ⟨59517164346716626940095607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158712438257911005173588285 59517164346716626940095607)
  ·
    refine ⟨89275746520074940410143411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59517164346716626940095607 89275746520074940410143411)
    ·
      refine ⟨133913619780112410615215117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89275746520074940410143411 133913619780112410615215117)
      ·
        refine ⟨50217607417542153980705669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133913619780112410615215117 50217607417542153980705669)
        ·
          refine ⟨9415801390789153871382313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50217607417542153980705669 9415801390789153871382313)
          ·
            refine ⟨7061851043091865403536735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9415801390789153871382313 7061851043091865403536735)
            ·
              refine ⟨10592776564637798105305103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7061851043091865403536735 10592776564637798105305103)
              ·
                refine ⟨15889164846956697157957655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10592776564637798105305103 15889164846956697157957655)
                ·
                  refine ⟨23833747270435045736936483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15889164846956697157957655 23833747270435045736936483)
                  ·
                    refine ⟨35750620905652568605404725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23833747270435045736936483 35750620905652568605404725)
                    ·
                      refine ⟨3351620709904928306756693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35750620905652568605404725 3351620709904928306756693)
                      ·
                        rfl

theorem cell23_6527258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_6527258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527258 prefixEnd_6527258 := by exact prefixLift 6527258
  have htrace : WordTrace (prefixWord ++ tailWord_6527258) baseStart_6527258 baseEnd_6527258 := by
    simpa [prefixWord, tailWord_6527258, baseEnd_6527258] using wordTrace_append hprefix tailTrace_6527258
  have hstable : (prefixWord ++ tailWord_6527258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527258).length < 2 ^ (prefixWord ++ tailWord_6527258).sum := by decide
  have hdescent : baseEnd_6527258 < baseStart_6527258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527261 : List Nat := [1, 4, 2, 3, 3, 10]
def baseStart_6527261 : Nat := 118140960795 + 6527261 * 2 ^ 59
def prefixEnd_6527261 : Nat := 4983230072969 + 3 ^ 40 * 6527261 * 2
def baseEnd_6527261 : Nat := 13792684157806139074153

theorem tailTrace_6527261 : CollatzResearch.WordTrace tailWord_6527261 prefixEnd_6527261 13792684157806139074153 := by
  unfold tailWord_6527261
  simp only [CollatzResearch.WordTrace]
  refine ⟨238068766805855639272741637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158712511203903759515161091 238068766805855639272741637)
  ·
    refine ⟨44637893776097932363639057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238068766805855639272741637 44637893776097932363639057)
    ·
      refine ⟨33478420332073449272729293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44637893776097932363639057 33478420332073449272729293)
      ·
        refine ⟨12554407624527543477273485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33478420332073449272729293 12554407624527543477273485)
        ·
          refine ⟨4707902859197828803977557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12554407624527543477273485 4707902859197828803977557)
          ·
            refine ⟨13792684157806139074153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4707902859197828803977557 13792684157806139074153)
            ·
              rfl

theorem cell23_6527261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 10].length) (baseStart_6527261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527261 prefixEnd_6527261 := by exact prefixLift 6527261
  have htrace : WordTrace (prefixWord ++ tailWord_6527261) baseStart_6527261 baseEnd_6527261 := by
    simpa [prefixWord, tailWord_6527261, baseEnd_6527261] using wordTrace_append hprefix tailTrace_6527261
  have hstable : (prefixWord ++ tailWord_6527261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527261).length < 2 ^ (prefixWord ++ tailWord_6527261).sum := by decide
  have hdescent : baseEnd_6527261 < baseStart_6527261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527288 : List Nat := [2, 1, 2, 1, 3, 1, 4, 3, 2, 1, 3]
def baseStart_6527288 : Nat := 118140960795 + 6527288 * 2 ^ 59
def prefixEnd_6527288 : Nat := 4983230072969 + 3 ^ 40 * 6527288 * 2
def baseEnd_6527288 : Nat := 3351636114324563189381555

theorem tailTrace_6527288 : CollatzResearch.WordTrace tailWord_6527288 prefixEnd_6527288 3351636114324563189381555 := by
  unfold tailWord_6527288
  simp only [CollatzResearch.WordTrace]
  refine ⟨119034875788378911441987259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158713167717838548589316345 119034875788378911441987259)
  ·
    refine ⟨178552313682568367162980889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119034875788378911441987259 178552313682568367162980889)
    ·
      refine ⟨133914235261926275372235667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178552313682568367162980889 133914235261926275372235667)
      ·
        refine ⟨200871352892889413058353501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133914235261926275372235667 200871352892889413058353501)
        ·
          refine ⟨75326757334833529896882563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200871352892889413058353501 75326757334833529896882563)
          ·
            refine ⟨112990136002250294845323845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75326757334833529896882563 112990136002250294845323845)
            ·
              refine ⟨21185650500421930283498221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112990136002250294845323845 21185650500421930283498221)
              ·
                refine ⟨7944618937658223856311833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21185650500421930283498221 7944618937658223856311833)
                ·
                  refine ⟨5958464203243667892233875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7944618937658223856311833 5958464203243667892233875)
                  ·
                    refine ⟨8937696304865501838350813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5958464203243667892233875 8937696304865501838350813)
                    ·
                      refine ⟨3351636114324563189381555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8937696304865501838350813 3351636114324563189381555)
                      ·
                        rfl

theorem cell23_6527288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 2, 1, 3].length) (baseStart_6527288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527288 prefixEnd_6527288 := by exact prefixLift 6527288
  have htrace : WordTrace (prefixWord ++ tailWord_6527288) baseStart_6527288 baseEnd_6527288 := by
    simpa [prefixWord, tailWord_6527288, baseEnd_6527288] using wordTrace_append hprefix tailTrace_6527288
  have hstable : (prefixWord ++ tailWord_6527288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527288).length < 2 ^ (prefixWord ++ tailWord_6527288).sum := by decide
  have hdescent : baseEnd_6527288 < baseStart_6527288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527311 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 3, 4, 2]
def baseStart_6527311 : Nat := 118140960795 + 6527311 * 2 ^ 59
def prefixEnd_6527311 : Nat := 4983230072969 + 3 ^ 40 * 6527311 * 2
def baseEnd_6527311 : Nat := 3351647924379616599393949

theorem tailTrace_6527311 : CollatzResearch.WordTrace tailWord_6527311 prefixEnd_6527311 3351647924379616599393949 := by
  unfold tailWord_6527311
  simp only [CollatzResearch.WordTrace]
  refine ⟨238070590455674497812061787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158713726970449665208041191 238070590455674497812061787)
  ·
    refine ⟨357105885683511746718092681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238070590455674497812061787 357105885683511746718092681)
    ·
      refine ⟨267829414262633810038569511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357105885683511746718092681 267829414262633810038569511)
      ·
        refine ⟨401744121393950715057854267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267829414262633810038569511 401744121393950715057854267)
        ·
          refine ⟨602616182090926072586781401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401744121393950715057854267 602616182090926072586781401)
          ·
            refine ⟨451962136568194554440086051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602616182090926072586781401 451962136568194554440086051)
            ·
              refine ⟨677943204852291831660129077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451962136568194554440086051 677943204852291831660129077)
              ·
                refine ⟨63557175454902359218137101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 677943204852291831660129077 63557175454902359218137101)
                ·
                  refine ⟨23833940795588384706801413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63557175454902359218137101 23833940795588384706801413)
                  ·
                    refine ⟨4468863899172822132525265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23833940795588384706801413 4468863899172822132525265)
                    ·
                      refine ⟨3351647924379616599393949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4468863899172822132525265 3351647924379616599393949)
                      ·
                        rfl

theorem cell23_6527311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 4, 2].length) (baseStart_6527311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527311 prefixEnd_6527311 := by exact prefixLift 6527311
  have htrace : WordTrace (prefixWord ++ tailWord_6527311) baseStart_6527311 baseEnd_6527311 := by
    simpa [prefixWord, tailWord_6527311, baseEnd_6527311] using wordTrace_append hprefix tailTrace_6527311
  have hstable : (prefixWord ++ tailWord_6527311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527311).length < 2 ^ (prefixWord ++ tailWord_6527311).sum := by decide
  have hdescent : baseEnd_6527311 < baseStart_6527311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527341 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_6527341 : Nat := 118140960795 + 6527341 * 2 ^ 59
def prefixEnd_6527341 : Nat := 4983230072969 + 3 ^ 40 * 6527341 * 2
def baseEnd_6527341 : Nat := 3351663328799251482018811

theorem tailTrace_6527341 : CollatzResearch.WordTrace tailWord_6527341 prefixEnd_6527341 3351663328799251482018811 := by
  unfold tailWord_6527341
  simp only [CollatzResearch.WordTrace]
  refine ⟨238071684645565812935653877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158714456430377208623769251 238071684645565812935653877)
  ·
    refine ⟨22319220435521794962717551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 238071684645565812935653877 22319220435521794962717551)
    ·
      refine ⟨33478830653282692444076327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22319220435521794962717551 33478830653282692444076327)
      ·
        refine ⟨50218245979924038666114491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33478830653282692444076327 50218245979924038666114491)
        ·
          refine ⟨75327368969886057999171737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50218245979924038666114491 75327368969886057999171737)
          ·
            refine ⟨56495526727414543499378803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75327368969886057999171737 56495526727414543499378803)
            ·
              refine ⟨84743290091121815249068205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56495526727414543499378803 84743290091121815249068205)
              ·
                refine ⟨31778733784170680718400577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84743290091121815249068205 31778733784170680718400577)
                ·
                  refine ⟨23834050338128010538800433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31778733784170680718400577 23834050338128010538800433)
                  ·
                    refine ⟨17875537753596007904100325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23834050338128010538800433 17875537753596007904100325)
                    ·
                      refine ⟨3351663328799251482018811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17875537753596007904100325 3351663328799251482018811)
                      ·
                        rfl

theorem cell23_6527341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_6527341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527341 prefixEnd_6527341 := by exact prefixLift 6527341
  have htrace : WordTrace (prefixWord ++ tailWord_6527341) baseStart_6527341 baseEnd_6527341 := by
    simpa [prefixWord, tailWord_6527341, baseEnd_6527341] using wordTrace_append hprefix tailTrace_6527341
  have hstable : (prefixWord ++ tailWord_6527341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527341).length < 2 ^ (prefixWord ++ tailWord_6527341).sum := by decide
  have hdescent : baseEnd_6527341 < baseStart_6527341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527391 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 5]
def baseStart_6527391 : Nat := 118140960795 + 6527391 * 2 ^ 59
def prefixEnd_6527391 : Nat := 4983230072969 + 3 ^ 40 * 6527391 * 2
def baseEnd_6527391 : Nat := 3351689002831976286393581

theorem tailTrace_6527391 : CollatzResearch.WordTrace tailWord_6527391 prefixEnd_6527391 3351689002831976286393581 := by
  unfold tailWord_6527391
  simp only [CollatzResearch.WordTrace]
  refine ⟨238073508295384671474974027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158715672196923114316649351 238073508295384671474974027)
  ·
    refine ⟨357110262443077007212461041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238073508295384671474974027 357110262443077007212461041)
    ·
      refine ⟨267832696832307755409345781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357110262443077007212461041 267832696832307755409345781)
      ·
        refine ⟨25109315328028852069626167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 267832696832307755409345781 25109315328028852069626167)
        ·
          refine ⟨37663972992043278104439251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25109315328028852069626167 37663972992043278104439251)
          ·
            refine ⟨56495959488064917156658877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37663972992043278104439251 56495959488064917156658877)
            ·
              refine ⟨21185984808024343933747079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56495959488064917156658877 21185984808024343933747079)
              ·
                refine ⟨31778977212036515900620619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21185984808024343933747079 31778977212036515900620619)
                ·
                  refine ⟨47668465818054773850930929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31778977212036515900620619 47668465818054773850930929)
                  ·
                    refine ⟨35751349363541080388198197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47668465818054773850930929 35751349363541080388198197)
                    ·
                      refine ⟨3351689002831976286393581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35751349363541080388198197 3351689002831976286393581)
                      ·
                        rfl

theorem cell23_6527391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_6527391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527391 prefixEnd_6527391 := by exact prefixLift 6527391
  have htrace : WordTrace (prefixWord ++ tailWord_6527391) baseStart_6527391 baseEnd_6527391 := by
    simpa [prefixWord, tailWord_6527391, baseEnd_6527391] using wordTrace_append hprefix tailTrace_6527391
  have hstable : (prefixWord ++ tailWord_6527391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527391).length < 2 ^ (prefixWord ++ tailWord_6527391).sum := by decide
  have hdescent : baseEnd_6527391 < baseStart_6527391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527502 : List Nat := [4, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3]
def baseStart_6527502 : Nat := 118140960795 + 6527502 * 2 ^ 59
def prefixEnd_6527502 : Nat := 4983230072969 + 3 ^ 40 * 6527502 * 2
def baseEnd_6527502 : Nat := 3351745999184625352105571

theorem tailTrace_6527502 : CollatzResearch.WordTrace tailWord_6527502 prefixEnd_6527502 3351745999184625352105571 := by
  unfold tailWord_6527502
  simp only [CollatzResearch.WordTrace]
  refine ⟨29759694599747817179033095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158718371198655024954843173 29759694599747817179033095)
  ·
    refine ⟨44639541899621725768549643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29759694599747817179033095 44639541899621725768549643)
    ·
      refine ⟨66959312849432588652824465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44639541899621725768549643 66959312849432588652824465)
      ·
        refine ⟨50219484637074441489618349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66959312849432588652824465 50219484637074441489618349)
        ·
          refine ⟨18832306738902915558606881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50219484637074441489618349 18832306738902915558606881)
          ·
            refine ⟨14124230054177186668955161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18832306738902915558606881 14124230054177186668955161)
            ·
              refine ⟨10593172540632890001716371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14124230054177186668955161 10593172540632890001716371)
              ·
                refine ⟨15889758810949335002574557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10593172540632890001716371 15889758810949335002574557)
                ·
                  refine ⟨5958659554106000625965459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15889758810949335002574557 5958659554106000625965459)
                  ·
                    refine ⟨8937989331159000938948189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5958659554106000625965459 8937989331159000938948189)
                    ·
                      refine ⟨3351745999184625352105571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8937989331159000938948189 3351745999184625352105571)
                      ·
                        rfl

theorem cell23_6527502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_6527502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527502 prefixEnd_6527502 := by exact prefixLift 6527502
  have htrace : WordTrace (prefixWord ++ tailWord_6527502) baseStart_6527502 baseEnd_6527502 := by
    simpa [prefixWord, tailWord_6527502, baseEnd_6527502] using wordTrace_append hprefix tailTrace_6527502
  have hstable : (prefixWord ++ tailWord_6527502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527502).length < 2 ^ (prefixWord ++ tailWord_6527502).sum := by decide
  have hdescent : baseEnd_6527502 < baseStart_6527502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527538 : List Nat := [3, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_6527538 : Nat := 118140960795 + 6527538 * 2 ^ 59
def prefixEnd_6527538 : Nat := 4983230072969 + 3 ^ 40 * 6527538 * 2
def baseEnd_6527538 : Nat := 3351764484488187211255405

theorem tailTrace_6527538 : CollatzResearch.WordTrace tailWord_6527538 prefixEnd_6527538 3351764484488187211255405 := by
  unfold tailWord_6527538
  simp only [CollatzResearch.WordTrace]
  refine ⟨59519717456463028895143817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158719246550568077053716845 59519717456463028895143817)
  ·
    refine ⟨44639788092347271671357863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59519717456463028895143817 44639788092347271671357863)
    ·
      refine ⟨66959682138520907507036795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44639788092347271671357863 66959682138520907507036795)
      ·
        refine ⟨100439523207781361260555193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66959682138520907507036795 100439523207781361260555193)
        ·
          refine ⟨75329642405836020945416395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100439523207781361260555193 75329642405836020945416395)
          ·
            refine ⟨112994463608754031418124593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75329642405836020945416395 112994463608754031418124593)
            ·
              refine ⟨84745847706565523563593445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112994463608754031418124593 84745847706565523563593445)
              ·
                refine ⟨15889846444981035668173771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84745847706565523563593445 15889846444981035668173771)
                ·
                  refine ⟨23834769667471553502260657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15889846444981035668173771 23834769667471553502260657)
                  ·
                    refine ⟨17876077250603665126695493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23834769667471553502260657 17876077250603665126695493)
                    ·
                      refine ⟨3351764484488187211255405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17876077250603665126695493 3351764484488187211255405)
                      ·
                        rfl

theorem cell23_6527538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_6527538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527538 prefixEnd_6527538 := by exact prefixLift 6527538
  have htrace : WordTrace (prefixWord ++ tailWord_6527538) baseStart_6527538 baseEnd_6527538 := by
    simpa [prefixWord, tailWord_6527538, baseEnd_6527538] using wordTrace_append hprefix tailTrace_6527538
  have hstable : (prefixWord ++ tailWord_6527538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527538).length < 2 ^ (prefixWord ++ tailWord_6527538).sum := by decide
  have hdescent : baseEnd_6527538 < baseStart_6527538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527542 : List Nat := [5, 1, 2, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_6527542 : Nat := 118140960795 + 6527542 * 2 ^ 59
def prefixEnd_6527542 : Nat := 4983230072969 + 3 ^ 40 * 6527542 * 2
def baseEnd_6527542 : Nat := 3351766538410805195605387

theorem tailTrace_6527542 : CollatzResearch.WordTrace tailWord_6527542 prefixEnd_6527542 3351766538410805195605387 := by
  unfold tailWord_6527542
  simp only [CollatzResearch.WordTrace]
  refine ⟨14879938482364851516482555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158719343811891749509147253 14879938482364851516482555)
  ·
    refine ⟨22319907723547277274723833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14879938482364851516482555 22319907723547277274723833)
    ·
      refine ⟨16739930792660457956042875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22319907723547277274723833 16739930792660457956042875)
      ·
        refine ⟨25109896188990686934064313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16739930792660457956042875 25109896188990686934064313)
        ·
          refine ⟨18832422141743015200548235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25109896188990686934064313 18832422141743015200548235)
          ·
            refine ⟨28248633212614522800822353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18832422141743015200548235 28248633212614522800822353)
            ·
              refine ⟨21186474909460892100616765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28248633212614522800822353 21186474909460892100616765)
              ·
                refine ⟨7944928091047834537731287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21186474909460892100616765 7944928091047834537731287)
                ·
                  refine ⟨11917392136571751806596931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7944928091047834537731287 11917392136571751806596931)
                  ·
                    refine ⟨17876088204857627709895397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11917392136571751806596931 17876088204857627709895397)
                    ·
                      refine ⟨3351766538410805195605387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17876088204857627709895397 3351766538410805195605387)
                      ·
                        rfl

theorem cell23_6527542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_6527542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527542 prefixEnd_6527542 := by exact prefixLift 6527542
  have htrace : WordTrace (prefixWord ++ tailWord_6527542) baseStart_6527542 baseEnd_6527542 := by
    simpa [prefixWord, tailWord_6527542, baseEnd_6527542] using wordTrace_append hprefix tailTrace_6527542
  have hstable : (prefixWord ++ tailWord_6527542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527542).length < 2 ^ (prefixWord ++ tailWord_6527542).sum := by decide
  have hdescent : baseEnd_6527542 < baseStart_6527542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527545 : List Nat := [1, 2, 1, 5, 1, 1, 1, 5, 1, 2, 3]
def baseStart_6527545 : Nat := 118140960795 + 6527545 * 2 ^ 59
def prefixEnd_6527545 : Nat := 4983230072969 + 3 ^ 40 * 6527545 * 2
def baseEnd_6527545 : Nat := 3351768078852768683867873

theorem tailTrace_6527545 : CollatzResearch.WordTrace tailWord_6527545 prefixEnd_6527545 3351768078852768683867873 := by
  unfold tailWord_6527545
  simp only [CollatzResearch.WordTrace]
  refine ⟨238079125136826755776080089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158719416757884503850720059 238079125136826755776080089)
  ·
    refine ⟨178559343852620066832060067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238079125136826755776080089 178559343852620066832060067)
    ·
      refine ⟨267839015778930100248090101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178559343852620066832060067 267839015778930100248090101)
      ·
        refine ⟨25109907729274696898258447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 267839015778930100248090101 25109907729274696898258447)
        ·
          refine ⟨37664861593912045347387671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25109907729274696898258447 37664861593912045347387671)
          ·
            refine ⟨56497292390868068021081507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37664861593912045347387671 56497292390868068021081507)
            ·
              refine ⟨84745938586302102031622261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56497292390868068021081507 84745938586302102031622261)
              ·
                refine ⟨7944931742465822065464587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84745938586302102031622261 7944931742465822065464587)
                ·
                  refine ⟨11917397613698733098196881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7944931742465822065464587 11917397613698733098196881)
                  ·
                    refine ⟨8938048210274049823647661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11917397613698733098196881 8938048210274049823647661)
                    ·
                      refine ⟨3351768078852768683867873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8938048210274049823647661 3351768078852768683867873)
                      ·
                        rfl

theorem cell23_6527545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_6527545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527545 prefixEnd_6527545 := by exact prefixLift 6527545
  have htrace : WordTrace (prefixWord ++ tailWord_6527545) baseStart_6527545 baseEnd_6527545 := by
    simpa [prefixWord, tailWord_6527545, baseEnd_6527545] using wordTrace_append hprefix tailTrace_6527545
  have hstable : (prefixWord ++ tailWord_6527545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527545).length < 2 ^ (prefixWord ++ tailWord_6527545).sum := by decide
  have hdescent : baseEnd_6527545 < baseStart_6527545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527548 : List Nat := [2, 2, 2, 2, 3, 3, 9]
def baseStart_6527548 : Nat := 118140960795 + 6527548 * 2 ^ 59
def prefixEnd_6527548 : Nat := 4983230072969 + 3 ^ 40 * 6527548 * 2
def baseEnd_6527548 : Nat := 41379871843144841631239

theorem tailTrace_6527548 : CollatzResearch.WordTrace tailWord_6527548 prefixEnd_6527548 41379871843144841631239 := by
  unfold tailWord_6527548
  simp only [CollatzResearch.WordTrace]
  refine ⟨119039617277907943644219649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158719489703877258192292865 119039617277907943644219649)
  ·
    refine ⟨89279712958430957733164737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119039617277907943644219649 89279712958430957733164737)
    ·
      refine ⟨66959784718823218299873553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89279712958430957733164737 66959784718823218299873553)
      ·
        refine ⟨50219838539117413724905165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66959784718823218299873553 50219838539117413724905165)
        ·
          refine ⟨18832439452169030146839437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50219838539117413724905165 18832439452169030146839437)
          ·
            refine ⟨7062164794563386305064789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18832439452169030146839437 7062164794563386305064789)
            ·
              refine ⟨41379871843144841631239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7062164794563386305064789 41379871843144841631239)
              ·
                rfl

theorem cell23_6527548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 9].length) (baseStart_6527548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527548 prefixEnd_6527548 := by exact prefixLift 6527548
  have htrace : WordTrace (prefixWord ++ tailWord_6527548) baseStart_6527548 baseEnd_6527548 := by
    simpa [prefixWord, tailWord_6527548, baseEnd_6527548] using wordTrace_append hprefix tailTrace_6527548
  have hstable : (prefixWord ++ tailWord_6527548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527548).length < 2 ^ (prefixWord ++ tailWord_6527548).sum := by decide
  have hdescent : baseEnd_6527548 < baseStart_6527548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527559 : List Nat := [1, 1, 4, 1, 4, 3, 1, 1, 3, 2, 2]
def baseStart_6527559 : Nat := 118140960795 + 6527559 * 2 ^ 59
def prefixEnd_6527559 : Nat := 4983230072969 + 3 ^ 40 * 6527559 * 2
def baseEnd_6527559 : Nat := 3351775267581931629092809

theorem tailTrace_6527559 : CollatzResearch.WordTrace tailWord_6527559 prefixEnd_6527559 3351775267581931629092809 := by
  unfold tailWord_6527559
  simp only [CollatzResearch.WordTrace]
  refine ⟨238079635758776036167089731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158719757172517357444726487 238079635758776036167089731)
  ·
    refine ⟨357119453638164054250634597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238079635758776036167089731 357119453638164054250634597)
    ·
      refine ⟨66959897557155760171993987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 357119453638164054250634597 66959897557155760171993987)
      ·
        refine ⟨100439846335733640257990981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66959897557155760171993987 100439846335733640257990981)
        ·
          refine ⟨18832471187950057548373309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100439846335733640257990981 18832471187950057548373309)
          ·
            refine ⟨7062176695481271580639991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18832471187950057548373309 7062176695481271580639991)
            ·
              refine ⟨10593265043221907370959987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7062176695481271580639991 10593265043221907370959987)
              ·
                refine ⟨15889897564832861056439981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10593265043221907370959987 15889897564832861056439981)
                ·
                  refine ⟨5958711586812322896164993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15889897564832861056439981 5958711586812322896164993)
                  ·
                    refine ⟨4469033690109242172123745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5958711586812322896164993 4469033690109242172123745)
                    ·
                      refine ⟨3351775267581931629092809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4469033690109242172123745 3351775267581931629092809)
                      ·
                        rfl

theorem cell23_6527559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_6527559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527559 prefixEnd_6527559 := by exact prefixLift 6527559
  have htrace : WordTrace (prefixWord ++ tailWord_6527559) baseStart_6527559 baseEnd_6527559 := by
    simpa [prefixWord, tailWord_6527559, baseEnd_6527559] using wordTrace_append hprefix tailTrace_6527559
  have hstable : (prefixWord ++ tailWord_6527559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527559).length < 2 ^ (prefixWord ++ tailWord_6527559).sum := by decide
  have hdescent : baseEnd_6527559 < baseStart_6527559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527565 : List Nat := [1, 6, 1, 1, 2, 2, 2, 8]
def baseStart_6527565 : Nat := 118140960795 + 6527565 * 2 ^ 59
def prefixEnd_6527565 : Nat := 4983230072969 + 3 ^ 40 * 6527565 * 2
def baseEnd_6527565 : Nat := 124139938832068837245103

theorem tailTrace_6527565 : CollatzResearch.WordTrace tailWord_6527565 prefixEnd_6527565 124139938832068837245103 := by
  unfold tailWord_6527565
  simp only [CollatzResearch.WordTrace]
  refine ⟨238079854596754299191808149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158719903064502866127872099 238079854596754299191808149)
  ·
    refine ⟨11159993184222857774616007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 238079854596754299191808149 11159993184222857774616007)
    ·
      refine ⟨16739989776334286661924011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11159993184222857774616007 16739989776334286661924011)
      ·
        refine ⟨25109984664501429992886017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16739989776334286661924011 25109984664501429992886017)
        ·
          refine ⟨18832488498376072494664513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25109984664501429992886017 18832488498376072494664513)
          ·
            refine ⟨14124366373782054370998385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18832488498376072494664513 14124366373782054370998385)
            ·
              refine ⟨10593274780336540778248789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14124366373782054370998385 10593274780336540778248789)
              ·
                refine ⟨124139938832068837245103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10593274780336540778248789 124139938832068837245103)
                ·
                  rfl

theorem cell23_6527565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 8].length) (baseStart_6527565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527565 prefixEnd_6527565 := by exact prefixLift 6527565
  have htrace : WordTrace (prefixWord ++ tailWord_6527565) baseStart_6527565 baseEnd_6527565 := by
    simpa [prefixWord, tailWord_6527565, baseEnd_6527565] using wordTrace_append hprefix tailTrace_6527565
  have hstable : (prefixWord ++ tailWord_6527565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527565).length < 2 ^ (prefixWord ++ tailWord_6527565).sum := by decide
  have hdescent : baseEnd_6527565 < baseStart_6527565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527592 : List Nat := [2, 1, 4, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_6527592 : Nat := 118140960795 + 6527592 * 2 ^ 59
def prefixEnd_6527592 : Nat := 4983230072969 + 3 ^ 40 * 6527592 * 2
def baseEnd_6527592 : Nat := 3351792212443529999980157

theorem tailTrace_6527592 : CollatzResearch.WordTrace tailWord_6527592 prefixEnd_6527592 3351792212443529999980157 := by
  unfold tailWord_6527592
  simp only [CollatzResearch.WordTrace]
  refine ⟨119040419683828241401520515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158720559578437655202027353 119040419683828241401520515)
  ·
    refine ⟨178560629525742362102280773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119040419683828241401520515 178560629525742362102280773)
    ·
      refine ⟨33480118036076692894177645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178560629525742362102280773 33480118036076692894177645)
      ·
        refine ⟨12555044263528759835316617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33480118036076692894177645 12555044263528759835316617)
        ·
          refine ⟨9416283197646569876487463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12555044263528759835316617 9416283197646569876487463)
          ·
            refine ⟨14124424796469854814731195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9416283197646569876487463 14124424796469854814731195)
            ·
              refine ⟨21186637194704782222096793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14124424796469854814731195 21186637194704782222096793)
              ·
                refine ⟨15889977896028586666572595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21186637194704782222096793 15889977896028586666572595)
                ·
                  refine ⟨23834966844042879999858893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15889977896028586666572595 23834966844042879999858893)
                  ·
                    refine ⟨8938112566516079999947085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23834966844042879999858893 8938112566516079999947085)
                    ·
                      refine ⟨3351792212443529999980157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8938112566516079999947085 3351792212443529999980157)
                      ·
                        rfl

theorem cell23_6527592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_6527592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527592 prefixEnd_6527592 := by exact prefixLift 6527592
  have htrace : WordTrace (prefixWord ++ tailWord_6527592) baseStart_6527592 baseEnd_6527592 := by
    simpa [prefixWord, tailWord_6527592, baseEnd_6527592] using wordTrace_append hprefix tailTrace_6527592
  have hstable : (prefixWord ++ tailWord_6527592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527592).length < 2 ^ (prefixWord ++ tailWord_6527592).sum := by decide
  have hdescent : baseEnd_6527592 < baseStart_6527592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527662 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_6527662 : Nat := 118140960795 + 6527662 * 2 ^ 59
def prefixEnd_6527662 : Nat := 4983230072969 + 3 ^ 40 * 6527662 * 2
def baseEnd_6527662 : Nat := 3351828156089344726104835

theorem tailTrace_6527662 : CollatzResearch.WordTrace tailWord_6527662 prefixEnd_6527662 3351828156089344726104835 := by
  unfold tailWord_6527662
  simp only [CollatzResearch.WordTrace]
  refine ⟨29760424059675360594761155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158722261651601923172059493 29760424059675360594761155)
  ·
    refine ⟨44640636089513040892141733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29760424059675360594761155 44640636089513040892141733)
    ·
      refine ⟨8370119266783695167276575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44640636089513040892141733 8370119266783695167276575)
      ·
        refine ⟨12555178900175542750914863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8370119266783695167276575 12555178900175542750914863)
        ·
          refine ⟨18832768350263314126372295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12555178900175542750914863 18832768350263314126372295)
          ·
            refine ⟨28249152525394971189558443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18832768350263314126372295 28249152525394971189558443)
            ·
              refine ⟨42373728788092456784337665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28249152525394971189558443 42373728788092456784337665)
              ·
                refine ⟨31780296591069342588253249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42373728788092456784337665 31780296591069342588253249)
                ·
                  refine ⟨23835222443302006941189937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31780296591069342588253249 23835222443302006941189937)
                  ·
                    refine ⟨17876416832476505205892453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23835222443302006941189937 17876416832476505205892453)
                    ·
                      refine ⟨3351828156089344726104835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17876416832476505205892453 3351828156089344726104835)
                      ·
                        rfl

theorem cell23_6527662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_6527662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527662 prefixEnd_6527662 := by exact prefixLift 6527662
  have htrace : WordTrace (prefixWord ++ tailWord_6527662) baseStart_6527662 baseEnd_6527662 := by
    simpa [prefixWord, tailWord_6527662, baseEnd_6527662] using wordTrace_append hprefix tailTrace_6527662
  have hstable : (prefixWord ++ tailWord_6527662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527662).length < 2 ^ (prefixWord ++ tailWord_6527662).sum := by decide
  have hdescent : baseEnd_6527662 < baseStart_6527662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527705 : List Nat := [1, 2, 1, 2, 3, 2, 2, 3, 2, 1, 4]
def baseStart_6527705 : Nat := 118140960795 + 6527705 * 2 ^ 59
def prefixEnd_6527705 : Nat := 4983230072969 + 3 ^ 40 * 6527705 * 2
def baseEnd_6527705 : Nat := 3351850235757488057867137

theorem tailTrace_6527705 : CollatzResearch.WordTrace tailWord_6527705 prefixEnd_6527705 3351850235757488057867137 := by
  unfold tailWord_6527705
  simp only [CollatzResearch.WordTrace]
  refine ⟨238084960816247103101904569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158723307210831402067936379 238084960816247103101904569)
  ·
    refine ⟨178563720612185327326428427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238084960816247103101904569 178563720612185327326428427)
    ·
      refine ⟨267845580918277990989642641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178563720612185327326428427 267845580918277990989642641)
      ·
        refine ⟨200884185688708493242231981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267845580918277990989642641 200884185688708493242231981)
        ·
          refine ⟨75331569633265684965836993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200884185688708493242231981 75331569633265684965836993)
          ·
            refine ⟨56498677224949263724377745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75331569633265684965836993 56498677224949263724377745)
            ·
              refine ⟨42374007918711947793283309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56498677224949263724377745 42374007918711947793283309)
              ·
                refine ⟨15890252969516980422481241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42374007918711947793283309 15890252969516980422481241)
                ·
                  refine ⟨11917689727137735316860931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15890252969516980422481241 11917689727137735316860931)
                  ·
                    refine ⟨17876534590706602975291397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11917689727137735316860931 17876534590706602975291397)
                    ·
                      refine ⟨3351850235757488057867137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17876534590706602975291397 3351850235757488057867137)
                      ·
                        rfl

theorem cell23_6527705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_6527705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527705 prefixEnd_6527705 := by exact prefixLift 6527705
  have htrace : WordTrace (prefixWord ++ tailWord_6527705) baseStart_6527705 baseEnd_6527705 := by
    simpa [prefixWord, tailWord_6527705, baseEnd_6527705] using wordTrace_append hprefix tailTrace_6527705
  have hstable : (prefixWord ++ tailWord_6527705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527705).length < 2 ^ (prefixWord ++ tailWord_6527705).sum := by decide
  have hdescent : baseEnd_6527705 < baseStart_6527705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527728 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 8]
def baseStart_6527728 : Nat := 118140960795 + 6527728 * 2 ^ 59
def prefixEnd_6527728 : Nat := 4983230072969 + 3 ^ 40 * 6527728 * 2
def baseEnd_6527728 : Nat := 372429116201393496431059

theorem tailTrace_6527728 : CollatzResearch.WordTrace tailWord_6527728 prefixEnd_6527728 372429116201393496431059 := by
  unfold tailWord_6527728
  simp only [CollatzResearch.WordTrace]
  refine ⟨119042899847581889014995919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158723866463442518686661225 119042899847581889014995919)
  ·
    refine ⟨178564349771372833522493879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119042899847581889014995919 178564349771372833522493879)
    ·
      refine ⟨267846524657059250283740819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178564349771372833522493879 267846524657059250283740819)
      ·
        refine ⟨401769786985588875425611229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267846524657059250283740819 401769786985588875425611229)
        ·
          refine ⟨150663670119595828284604211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401769786985588875425611229 150663670119595828284604211)
          ·
            refine ⟨225995505179393742426906317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150663670119595828284604211 225995505179393742426906317)
            ·
              refine ⟨84748314442272653410089869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225995505179393742426906317 84748314442272653410089869)
              ·
                refine ⟨31780617915852245028783701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84748314442272653410089869 31780617915852245028783701)
                ·
                  refine ⟨372429116201393496431059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31780617915852245028783701 372429116201393496431059)
                  ·
                    rfl

theorem cell23_6527728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 8].length) (baseStart_6527728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527728 prefixEnd_6527728 := by exact prefixLift 6527728
  have htrace : WordTrace (prefixWord ++ tailWord_6527728) baseStart_6527728 baseEnd_6527728 := by
    simpa [prefixWord, tailWord_6527728, baseEnd_6527728] using wordTrace_append hprefix tailTrace_6527728
  have hstable : (prefixWord ++ tailWord_6527728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527728).length < 2 ^ (prefixWord ++ tailWord_6527728).sum := by decide
  have hdescent : baseEnd_6527728 < baseStart_6527728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527806 : List Nat := [4, 2, 1, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_6527806 : Nat := 118140960795 + 6527806 * 2 ^ 59
def prefixEnd_6527806 : Nat := 4983230072969 + 3 ^ 40 * 6527806 * 2
def baseEnd_6527806 : Nat := 3351902097303592162704173

theorem tailTrace_6527806 : CollatzResearch.WordTrace tailWord_6527806 prefixEnd_6527806 3351902097303592162704173 := by
  unfold tailWord_6527806
  simp only [CollatzResearch.WordTrace]
  refine ⟨29761080573610149668916409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158725763059254131567554181 29761080573610149668916409)
  ·
    refine ⟨22320810430207612251687307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29761080573610149668916409 22320810430207612251687307)
    ·
      refine ⟨33481215645311418377530961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22320810430207612251687307 33481215645311418377530961)
      ·
        refine ⟨25110911733983563783148221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33481215645311418377530961 25110911733983563783148221)
        ·
          refine ⟨9416591900243836418680583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25110911733983563783148221 9416591900243836418680583)
          ·
            refine ⟨14124887850365754628020875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9416591900243836418680583 14124887850365754628020875)
            ·
              refine ⟨21187331775548631942031313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14124887850365754628020875 21187331775548631942031313)
              ·
                refine ⟨15890498831661473956523485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21187331775548631942031313 15890498831661473956523485)
                ·
                  refine ⟨5958937061873052733696307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15890498831661473956523485 5958937061873052733696307)
                  ·
                    refine ⟨8938405592809579100544461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5958937061873052733696307 8938405592809579100544461)
                    ·
                      refine ⟨3351902097303592162704173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8938405592809579100544461 3351902097303592162704173)
                      ·
                        rfl

theorem cell23_6527806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_6527806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527806 prefixEnd_6527806 := by exact prefixLift 6527806
  have htrace : WordTrace (prefixWord ++ tailWord_6527806) baseStart_6527806 baseEnd_6527806 := by
    simpa [prefixWord, tailWord_6527806, baseEnd_6527806] using wordTrace_append hprefix tailTrace_6527806
  have hstable : (prefixWord ++ tailWord_6527806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527806).length < 2 ^ (prefixWord ++ tailWord_6527806).sum := by decide
  have hdescent : baseEnd_6527806 < baseStart_6527806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527829 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 5, 2, 2]
def baseStart_6527829 : Nat := 118140960795 + 6527829 * 2 ^ 59
def prefixEnd_6527829 : Nat := 4983230072969 + 3 ^ 40 * 6527829 * 2
def baseEnd_6527829 : Nat := 3351913907358645572716567

theorem tailTrace_6527829 : CollatzResearch.WordTrace tailWord_6527829 prefixEnd_6527829 3351913907358645572716567 := by
  unfold tailWord_6527829
  simp only [CollatzResearch.WordTrace]
  refine ⟨238089483467797872279418541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158726322311865248186279027 238089483467797872279418541)
  ·
    refine ⟨89283556300424202104781953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238089483467797872279418541 89283556300424202104781953)
    ·
      refine ⟨66962667225318151578586465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89283556300424202104781953 66962667225318151578586465)
      ·
        refine ⟨50222000418988613683939849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66962667225318151578586465 50222000418988613683939849)
        ·
          refine ⟨37666500314241460262954887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50222000418988613683939849 37666500314241460262954887)
          ·
            refine ⟨56499750471362190394432331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37666500314241460262954887 56499750471362190394432331)
            ·
              refine ⟨84749625707043285591648497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56499750471362190394432331 84749625707043285591648497)
              ·
                refine ⟨63562219280282464193736373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84749625707043285591648497 63562219280282464193736373)
                ·
                  refine ⟨5958958057526481018162785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63562219280282464193736373 5958958057526481018162785)
                  ·
                    refine ⟨4469218543144860763622089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5958958057526481018162785 4469218543144860763622089)
                    ·
                      refine ⟨3351913907358645572716567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4469218543144860763622089 3351913907358645572716567)
                      ·
                        rfl

theorem cell23_6527829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_6527829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527829 prefixEnd_6527829 := by exact prefixLift 6527829
  have htrace : WordTrace (prefixWord ++ tailWord_6527829) baseStart_6527829 baseEnd_6527829 := by
    simpa [prefixWord, tailWord_6527829, baseEnd_6527829] using wordTrace_append hprefix tailTrace_6527829
  have hstable : (prefixWord ++ tailWord_6527829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527829).length < 2 ^ (prefixWord ++ tailWord_6527829).sum := by decide
  have hdescent : baseEnd_6527829 < baseStart_6527829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527874 : List Nat := [3, 4, 2, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_6527874 : Nat := 118140960795 + 6527874 * 2 ^ 59
def prefixEnd_6527874 : Nat := 4983230072969 + 3 ^ 40 * 6527874 * 2
def baseEnd_6527874 : Nat := 3351937013988097896653861

theorem tailTrace_6527874 : CollatzResearch.WordTrace tailWord_6527874 prefixEnd_6527874 3351937013988097896653861 := by
  unfold tailWord_6527874
  simp only [CollatzResearch.WordTrace]
  refine ⟨59522781188158711241201669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158727416501756563309871117 59522781188158711241201669)
  ·
    refine ⟨11160521472779758357725313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59522781188158711241201669 11160521472779758357725313)
    ·
      refine ⟨8370391104584818768293985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11160521472779758357725313 8370391104584818768293985)
      ·
        refine ⟨6277793328438614076220489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8370391104584818768293985 6277793328438614076220489)
        ·
          refine ⟨4708344996328960557165367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6277793328438614076220489 4708344996328960557165367)
          ·
            refine ⟨7062517494493440835748051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4708344996328960557165367 7062517494493440835748051)
            ·
              refine ⟨10593776241740161253622077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7062517494493440835748051 10593776241740161253622077)
              ·
                refine ⟨3972666090652560470108279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10593776241740161253622077 3972666090652560470108279)
                ·
                  refine ⟨5958999135978840705162419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3972666090652560470108279 5958999135978840705162419)
                  ·
                    refine ⟨8938498703968261057743629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5958999135978840705162419 8938498703968261057743629)
                    ·
                      refine ⟨3351937013988097896653861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8938498703968261057743629 3351937013988097896653861)
                      ·
                        rfl

theorem cell23_6527874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_6527874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527874 prefixEnd_6527874 := by exact prefixLift 6527874
  have htrace : WordTrace (prefixWord ++ tailWord_6527874) baseStart_6527874 baseEnd_6527874 := by
    simpa [prefixWord, tailWord_6527874, baseEnd_6527874] using wordTrace_append hprefix tailTrace_6527874
  have hstable : (prefixWord ++ tailWord_6527874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527874).length < 2 ^ (prefixWord ++ tailWord_6527874).sum := by decide
  have hdescent : baseEnd_6527874 < baseStart_6527874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527875 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 5]
def baseStart_6527875 : Nat := 118140960795 + 6527875 * 2 ^ 59
def prefixEnd_6527875 : Nat := 4983230072969 + 3 ^ 40 * 6527875 * 2
def baseEnd_6527875 : Nat := 3351937527468752392741355

theorem tailTrace_6527875 : CollatzResearch.WordTrace tailWord_6527875 prefixEnd_6527875 3351937527468752392741355 := by
  unfold tailWord_6527875
  simp only [CollatzResearch.WordTrace]
  refine ⟨238091161225631222135593079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158727440817087481423728719 238091161225631222135593079)
  ·
    refine ⟨357136741838446833203389619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238091161225631222135593079 357136741838446833203389619)
    ·
      refine ⟨535705112757670249805084429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357136741838446833203389619 535705112757670249805084429)
      ·
        refine ⟨200889417284126343676906661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 535705112757670249805084429 200889417284126343676906661)
        ·
          refine ⟨37666765740773689439419999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200889417284126343676906661 37666765740773689439419999)
          ·
            refine ⟨56500148611160534159129999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37666765740773689439419999 56500148611160534159129999)
            ·
              refine ⟨84750222916740801238694999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56500148611160534159129999 84750222916740801238694999)
              ·
                refine ⟨127125334375111201858042499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84750222916740801238694999 127125334375111201858042499)
                ·
                  refine ⟨190688001562666802787063749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127125334375111201858042499 190688001562666802787063749)
                  ·
                    refine ⟨35754000293000025522574453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 190688001562666802787063749 35754000293000025522574453)
                    ·
                      refine ⟨3351937527468752392741355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35754000293000025522574453 3351937527468752392741355)
                      ·
                        rfl

theorem cell23_6527875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_6527875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527875 prefixEnd_6527875 := by exact prefixLift 6527875
  have htrace : WordTrace (prefixWord ++ tailWord_6527875) baseStart_6527875 baseEnd_6527875 := by
    simpa [prefixWord, tailWord_6527875, baseEnd_6527875] using wordTrace_append hprefix tailTrace_6527875
  have hstable : (prefixWord ++ tailWord_6527875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527875).length < 2 ^ (prefixWord ++ tailWord_6527875).sum := by decide
  have hdescent : baseEnd_6527875 < baseStart_6527875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527879 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 4, 1, 3]
def baseStart_6527879 : Nat := 118140960795 + 6527879 * 2 ^ 59
def prefixEnd_6527879 : Nat := 4983230072969 + 3 ^ 40 * 6527879 * 2
def baseEnd_6527879 : Nat := 3351939581391370377091337

theorem tailTrace_6527879 : CollatzResearch.WordTrace tailWord_6527879 prefixEnd_6527879 3351939581391370377091337 := by
  unfold tailWord_6527879
  simp only [CollatzResearch.WordTrace]
  refine ⟨238091307117616730818738691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158727538078411153879159127 238091307117616730818738691)
  ·
    refine ⟨357136960676425096228108037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238091307117616730818738691 357136960676425096228108037)
    ·
      refine ⟨66963180126829705542770257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 357136960676425096228108037 66963180126829705542770257)
      ·
        refine ⟨50222385095122279157077693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66963180126829705542770257 50222385095122279157077693)
        ·
          refine ⟨18833394410670854683904135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50222385095122279157077693 18833394410670854683904135)
          ·
            refine ⟨28250091616006282025856203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18833394410670854683904135 28250091616006282025856203)
            ·
              refine ⟨42375137424009423038784305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28250091616006282025856203 42375137424009423038784305)
              ·
                refine ⟨31781353068007067279088229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42375137424009423038784305 31781353068007067279088229)
                ·
                  refine ⟨5959003700251325114829043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31781353068007067279088229 5959003700251325114829043)
                  ·
                    refine ⟨8938505550376987672243565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5959003700251325114829043 8938505550376987672243565)
                    ·
                      refine ⟨3351939581391370377091337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8938505550376987672243565 3351939581391370377091337)
                      ·
                        rfl

theorem cell23_6527879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_6527879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527879 prefixEnd_6527879 := by exact prefixLift 6527879
  have htrace : WordTrace (prefixWord ++ tailWord_6527879) baseStart_6527879 baseEnd_6527879 := by
    simpa [prefixWord, tailWord_6527879, baseEnd_6527879] using wordTrace_append hprefix tailTrace_6527879
  have hstable : (prefixWord ++ tailWord_6527879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527879).length < 2 ^ (prefixWord ++ tailWord_6527879).sum := by decide
  have hdescent : baseEnd_6527879 < baseStart_6527879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527880 : List Nat := [2, 1, 3, 3, 2, 3, 1, 3, 1, 2, 2]
def baseStart_6527880 : Nat := 118140960795 + 6527880 * 2 ^ 59
def prefixEnd_6527880 : Nat := 4983230072969 + 3 ^ 40 * 6527880 * 2
def baseEnd_6527880 : Nat := 3351940094872024873178833

theorem tailTrace_6527880 : CollatzResearch.WordTrace tailWord_6527880 prefixEnd_6527880 3351940094872024873178833 := by
  unfold tailWord_6527880
  simp only [CollatzResearch.WordTrace]
  refine ⟨119045671795306553994762547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158727562393742071993016729 119045671795306553994762547)
  ·
    refine ⟨178568507692959830992143821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119045671795306553994762547 178568507692959830992143821)
    ·
      refine ⟨66963190384859936622053933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178568507692959830992143821 66963190384859936622053933)
      ·
        refine ⟨25111196394322476233270225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66963190384859936622053933 25111196394322476233270225)
        ·
          refine ⟨18833397295741857174952669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25111196394322476233270225 18833397295741857174952669)
          ·
            refine ⟨7062523985903196440607251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18833397295741857174952669 7062523985903196440607251)
            ·
              refine ⟨10593785978854794660910877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7062523985903196440607251 10593785978854794660910877)
              ·
                refine ⟨3972669742070547997841579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10593785978854794660910877 3972669742070547997841579)
                ·
                  refine ⟨5959004613105821996762369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3972669742070547997841579 5959004613105821996762369)
                  ·
                    refine ⟨4469253459829366497571777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5959004613105821996762369 4469253459829366497571777)
                    ·
                      refine ⟨3351940094872024873178833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4469253459829366497571777 3351940094872024873178833)
                      ·
                        rfl

theorem cell23_6527880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_6527880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527880 prefixEnd_6527880 := by exact prefixLift 6527880
  have htrace : WordTrace (prefixWord ++ tailWord_6527880) baseStart_6527880 baseEnd_6527880 := by
    simpa [prefixWord, tailWord_6527880, baseEnd_6527880] using wordTrace_append hprefix tailTrace_6527880
  have hstable : (prefixWord ++ tailWord_6527880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527880).length < 2 ^ (prefixWord ++ tailWord_6527880).sum := by decide
  have hdescent : baseEnd_6527880 < baseStart_6527880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527892 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_6527892 : Nat := 118140960795 + 6527892 * 2 ^ 59
def prefixEnd_6527892 : Nat := 4983230072969 + 3 ^ 40 * 6527892 * 2
def baseEnd_6527892 : Nat := 3351946256639878826228777

theorem tailTrace_6527892 : CollatzResearch.WordTrace tailWord_6527892 prefixEnd_6527892 3351946256639878826228777 := by
  unfold tailWord_6527892
  simp only [CollatzResearch.WordTrace]
  refine ⟨119045890633284817019480965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158727854177713089359307953 119045890633284817019480965)
  ·
    refine ⟨22321104493740903191152681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119045890633284817019480965 22321104493740903191152681)
    ·
      refine ⟨16740828370305677393364511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22321104493740903191152681 16740828370305677393364511)
      ·
        refine ⟨25111242555458516090046767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16740828370305677393364511 25111242555458516090046767)
        ·
          refine ⟨37666863833187774135070151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25111242555458516090046767 37666863833187774135070151)
          ·
            refine ⟨56500295749781661202605227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37666863833187774135070151 56500295749781661202605227)
            ·
              refine ⟨84750443624672491803907841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56500295749781661202605227 84750443624672491803907841)
              ·
                refine ⟨63562832718504368852930881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84750443624672491803907841 63562832718504368852930881)
                ·
                  refine ⟨47672124538878276639698161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63562832718504368852930881 47672124538878276639698161)
                  ·
                    refine ⟨35754093404158707479773621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47672124538878276639698161 35754093404158707479773621)
                    ·
                      refine ⟨3351946256639878826228777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35754093404158707479773621 3351946256639878826228777)
                      ·
                        rfl

theorem cell23_6527892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_6527892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527892 prefixEnd_6527892 := by exact prefixLift 6527892
  have htrace : WordTrace (prefixWord ++ tailWord_6527892) baseStart_6527892 baseEnd_6527892 := by
    simpa [prefixWord, tailWord_6527892, baseEnd_6527892] using wordTrace_append hprefix tailTrace_6527892
  have hstable : (prefixWord ++ tailWord_6527892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527892).length < 2 ^ (prefixWord ++ tailWord_6527892).sum := by decide
  have hdescent : baseEnd_6527892 < baseStart_6527892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527919 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 6, 2, 2]
def baseStart_6527919 : Nat := 118140960795 + 6527919 * 2 ^ 59
def prefixEnd_6527919 : Nat := 4983230072969 + 3 ^ 40 * 6527919 * 2
def baseEnd_6527919 : Nat := 3351960120617550220591153

theorem tailTrace_6527919 : CollatzResearch.WordTrace tailWord_6527919 prefixEnd_6527919 3351960120617550220591153 := by
  unfold tailWord_6527919
  simp only [CollatzResearch.WordTrace]
  refine ⟨238092766037471817650194811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158728510691647878433463207 238092766037471817650194811)
  ·
    refine ⟨357139149056207726475292217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238092766037471817650194811 357139149056207726475292217)
    ·
      refine ⟨267854361792155794856469163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357139149056207726475292217 267854361792155794856469163)
      ·
        refine ⟨401781542688233692284703745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267854361792155794856469163 401781542688233692284703745)
        ·
          refine ⟨301336157016175269213527809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401781542688233692284703745 301336157016175269213527809)
          ·
            refine ⟨226002117762131451910145857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301336157016175269213527809 226002117762131451910145857)
            ·
              refine ⟨169501588321598588932609393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226002117762131451910145857 169501588321598588932609393)
              ·
                refine ⟨127126191241198941699457045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169501588321598588932609393 127126191241198941699457045)
                ·
                  refine ⟨5959040214431200392162049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127126191241198941699457045 5959040214431200392162049)
                  ·
                    refine ⟨4469280160823400294121537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5959040214431200392162049 4469280160823400294121537)
                    ·
                      refine ⟨3351960120617550220591153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4469280160823400294121537 3351960120617550220591153)
                      ·
                        rfl

theorem cell23_6527919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 2, 2].length) (baseStart_6527919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527919 prefixEnd_6527919 := by exact prefixLift 6527919
  have htrace : WordTrace (prefixWord ++ tailWord_6527919) baseStart_6527919 baseEnd_6527919 := by
    simpa [prefixWord, tailWord_6527919, baseEnd_6527919] using wordTrace_append hprefix tailTrace_6527919
  have hstable : (prefixWord ++ tailWord_6527919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527919).length < 2 ^ (prefixWord ++ tailWord_6527919).sum := by decide
  have hdescent : baseEnd_6527919 < baseStart_6527919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527935 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 7]
def baseStart_6527935 : Nat := 118140960795 + 6527935 * 2 ^ 59
def prefixEnd_6527935 : Nat := 4983230072969 + 3 ^ 40 * 6527935 * 2
def baseEnd_6527935 : Nat := 3351968336308022157991079

theorem tailTrace_6527935 : CollatzResearch.WordTrace tailWord_6527935 prefixEnd_6527935 3351968336308022157991079 := by
  unfold tailWord_6527935
  simp only [CollatzResearch.WordTrace]
  refine ⟨238093349605413852382777259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158728899736942568255184839 238093349605413852382777259)
  ·
    refine ⟨357140024408120778574165889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238093349605413852382777259 357140024408120778574165889)
    ·
      refine ⟨267855018306090583930624417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357140024408120778574165889 267855018306090583930624417)
      ·
        refine ⟨200891263729567937947968313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267855018306090583930624417 200891263729567937947968313)
        ·
          refine ⟨150668447797175953460976235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200891263729567937947968313 150668447797175953460976235)
          ·
            refine ⟨226002671695763930191464353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150668447797175953460976235 226002671695763930191464353)
            ·
              refine ⟨169502003771822947643598265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226002671695763930191464353 169502003771822947643598265)
              ·
                refine ⟨127126502828867210732698699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169502003771822947643598265 127126502828867210732698699)
                ·
                  refine ⟨190689754243300816099048049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127126502828867210732698699 190689754243300816099048049)
                  ·
                    refine ⟨143017315682475612074286037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 190689754243300816099048049 143017315682475612074286037)
                    ·
                      refine ⟨3351968336308022157991079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143017315682475612074286037 3351968336308022157991079)
                      ·
                        rfl

theorem cell23_6527935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_6527935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527935 prefixEnd_6527935 := by exact prefixLift 6527935
  have htrace : WordTrace (prefixWord ++ tailWord_6527935) baseStart_6527935 baseEnd_6527935 := by
    simpa [prefixWord, tailWord_6527935, baseEnd_6527935] using wordTrace_append hprefix tailTrace_6527935
  have hstable : (prefixWord ++ tailWord_6527935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527935).length < 2 ^ (prefixWord ++ tailWord_6527935).sum := by decide
  have hdescent : baseEnd_6527935 < baseStart_6527935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527945 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 2, 4, 6]
def baseStart_6527945 : Nat := 118140960795 + 6527945 * 2 ^ 59
def prefixEnd_6527945 : Nat := 4983230072969 + 3 ^ 40 * 6527945 * 2
def baseEnd_6527945 : Nat := 3351973471114567118866033

theorem tailTrace_6527945 : CollatzResearch.WordTrace tailWord_6527945 prefixEnd_6527945 3351973471114567118866033 := by
  unfold tailWord_6527945
  simp only [CollatzResearch.WordTrace]
  refine ⟨238093714335377624090641289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158729142890251749393760859 238093714335377624090641289)
  ·
    refine ⟨178570285751533218067980967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238093714335377624090641289 178570285751533218067980967)
    ·
      refine ⟨267855428627299827101971451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178570285751533218067980967 267855428627299827101971451)
      ·
        refine ⟨401783142940949740652957177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267855428627299827101971451 401783142940949740652957177)
        ·
          refine ⟨301337357205712305489717883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401783142940949740652957177 301337357205712305489717883)
          ·
            refine ⟨452006035808568458234576825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301337357205712305489717883 452006035808568458234576825)
            ·
              refine ⟨339004526856426343675932619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452006035808568458234576825 339004526856426343675932619)
              ·
                refine ⟨508506790284639515513898929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339004526856426343675932619 508506790284639515513898929)
                ·
                  refine ⟨381380092713479636635424197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508506790284639515513898929 381380092713479636635424197)
                  ·
                    refine ⟨71508767383777431869142037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 381380092713479636635424197 71508767383777431869142037)
                    ·
                      refine ⟨3351973471114567118866033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71508767383777431869142037 3351973471114567118866033)
                      ·
                        rfl

theorem cell23_6527945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_6527945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527945 prefixEnd_6527945 := by exact prefixLift 6527945
  have htrace : WordTrace (prefixWord ++ tailWord_6527945) baseStart_6527945 baseEnd_6527945 := by
    simpa [prefixWord, tailWord_6527945, baseEnd_6527945] using wordTrace_append hprefix tailTrace_6527945
  have hstable : (prefixWord ++ tailWord_6527945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527945).length < 2 ^ (prefixWord ++ tailWord_6527945).sum := by decide
  have hdescent : baseEnd_6527945 < baseStart_6527945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527952 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 3]
def baseStart_6527952 : Nat := 118140960795 + 6527952 * 2 ^ 59
def prefixEnd_6527952 : Nat := 4983230072969 + 3 ^ 40 * 6527952 * 2
def baseEnd_6527952 : Nat := 3351977065479148591478501

theorem tailTrace_6527952 : CollatzResearch.WordTrace tailWord_6527952 prefixEnd_6527952 3351977065479148591478501 := by
  unfold tailWord_6527952
  simp only [CollatzResearch.WordTrace]
  refine ⟨119046984823176132143073055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158729313097568176190764073 119046984823176132143073055)
  ·
    refine ⟨178570477234764198214609583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119046984823176132143073055 178570477234764198214609583)
    ·
      refine ⟨267855715852146297321914375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178570477234764198214609583 267855715852146297321914375)
      ·
        refine ⟨401783573778219445982871563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267855715852146297321914375 401783573778219445982871563)
        ·
          refine ⟨602675360667329168974307345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401783573778219445982871563 602675360667329168974307345)
          ·
            refine ⟨452006520500496876730730509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602675360667329168974307345 452006520500496876730730509)
            ·
              refine ⟨169502445187686328774023941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 452006520500496876730730509 169502445187686328774023941)
              ·
                refine ⟨31781708472691186645129489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169502445187686328774023941 31781708472691186645129489)
                ·
                  refine ⟨23836281354518389983847117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31781708472691186645129489 23836281354518389983847117)
                  ·
                    refine ⟨8938605507944396243942669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23836281354518389983847117 8938605507944396243942669)
                    ·
                      refine ⟨3351977065479148591478501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8938605507944396243942669 3351977065479148591478501)
                      ·
                        rfl

theorem cell23_6527952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 3].length) (baseStart_6527952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527952 prefixEnd_6527952 := by exact prefixLift 6527952
  have htrace : WordTrace (prefixWord ++ tailWord_6527952) baseStart_6527952 baseEnd_6527952 := by
    simpa [prefixWord, tailWord_6527952, baseEnd_6527952] using wordTrace_append hprefix tailTrace_6527952
  have hstable : (prefixWord ++ tailWord_6527952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527952).length < 2 ^ (prefixWord ++ tailWord_6527952).sum := by decide
  have hdescent : baseEnd_6527952 < baseStart_6527952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6527970 : List Nat := [3, 3, 3, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_6527970 : Nat := 118140960795 + 6527970 * 2 ^ 59
def prefixEnd_6527970 : Nat := 4983230072969 + 3 ^ 40 * 6527970 * 2
def baseEnd_6527970 : Nat := 3351986308130929521053419

theorem tailTrace_6527970 : CollatzResearch.WordTrace tailWord_6527970 prefixEnd_6527970 3351986308130929521053419 := by
  unfold tailWord_6527970
  simp only [CollatzResearch.WordTrace]
  refine ⟨59523656540071763340075341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158729750773524702240200909 59523656540071763340075341)
  ·
    refine ⟨22321371202526911252528253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59523656540071763340075341 22321371202526911252528253)
    ·
      refine ⟨8370514200947591719698095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22321371202526911252528253 8370514200947591719698095)
      ·
        refine ⟨12555771301421387579547143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8370514200947591719698095 12555771301421387579547143)
        ·
          refine ⟨18833656952132081369320715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12555771301421387579547143 18833656952132081369320715)
          ·
            refine ⟨28250485428198122053981073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18833656952132081369320715 28250485428198122053981073)
            ·
              refine ⟨21187864071148591540485805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28250485428198122053981073 21187864071148591540485805)
              ·
                refine ⟨7945449026680721827682177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21187864071148591540485805 7945449026680721827682177)
                ·
                  refine ⟨5959086770010541370761633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7945449026680721827682177 5959086770010541370761633)
                  ·
                    refine ⟨4469315077507906028071225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5959086770010541370761633 4469315077507906028071225)
                    ·
                      refine ⟨3351986308130929521053419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4469315077507906028071225 3351986308130929521053419)
                      ·
                        rfl

theorem cell23_6527970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_6527970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6527970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6527970 prefixEnd_6527970 := by exact prefixLift 6527970
  have htrace : WordTrace (prefixWord ++ tailWord_6527970) baseStart_6527970 baseEnd_6527970 := by
    simpa [prefixWord, tailWord_6527970, baseEnd_6527970] using wordTrace_append hprefix tailTrace_6527970
  have hstable : (prefixWord ++ tailWord_6527970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6527970).length < 2 ^ (prefixWord ++ tailWord_6527970).sum := by decide
  have hdescent : baseEnd_6527970 < baseStart_6527970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6527970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528036 : List Nat := [2, 3, 1, 4, 1, 1, 2, 2, 3, 4]
def baseStart_6528036 : Nat := 118140960795 + 6528036 * 2 ^ 59
def prefixEnd_6528036 : Nat := 4983230072969 + 3 ^ 40 * 6528036 * 2
def baseEnd_6528036 : Nat := 1117340065951375420942705

theorem tailTrace_6528036 : CollatzResearch.WordTrace tailWord_6528036 prefixEnd_6528036 1117340065951375420942705 := by
  unfold tailWord_6528036
  simp only [CollatzResearch.WordTrace]
  refine ⟨119048516689023973316101981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158731355585365297754802641 119048516689023973316101981)
  ·
    refine ⟨44643193758383989993538243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119048516689023973316101981 44643193758383989993538243)
    ·
      refine ⟨66964790637575984990307365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44643193758383989993538243 66964790637575984990307365)
      ·
        refine ⟨12555898244545497185682631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66964790637575984990307365 12555898244545497185682631)
        ·
          refine ⟨18833847366818245778523947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12555898244545497185682631 18833847366818245778523947)
          ·
            refine ⟨28250771050227368667785921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18833847366818245778523947 28250771050227368667785921)
            ·
              refine ⟨21188078287670526500839441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28250771050227368667785921 21188078287670526500839441)
              ·
                refine ⟨15891058715752894875629581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21188078287670526500839441 15891058715752894875629581)
                ·
                  refine ⟨5959147018407335578361093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15891058715752894875629581 5959147018407335578361093)
                  ·
                    refine ⟨1117340065951375420942705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5959147018407335578361093 1117340065951375420942705)
                    ·
                      rfl

theorem cell23_6528036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_6528036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528036 prefixEnd_6528036 := by exact prefixLift 6528036
  have htrace : WordTrace (prefixWord ++ tailWord_6528036) baseStart_6528036 baseEnd_6528036 := by
    simpa [prefixWord, tailWord_6528036, baseEnd_6528036] using wordTrace_append hprefix tailTrace_6528036
  have hstable : (prefixWord ++ tailWord_6528036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528036).length < 2 ^ (prefixWord ++ tailWord_6528036).sum := by decide
  have hdescent : baseEnd_6528036 < baseStart_6528036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528046 : List Nat := [4, 1, 3, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_6528046 : Nat := 118140960795 + 6528046 * 2 ^ 59
def prefixEnd_6528046 : Nat := 4983230072969 + 3 ^ 40 * 6528046 * 2
def baseEnd_6528046 : Nat := 3352025332660671223703069

theorem tailTrace_6528046 : CollatzResearch.WordTrace tailWord_6528046 prefixEnd_6528046 3352025332660671223703069 := by
  unfold tailWord_6528046
  simp only [CollatzResearch.WordTrace]
  refine ⟨29762174763501464792508499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158731598738674478893378661 29762174763501464792508499)
  ·
    refine ⟨44643262145252197188762749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29762174763501464792508499 44643262145252197188762749)
    ·
      refine ⟨16741223304469573945786031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44643262145252197188762749 16741223304469573945786031)
      ·
        refine ⟨25111834956704360918679047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16741223304469573945786031 25111834956704360918679047)
        ·
          refine ⟨37667752435056541378018571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25111834956704360918679047 37667752435056541378018571)
          ·
            refine ⟨56501628652584812067027857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37667752435056541378018571 56501628652584812067027857)
            ·
              refine ⟨42376221489438609050270893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56501628652584812067027857 42376221489438609050270893)
              ·
                refine ⟨15891083058539478393851585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42376221489438609050270893 15891083058539478393851585)
                ·
                  refine ⟨11918312293904608795388689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15891083058539478393851585 11918312293904608795388689)
                  ·
                    refine ⟨8938734220428456596541517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11918312293904608795388689 8938734220428456596541517)
                    ·
                      refine ⟨3352025332660671223703069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8938734220428456596541517 3352025332660671223703069)
                      ·
                        rfl

theorem cell23_6528046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_6528046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528046 prefixEnd_6528046 := by exact prefixLift 6528046
  have htrace : WordTrace (prefixWord ++ tailWord_6528046) baseStart_6528046 baseEnd_6528046 := by
    simpa [prefixWord, tailWord_6528046, baseEnd_6528046] using wordTrace_append hprefix tailTrace_6528046
  have hstable : (prefixWord ++ tailWord_6528046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528046).length < 2 ^ (prefixWord ++ tailWord_6528046).sum := by decide
  have hdescent : baseEnd_6528046 < baseStart_6528046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528070 : List Nat := [6, 1, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_6528070 : Nat := 118140960795 + 6528070 * 2 ^ 59
def prefixEnd_6528070 : Nat := 4983230072969 + 3 ^ 40 * 6528070 * 2
def baseEnd_6528070 : Nat := 1117345885398793043267653

theorem tailTrace_6528070 : CollatzResearch.WordTrace tailWord_6528070 prefixEnd_6528070 1117345885398793043267653 := by
  unfold tailWord_6528070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7440571045622649076216927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158732182306616513625961109 7440571045622649076216927)
  ·
    refine ⟨11160856568433973614325391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7440571045622649076216927 11160856568433973614325391)
    ·
      refine ⟨16741284852650960421488087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11160856568433973614325391 16741284852650960421488087)
      ·
        refine ⟨25111927278976440632232131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16741284852650960421488087 25111927278976440632232131)
        ·
          refine ⟨37667890918464660948348197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25111927278976440632232131 37667890918464660948348197)
          ·
            refine ⟨7062729547212123927815287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37667890918464660948348197 7062729547212123927815287)
            ·
              refine ⟨10594094320818185891722931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7062729547212123927815287 10594094320818185891722931)
              ·
                refine ⟨15891141481227278837584397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10594094320818185891722931 15891141481227278837584397)
                ·
                  refine ⟨5959178055460229564094149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15891141481227278837584397 5959178055460229564094149)
                  ·
                    refine ⟨1117345885398793043267653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5959178055460229564094149 1117345885398793043267653)
                    ·
                      rfl

theorem cell23_6528070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_6528070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528070 prefixEnd_6528070 := by exact prefixLift 6528070
  have htrace : WordTrace (prefixWord ++ tailWord_6528070) baseStart_6528070 baseEnd_6528070 := by
    simpa [prefixWord, tailWord_6528070, baseEnd_6528070] using wordTrace_append hprefix tailTrace_6528070
  have hstable : (prefixWord ++ tailWord_6528070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528070).length < 2 ^ (prefixWord ++ tailWord_6528070).sum := by decide
  have hdescent : baseEnd_6528070 < baseStart_6528070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528103 : List Nat := [1, 1, 5, 1, 1, 4, 2, 1, 2, 3, 2]
def baseStart_6528103 : Nat := 118140960795 + 6528103 * 2 ^ 59
def prefixEnd_6528103 : Nat := 4983230072969 + 3 ^ 40 * 6528103 * 2
def baseEnd_6528103 : Nat := 3352054601057977500690307

theorem tailTrace_6528103 : CollatzResearch.WordTrace tailWord_6528103 prefixEnd_6528103 3352054601057977500690307 := by
  unfold tailWord_6528103
  simp only [CollatzResearch.WordTrace]
  refine ⟨238099477068805217074892963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158732984712536811383261975 238099477068805217074892963)
  ·
    refine ⟨357149215603207825612339445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238099477068805217074892963 357149215603207825612339445)
    ·
      refine ⟨33482738962800733651156823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 357149215603207825612339445 33482738962800733651156823)
      ·
        refine ⟨50224108444201100476735235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33482738962800733651156823 50224108444201100476735235)
        ·
          refine ⟨75336162666301650715102853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50224108444201100476735235 75336162666301650715102853)
          ·
            refine ⟨14125530499931559509081785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75336162666301650715102853 14125530499931559509081785)
            ·
              refine ⟨10594147874948669631811339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14125530499931559509081785 10594147874948669631811339)
              ·
                refine ⟨15891221812423004447717009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10594147874948669631811339 15891221812423004447717009)
                ·
                  refine ⟨11918416359317253335787757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15891221812423004447717009 11918416359317253335787757)
                  ·
                    refine ⟨4469406134743970000920409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11918416359317253335787757 4469406134743970000920409)
                    ·
                      refine ⟨3352054601057977500690307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4469406134743970000920409 3352054601057977500690307)
                      ·
                        rfl

theorem cell23_6528103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_6528103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528103 prefixEnd_6528103 := by exact prefixLift 6528103
  have htrace : WordTrace (prefixWord ++ tailWord_6528103) baseStart_6528103 baseEnd_6528103 := by
    simpa [prefixWord, tailWord_6528103, baseEnd_6528103] using wordTrace_append hprefix tailTrace_6528103
  have hstable : (prefixWord ++ tailWord_6528103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528103).length < 2 ^ (prefixWord ++ tailWord_6528103).sum := by decide
  have hdescent : baseEnd_6528103 < baseStart_6528103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528109 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_6528109 : Nat := 118140960795 + 6528109 * 2 ^ 59
def prefixEnd_6528109 : Nat := 4983230072969 + 3 ^ 40 * 6528109 * 2
def baseEnd_6528109 : Nat := 1117352560647301492405093

theorem tailTrace_6528109 : CollatzResearch.WordTrace tailWord_6528109 prefixEnd_6528109 1117352560647301492405093 := by
  unfold tailWord_6528109
  simp only [CollatzResearch.WordTrace]
  refine ⟨238099695906783480099611381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158733130604522320066407587 238099695906783480099611381)
  ·
    refine ⟨22321846491260951259338567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 238099695906783480099611381 22321846491260951259338567)
    ·
      refine ⟨33482769736891426889007851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22321846491260951259338567 33482769736891426889007851)
      ·
        refine ⟨50224154605337140333511777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33482769736891426889007851 50224154605337140333511777)
        ·
          refine ⟨37668115954002855250133833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50224154605337140333511777 37668115954002855250133833)
          ·
            refine ⟨28251086965502141437600375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37668115954002855250133833 28251086965502141437600375)
            ·
              refine ⟨42376630448253212156400563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28251086965502141437600375 42376630448253212156400563)
              ·
                refine ⟨63564945672379818234600845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42376630448253212156400563 63564945672379818234600845)
                ·
                  refine ⟨23836854627142431837975317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63564945672379818234600845 23836854627142431837975317)
                  ·
                    refine ⟨1117352560647301492405093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23836854627142431837975317 1117352560647301492405093)
                    ·
                      rfl

theorem cell23_6528109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_6528109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528109 prefixEnd_6528109 := by exact prefixLift 6528109
  have htrace : WordTrace (prefixWord ++ tailWord_6528109) baseStart_6528109 baseEnd_6528109 := by
    simpa [prefixWord, tailWord_6528109, baseEnd_6528109] using wordTrace_append hprefix tailTrace_6528109
  have hstable : (prefixWord ++ tailWord_6528109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528109).length < 2 ^ (prefixWord ++ tailWord_6528109).sum := by decide
  have hdescent : baseEnd_6528109 < baseStart_6528109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528146 : List Nat := [3, 2, 3, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_6528146 : Nat := 118140960795 + 6528146 * 2 ^ 59
def prefixEnd_6528146 : Nat := 4983230072969 + 3 ^ 40 * 6528146 * 2
def baseEnd_6528146 : Nat := 3352076680726120832452609

theorem tailTrace_6528146 : CollatzResearch.WordTrace tailWord_6528146 prefixEnd_6528146 3352076680726120832452609 := by
  unfold tailWord_6528146
  simp only [CollatzResearch.WordTrace]
  refine ⟨59525261351912358854677073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158734030271766290279138861 59525261351912358854677073)
  ·
    refine ⟨44643946013934269141007805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59525261351912358854677073 44643946013934269141007805)
    ·
      refine ⟨16741479755225350927877927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44643946013934269141007805 16741479755225350927877927)
      ·
        refine ⟨25112219632838026391816891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16741479755225350927877927 25112219632838026391816891)
        ·
          refine ⟨37668329449257039587725337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25112219632838026391816891 37668329449257039587725337)
          ·
            refine ⟨28251247086942779690794003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37668329449257039587725337 28251247086942779690794003)
            ·
              refine ⟨42376870630414169536191005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28251247086942779690794003 42376870630414169536191005)
              ·
                refine ⟨15891326486405313576071627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42376870630414169536191005 15891326486405313576071627)
                ·
                  refine ⟨23836989729607970364107441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15891326486405313576071627 23836989729607970364107441)
                  ·
                    refine ⟨17877742297205977773080581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23836989729607970364107441 17877742297205977773080581)
                    ·
                      refine ⟨3352076680726120832452609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17877742297205977773080581 3352076680726120832452609)
                      ·
                        rfl

theorem cell23_6528146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_6528146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528146 prefixEnd_6528146 := by exact prefixLift 6528146
  have htrace : WordTrace (prefixWord ++ tailWord_6528146) baseStart_6528146 baseEnd_6528146 := by
    simpa [prefixWord, tailWord_6528146, baseEnd_6528146] using wordTrace_append hprefix tailTrace_6528146
  have hstable : (prefixWord ++ tailWord_6528146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528146).length < 2 ^ (prefixWord ++ tailWord_6528146).sum := by decide
  have hdescent : baseEnd_6528146 < baseStart_6528146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528156 : List Nat := [2, 2, 3, 2, 1, 3, 3, 7]
def baseStart_6528156 : Nat := 118140960795 + 6528156 * 2 ^ 59
def prefixEnd_6528156 : Nat := 4983230072969 + 3 ^ 40 * 6528156 * 2
def baseEnd_6528156 : Nat := 124151178353061696049169

theorem tailTrace_6528156 : CollatzResearch.WordTrace tailWord_6528156 prefixEnd_6528156 124151178353061696049169 := by
  unfold tailWord_6528156
  simp only [CollatzResearch.WordTrace]
  refine ⟨119050705068806603563286161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158734273425075471417714881 119050705068806603563286161)
  ·
    refine ⟨89288028801604952672464621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119050705068806603563286161 89288028801604952672464621)
    ·
      refine ⟨33483010800601857252174233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89288028801604952672464621 33483010800601857252174233)
      ·
        refine ⟨25112258100451392939130675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33483010800601857252174233 25112258100451392939130675)
        ·
          refine ⟨37668387150677089408696013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25112258100451392939130675 37668387150677089408696013)
          ·
            refine ⟨14125645181503908528261005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37668387150677089408696013 14125645181503908528261005)
            ·
              refine ⟨5297116943063965698097877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14125645181503908528261005 5297116943063965698097877)
              ·
                refine ⟨124151178353061696049169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5297116943063965698097877 124151178353061696049169)
                ·
                  rfl

theorem cell23_6528156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 7].length) (baseStart_6528156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528156 prefixEnd_6528156 := by exact prefixLift 6528156
  have htrace : WordTrace (prefixWord ++ tailWord_6528156) baseStart_6528156 baseEnd_6528156 := by
    simpa [prefixWord, tailWord_6528156, baseEnd_6528156] using wordTrace_append hprefix tailTrace_6528156
  have hstable : (prefixWord ++ tailWord_6528156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528156).length < 2 ^ (prefixWord ++ tailWord_6528156).sum := by decide
  have hdescent : baseEnd_6528156 < baseStart_6528156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528167 : List Nat := [1, 1, 6, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_6528167 : Nat := 118140960795 + 6528167 * 2 ^ 59
def prefixEnd_6528167 : Nat := 4983230072969 + 3 ^ 40 * 6528167 * 2
def baseEnd_6528167 : Nat := 3352087463819865250290013

theorem tailTrace_6528167 : CollatzResearch.WordTrace tailWord_6528167 prefixEnd_6528167 3352087463819865250290013 := by
  unfold tailWord_6528167
  simp only [CollatzResearch.WordTrace]
  refine ⟨238101811340573356005222755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158734540893715570670148503 238101811340573356005222755)
  ·
    refine ⟨357152717010860034007834133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238101811340573356005222755 357152717010860034007834133)
    ·
      refine ⟨16741533609884064094117225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 357152717010860034007834133 16741533609884064094117225)
      ·
        refine ⟨12556150207413048070587919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16741533609884064094117225 12556150207413048070587919)
        ·
          refine ⟨18834225311119572105881879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12556150207413048070587919 18834225311119572105881879)
          ·
            refine ⟨28251337966679358158822819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18834225311119572105881879 28251337966679358158822819)
            ·
              refine ⟨42377006950019037238234229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28251337966679358158822819 42377006950019037238234229)
              ·
                refine ⟨3972844401564284741084459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42377006950019037238234229 3972844401564284741084459)
                ·
                  refine ⟨5959266602346427111626689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3972844401564284741084459 5959266602346427111626689)
                  ·
                    refine ⟨4469449951759820333720017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5959266602346427111626689 4469449951759820333720017)
                    ·
                      refine ⟨3352087463819865250290013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4469449951759820333720017 3352087463819865250290013)
                      ·
                        rfl

theorem cell23_6528167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_6528167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528167 prefixEnd_6528167 := by exact prefixLift 6528167
  have htrace : WordTrace (prefixWord ++ tailWord_6528167) baseStart_6528167 baseEnd_6528167 := by
    simpa [prefixWord, tailWord_6528167, baseEnd_6528167] using wordTrace_append hprefix tailTrace_6528167
  have hstable : (prefixWord ++ tailWord_6528167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528167).length < 2 ^ (prefixWord ++ tailWord_6528167).sum := by decide
  have hdescent : baseEnd_6528167 < baseStart_6528167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528170 : List Nat := [3, 1, 5, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_6528170 : Nat := 118140960795 + 6528170 * 2 ^ 59
def prefixEnd_6528170 : Nat := 4983230072969 + 3 ^ 40 * 6528170 * 2
def baseEnd_6528170 : Nat := 3352089004261828738552499

theorem tailTrace_6528170 : CollatzResearch.WordTrace tailWord_6528170 prefixEnd_6528170 3352089004261828738552499 := by
  unfold tailWord_6528170
  simp only [CollatzResearch.WordTrace]
  refine ⟨59525480189890621879395491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158734613839708325011721309 59525480189890621879395491)
  ·
    refine ⟨89288220284835932819093237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59525480189890621879395491 89288220284835932819093237)
    ·
      refine ⟨8370770651703368701789991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89288220284835932819093237 8370770651703368701789991)
      ·
        refine ⟨12556155977555053052684987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8370770651703368701789991 12556155977555053052684987)
        ·
          refine ⟨18834233966332579579027481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12556155977555053052684987 18834233966332579579027481)
          ·
            refine ⟨14125675474749434684270611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18834233966332579579027481 14125675474749434684270611)
            ·
              refine ⟨21188513212124152026405917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14125675474749434684270611 21188513212124152026405917)
              ·
                refine ⟨7945692454546557009902219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21188513212124152026405917 7945692454546557009902219)
                ·
                  refine ⟨11918538681819835514853329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7945692454546557009902219 11918538681819835514853329)
                  ·
                    refine ⟨8938904011364876636139997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11918538681819835514853329 8938904011364876636139997)
                    ·
                      refine ⟨3352089004261828738552499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8938904011364876636139997 3352089004261828738552499)
                      ·
                        rfl

theorem cell23_6528170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_6528170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528170 prefixEnd_6528170 := by exact prefixLift 6528170
  have htrace : WordTrace (prefixWord ++ tailWord_6528170) baseStart_6528170 baseEnd_6528170 := by
    simpa [prefixWord, tailWord_6528170, baseEnd_6528170] using wordTrace_append hprefix tailTrace_6528170
  have hstable : (prefixWord ++ tailWord_6528170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528170).length < 2 ^ (prefixWord ++ tailWord_6528170).sum := by decide
  have hdescent : baseEnd_6528170 < baseStart_6528170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528189 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_6528189 : Nat := 118140960795 + 6528189 * 2 ^ 59
def prefixEnd_6528189 : Nat := 4983230072969 + 3 ^ 40 * 6528189 * 2
def baseEnd_6528189 : Nat := 3352098760394264164214911

theorem tailTrace_6528189 : CollatzResearch.WordTrace tailWord_6528189 prefixEnd_6528189 3352098760394264164214911 := by
  unfold tailWord_6528189
  simp only [CollatzResearch.WordTrace]
  refine ⟨238102613746493653762523621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158735075830995769175015747 238102613746493653762523621)
  ·
    refine ⟨44644240077467560080473179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238102613746493653762523621 44644240077467560080473179)
    ·
      refine ⟨66966360116201340120709769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44644240077467560080473179 66966360116201340120709769)
      ·
        refine ⟨50224770087151005090532327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66966360116201340120709769 50224770087151005090532327)
        ·
          refine ⟨75337155130726507635798491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50224770087151005090532327 75337155130726507635798491)
          ·
            refine ⟨113005732696089761453697737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75337155130726507635798491 113005732696089761453697737)
            ·
              refine ⟨84754299522067321090273303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113005732696089761453697737 84754299522067321090273303)
              ·
                refine ⟨127131449283100981635409955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84754299522067321090273303 127131449283100981635409955)
                ·
                  refine ⟨190697173924651472453114933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127131449283100981635409955 190697173924651472453114933)
                  ·
                    refine ⟨17877860055436075542479525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 190697173924651472453114933 17877860055436075542479525)
                    ·
                      refine ⟨3352098760394264164214911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17877860055436075542479525 3352098760394264164214911)
                      ·
                        rfl

theorem cell23_6528189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_6528189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528189 prefixEnd_6528189 := by exact prefixLift 6528189
  have htrace : WordTrace (prefixWord ++ tailWord_6528189) baseStart_6528189 baseEnd_6528189 := by
    simpa [prefixWord, tailWord_6528189, baseEnd_6528189] using wordTrace_append hprefix tailTrace_6528189
  have hstable : (prefixWord ++ tailWord_6528189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528189).length < 2 ^ (prefixWord ++ tailWord_6528189).sum := by decide
  have hdescent : baseEnd_6528189 < baseStart_6528189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528194 : List Nat := [3, 5, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_6528194 : Nat := 118140960795 + 6528194 * 2 ^ 59
def prefixEnd_6528194 : Nat := 4983230072969 + 3 ^ 40 * 6528194 * 2
def baseEnd_6528194 : Nat := 1117367109265845548217463

theorem tailTrace_6528194 : CollatzResearch.WordTrace tailWord_6528194 prefixEnd_6528194 1117367109265845548217463 := by
  unfold tailWord_6528194
  simp only [CollatzResearch.WordTrace]
  refine ⟨59525699027868884904113909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158735197407650359744303757 59525699027868884904113909)
  ·
    refine ⟨5580534283862707959760679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59525699027868884904113909 5580534283862707959760679)
    ·
      refine ⟨8370801425794061939641019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5580534283862707959760679 8370801425794061939641019)
      ·
        refine ⟨12556202138691092909461529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8370801425794061939641019 12556202138691092909461529)
        ·
          refine ⟨9417151604018319682096147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12556202138691092909461529 9417151604018319682096147)
          ·
            refine ⟨14125727406027479523144221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9417151604018319682096147 14125727406027479523144221)
            ·
              refine ⟨5297147777260304821179083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14125727406027479523144221 5297147777260304821179083)
              ·
                refine ⟨7945721665890457231768625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5297147777260304821179083 7945721665890457231768625)
                ·
                  refine ⟨5959291249417842923826469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7945721665890457231768625 5959291249417842923826469)
                  ·
                    refine ⟨1117367109265845548217463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5959291249417842923826469 1117367109265845548217463)
                    ·
                      rfl

theorem cell23_6528194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_6528194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528194 prefixEnd_6528194 := by exact prefixLift 6528194
  have htrace : WordTrace (prefixWord ++ tailWord_6528194) baseStart_6528194 baseEnd_6528194 := by
    simpa [prefixWord, tailWord_6528194, baseEnd_6528194] using wordTrace_append hprefix tailTrace_6528194
  have hstable : (prefixWord ++ tailWord_6528194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528194).length < 2 ^ (prefixWord ++ tailWord_6528194).sum := by decide
  have hdescent : baseEnd_6528194 < baseStart_6528194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528209 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 2, 1, 5]
def baseStart_6528209 : Nat := 118140960795 + 6528209 * 2 ^ 59
def prefixEnd_6528209 : Nat := 4983230072969 + 3 ^ 40 * 6528209 * 2
def baseEnd_6528209 : Nat := 3352109030007354085964819

theorem tailTrace_6528209 : CollatzResearch.WordTrace tailWord_6528209 prefixEnd_6528209 3352109030007354085964819 := by
  unfold tailWord_6528209
  simp only [CollatzResearch.WordTrace]
  refine ⟨238103343206421197178251681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158735562137614131452167787 238103343206421197178251681)
  ·
    refine ⟨178577507404815897883688761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238103343206421197178251681 178577507404815897883688761)
    ·
      refine ⟨133933130553611923412766571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178577507404815897883688761 133933130553611923412766571)
      ·
        refine ⟨200899695830417885119149857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133933130553611923412766571 200899695830417885119149857)
        ·
          refine ⟨150674771872813413839362393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200899695830417885119149857 150674771872813413839362393)
          ·
            refine ⟨113006078904610060379521795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150674771872813413839362393 113006078904610060379521795)
            ·
              refine ⟨169509118356915090569282693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113006078904610060379521795 169509118356915090569282693)
              ·
                refine ⟨31782959691921579481740505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169509118356915090569282693 31782959691921579481740505)
                ·
                  refine ⟨23837219768941184611305379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31782959691921579481740505 23837219768941184611305379)
                  ·
                    refine ⟨35755829653411776916958069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23837219768941184611305379 35755829653411776916958069)
                    ·
                      refine ⟨3352109030007354085964819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35755829653411776916958069 3352109030007354085964819)
                      ·
                        rfl

theorem cell23_6528209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_6528209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528209 prefixEnd_6528209 := by exact prefixLift 6528209
  have htrace : WordTrace (prefixWord ++ tailWord_6528209) baseStart_6528209 baseEnd_6528209 := by
    simpa [prefixWord, tailWord_6528209, baseEnd_6528209] using wordTrace_append hprefix tailTrace_6528209
  have hstable : (prefixWord ++ tailWord_6528209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528209).length < 2 ^ (prefixWord ++ tailWord_6528209).sum := by decide
  have hdescent : baseEnd_6528209 < baseStart_6528209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528210 : List Nat := [3, 2, 2, 2, 1, 1, 4, 2, 1, 3, 2]
def baseStart_6528210 : Nat := 118140960795 + 6528210 * 2 ^ 59
def prefixEnd_6528210 : Nat := 4983230072969 + 3 ^ 40 * 6528210 * 2
def baseEnd_6528210 : Nat := 3352109543488008582052315

theorem tailTrace_6528210 : CollatzResearch.WordTrace tailWord_6528210 prefixEnd_6528210 3352109543488008582052315 := by
  unfold tailWord_6528210
  simp only [CollatzResearch.WordTrace]
  refine ⟨59525844919854393587259521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158735586452945049566025389 59525844919854393587259521)
  ·
    refine ⟨44644383689890795190444641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59525844919854393587259521 44644383689890795190444641)
    ·
      refine ⟨33483287767418096392833481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44644383689890795190444641 33483287767418096392833481)
      ·
        refine ⟨25112465825563572294625111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33483287767418096392833481 25112465825563572294625111)
        ·
          refine ⟨37668698738345358441937667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25112465825563572294625111 37668698738345358441937667)
          ·
            refine ⟨56503048107518037662906501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37668698738345358441937667 56503048107518037662906501)
            ·
              refine ⟨10594321520159632061794969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56503048107518037662906501 10594321520159632061794969)
              ·
                refine ⟨7945741140119724046346227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10594321520159632061794969 7945741140119724046346227)
                ·
                  refine ⟨11918611710179586069519341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7945741140119724046346227 11918611710179586069519341)
                  ·
                    refine ⟨4469479391317344776069753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11918611710179586069519341 4469479391317344776069753)
                    ·
                      refine ⟨3352109543488008582052315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4469479391317344776069753 3352109543488008582052315)
                      ·
                        rfl

theorem cell23_6528210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_6528210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528210 prefixEnd_6528210 := by exact prefixLift 6528210
  have htrace : WordTrace (prefixWord ++ tailWord_6528210) baseStart_6528210 baseEnd_6528210 := by
    simpa [prefixWord, tailWord_6528210, baseEnd_6528210] using wordTrace_append hprefix tailTrace_6528210
  have hstable : (prefixWord ++ tailWord_6528210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528210).length < 2 ^ (prefixWord ++ tailWord_6528210).sum := by decide
  have hdescent : baseEnd_6528210 < baseStart_6528210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528223 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 4, 2, 2]
def baseStart_6528223 : Nat := 118140960795 + 6528223 * 2 ^ 59
def prefixEnd_6528223 : Nat := 4983230072969 + 3 ^ 40 * 6528223 * 2
def baseEnd_6528223 : Nat := 3352116218736517031189755

theorem tailTrace_6528223 : CollatzResearch.WordTrace tailWord_6528223 prefixEnd_6528223 3352116218736517031189755 := by
  unfold tailWord_6528223
  simp only [CollatzResearch.WordTrace]
  refine ⟨238103853828370477569261323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158735902552246985046174215 238103853828370477569261323)
  ·
    refine ⟨357155780742555716353891985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238103853828370477569261323 357155780742555716353891985)
    ·
      refine ⟨267866835556916787265418989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357155780742555716353891985 267866835556916787265418989)
      ·
        refine ⟨100450063333843795224532121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267866835556916787265418989 100450063333843795224532121)
        ·
          refine ⟨75337547500382846418399091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100450063333843795224532121 75337547500382846418399091)
          ·
            refine ⟨113006321250574269627598637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75337547500382846418399091 113006321250574269627598637)
            ·
              refine ⟨42377370468965351110349489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113006321250574269627598637 42377370468965351110349489)
              ·
                refine ⟨31783027851724013332762117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42377370468965351110349489 31783027851724013332762117)
                ·
                  refine ⟨5959317722198252499892897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31783027851724013332762117 5959317722198252499892897)
                  ·
                    refine ⟨4469488291648689374919673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5959317722198252499892897 4469488291648689374919673)
                    ·
                      refine ⟨3352116218736517031189755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4469488291648689374919673 3352116218736517031189755)
                      ·
                        rfl

theorem cell23_6528223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_6528223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528223 prefixEnd_6528223 := by exact prefixLift 6528223
  have htrace : WordTrace (prefixWord ++ tailWord_6528223) baseStart_6528223 baseEnd_6528223 := by
    simpa [prefixWord, tailWord_6528223, baseEnd_6528223] using wordTrace_append hprefix tailTrace_6528223
  have hstable : (prefixWord ++ tailWord_6528223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528223).length < 2 ^ (prefixWord ++ tailWord_6528223).sum := by decide
  have hdescent : baseEnd_6528223 < baseStart_6528223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528257 : List Nat := [1, 2, 4, 1, 1, 3, 4, 1, 2, 2, 2]
def baseStart_6528257 : Nat := 118140960795 + 6528257 * 2 ^ 59
def prefixEnd_6528257 : Nat := 4983230072969 + 3 ^ 40 * 6528257 * 2
def baseEnd_6528257 : Nat := 3352133677078769898164599

theorem tailTrace_6528257 : CollatzResearch.WordTrace tailWord_6528257 prefixEnd_6528257 3352133677078769898164599 := by
  unfold tailWord_6528257
  simp only [CollatzResearch.WordTrace]
  refine ⟨238105093910247301375999025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158736729273498200917332683 238105093910247301375999025)
  ·
    refine ⟨178578820432685476031999269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238105093910247301375999025 178578820432685476031999269)
    ·
      refine ⟨33483528831128526755999863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178578820432685476031999269 33483528831128526755999863)
      ·
        refine ⟨50225293246692790133999795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33483528831128526755999863 50225293246692790133999795)
        ·
          refine ⟨75337939870039185200999693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50225293246692790133999795 75337939870039185200999693)
          ·
            refine ⟨28251727451264694450374885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75337939870039185200999693 28251727451264694450374885)
            ·
              refine ⟨5297198897112130209445291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28251727451264694450374885 5297198897112130209445291)
              ·
                refine ⟨7945798345668195314167937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5297198897112130209445291 7945798345668195314167937)
                ·
                  refine ⟨5959348759251146485625953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7945798345668195314167937 5959348759251146485625953)
                  ·
                    refine ⟨4469511569438359864219465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5959348759251146485625953 4469511569438359864219465)
                    ·
                      refine ⟨3352133677078769898164599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4469511569438359864219465 3352133677078769898164599)
                      ·
                        rfl

theorem cell23_6528257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_6528257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528257 prefixEnd_6528257 := by exact prefixLift 6528257
  have htrace : WordTrace (prefixWord ++ tailWord_6528257) baseStart_6528257 baseEnd_6528257 := by
    simpa [prefixWord, tailWord_6528257, baseEnd_6528257] using wordTrace_append hprefix tailTrace_6528257
  have hstable : (prefixWord ++ tailWord_6528257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528257).length < 2 ^ (prefixWord ++ tailWord_6528257).sum := by decide
  have hdescent : baseEnd_6528257 < baseStart_6528257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528356 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_6528356 : Nat := 118140960795 + 6528356 * 2 ^ 59
def prefixEnd_6528356 : Nat := 4983230072969 + 3 ^ 40 * 6528356 * 2
def baseEnd_6528356 : Nat := 3352184511663565010826643

theorem tailTrace_6528356 : CollatzResearch.WordTrace tailWord_6528356 prefixEnd_6528356 3352184511663565010826643 := by
  unfold tailWord_6528356
  simp only [CollatzResearch.WordTrace]
  refine ⟨119054352368444320641926461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158739136491259094189235281 119054352368444320641926461)
  ·
    refine ⟨44645382138166620240722423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119054352368444320641926461 44645382138166620240722423)
    ·
      refine ⟨66968073207249930361083635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44645382138166620240722423 66968073207249930361083635)
      ·
        refine ⟨100452109810874895541625453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66968073207249930361083635 100452109810874895541625453)
        ·
          refine ⟨37669541179078085828109545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100452109810874895541625453 37669541179078085828109545)
          ·
            refine ⟨28252155884308564371082159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37669541179078085828109545 28252155884308564371082159)
            ·
              refine ⟨42378233826462846556623239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28252155884308564371082159 42378233826462846556623239)
              ·
                refine ⟨63567350739694269834934859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42378233826462846556623239 63567350739694269834934859)
                ·
                  refine ⟨95351026109541404752402289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63567350739694269834934859 95351026109541404752402289)
                  ·
                    refine ⟨71513269582156053564301717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95351026109541404752402289 71513269582156053564301717)
                    ·
                      refine ⟨3352184511663565010826643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71513269582156053564301717 3352184511663565010826643)
                      ·
                        rfl

theorem cell23_6528356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_6528356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528356 prefixEnd_6528356 := by exact prefixLift 6528356
  have htrace : WordTrace (prefixWord ++ tailWord_6528356) baseStart_6528356 baseEnd_6528356 := by
    simpa [prefixWord, tailWord_6528356, baseEnd_6528356] using wordTrace_append hprefix tailTrace_6528356
  have hstable : (prefixWord ++ tailWord_6528356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528356).length < 2 ^ (prefixWord ++ tailWord_6528356).sum := by decide
  have hdescent : baseEnd_6528356 < baseStart_6528356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528396 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 3, 6]
def baseStart_6528396 : Nat := 118140960795 + 6528396 * 2 ^ 59
def prefixEnd_6528396 : Nat := 4983230072969 + 3 ^ 40 * 6528396 * 2
def baseEnd_6528396 : Nat := 1117401683629914951442153

theorem tailTrace_6528396 : CollatzResearch.WordTrace tailWord_6528396 prefixEnd_6528396 1117401683629914951442153 := by
  unfold tailWord_6528396
  simp only [CollatzResearch.WordTrace]
  refine ⟨119055081828371864057654521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158740109104495818743539361 119055081828371864057654521)
  ·
    refine ⟨89291311371278898043240891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119055081828371864057654521 89291311371278898043240891)
    ·
      refine ⟨133936967056918347064861337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89291311371278898043240891 133936967056918347064861337)
      ·
        refine ⟨100452725292688760298646003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133936967056918347064861337 100452725292688760298646003)
        ·
          refine ⟨150679087939033140447969005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100452725292688760298646003 150679087939033140447969005)
          ·
            refine ⟨56504657977137427667988377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150679087939033140447969005 56504657977137427667988377)
            ·
              refine ⟨42378493482853070750991283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56504657977137427667988377 42378493482853070750991283)
              ·
                refine ⟨63567740224279606126486925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42378493482853070750991283 63567740224279606126486925)
                ·
                  refine ⟨23837902584104852297432597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63567740224279606126486925 23837902584104852297432597)
                  ·
                    refine ⟨1117401683629914951442153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23837902584104852297432597 1117401683629914951442153)
                    ·
                      rfl

theorem cell23_6528396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_6528396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528396 prefixEnd_6528396 := by exact prefixLift 6528396
  have htrace : WordTrace (prefixWord ++ tailWord_6528396) baseStart_6528396 baseEnd_6528396 := by
    simpa [prefixWord, tailWord_6528396, baseEnd_6528396] using wordTrace_append hprefix tailTrace_6528396
  have hstable : (prefixWord ++ tailWord_6528396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528396).length < 2 ^ (prefixWord ++ tailWord_6528396).sum := by decide
  have hdescent : baseEnd_6528396 < baseStart_6528396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528416 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 6]
def baseStart_6528416 : Nat := 118140960795 + 6528416 * 2 ^ 59
def prefixEnd_6528416 : Nat := 4983230072969 + 3 ^ 40 * 6528416 * 2
def baseEnd_6528416 : Nat := 3352215320502834776076367

theorem tailTrace_6528416 : CollatzResearch.WordTrace tailWord_6528416 prefixEnd_6528416 3352215320502834776076367 := by
  unfold tailWord_6528416
  simp only [CollatzResearch.WordTrace]
  refine ⟨119055446558335635765518551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158740595411114181020691401 119055446558335635765518551)
  ·
    refine ⟨178583169837503453648277827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119055446558335635765518551 178583169837503453648277827)
    ·
      refine ⟨267874754756255180472416741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178583169837503453648277827 267874754756255180472416741)
      ·
        refine ⟨50226516516797846338578139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267874754756255180472416741 50226516516797846338578139)
        ·
          refine ⟨75339774775196769507867209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50226516516797846338578139 75339774775196769507867209)
          ·
            refine ⟨56504831081397577130900407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75339774775196769507867209 56504831081397577130900407)
            ·
              refine ⟨84757246622096365696350611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56504831081397577130900407 84757246622096365696350611)
              ·
                refine ⟨127135869933144548544525917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84757246622096365696350611 127135869933144548544525917)
                ·
                  refine ⟨47675951224929205704197219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127135869933144548544525917 47675951224929205704197219)
                  ·
                    refine ⟨71513926837393808556295829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47675951224929205704197219 71513926837393808556295829)
                    ·
                      refine ⟨3352215320502834776076367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71513926837393808556295829 3352215320502834776076367)
                      ·
                        rfl

theorem cell23_6528416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_6528416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528416 prefixEnd_6528416 := by exact prefixLift 6528416
  have htrace : WordTrace (prefixWord ++ tailWord_6528416) baseStart_6528416 baseEnd_6528416 := by
    simpa [prefixWord, tailWord_6528416, baseEnd_6528416] using wordTrace_append hprefix tailTrace_6528416
  have hstable : (prefixWord ++ tailWord_6528416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528416).length < 2 ^ (prefixWord ++ tailWord_6528416).sum := by decide
  have hdescent : baseEnd_6528416 < baseStart_6528416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528423 : List Nat := [1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_6528423 : Nat := 118140960795 + 6528423 * 2 ^ 59
def prefixEnd_6528423 : Nat := 4983230072969 + 3 ^ 40 * 6528423 * 2
def baseEnd_6528423 : Nat := 3352218914867416248688835

theorem tailTrace_6528423 : CollatzResearch.WordTrace tailWord_6528423 prefixEnd_6528423 3352218914867416248688835 := by
  unfold tailWord_6528423
  simp only [CollatzResearch.WordTrace]
  refine ⟨238111148427645911726541923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158740765618430607817694615 238111148427645911726541923)
  ·
    refine ⟨357166722641468867589812885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238111148427645911726541923 357166722641468867589812885)
    ·
      refine ⟨16742190123818853168272479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 357166722641468867589812885 16742190123818853168272479)
      ·
        refine ⟨25113285185728279752408719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16742190123818853168272479 25113285185728279752408719)
        ·
          refine ⟨37669927778592419628613079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25113285185728279752408719 37669927778592419628613079)
          ·
            refine ⟨56504891667888629442919619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37669927778592419628613079 56504891667888629442919619)
            ·
              refine ⟨84757337501832944164379429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56504891667888629442919619 84757337501832944164379429)
              ·
                refine ⟨15892000781593677030821143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84757337501832944164379429 15892000781593677030821143)
                ·
                  refine ⟨23838001172390515546231715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15892000781593677030821143 23838001172390515546231715)
                  ·
                    refine ⟨35757001758585773319347573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23838001172390515546231715 35757001758585773319347573)
                    ·
                      refine ⟨3352218914867416248688835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35757001758585773319347573 3352218914867416248688835)
                      ·
                        rfl

theorem cell23_6528423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_6528423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528423 prefixEnd_6528423 := by exact prefixLift 6528423
  have htrace : WordTrace (prefixWord ++ tailWord_6528423) baseStart_6528423 baseEnd_6528423 := by
    simpa [prefixWord, tailWord_6528423, baseEnd_6528423] using wordTrace_append hprefix tailTrace_6528423
  have hstable : (prefixWord ++ tailWord_6528423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528423).length < 2 ^ (prefixWord ++ tailWord_6528423).sum := by decide
  have hdescent : baseEnd_6528423 < baseStart_6528423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528433 : List Nat := [1, 2, 2, 4, 1, 1, 2, 3, 1, 2, 4]
def baseStart_6528433 : Nat := 118140960795 + 6528433 * 2 ^ 59
def prefixEnd_6528433 : Nat := 4983230072969 + 3 ^ 40 * 6528433 * 2
def baseEnd_6528433 : Nat := 3352224049673961209563789

theorem tailTrace_6528433 : CollatzResearch.WordTrace tailWord_6528433 prefixEnd_6528433 3352224049673961209563789 := by
  unfold tailWord_6528433
  simp only [CollatzResearch.WordTrace]
  refine ⟨238111513157609683434405953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158741008771739788956270635 238111513157609683434405953)
  ·
    refine ⟨178583634868207262575804465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238111513157609683434405953 178583634868207262575804465)
    ·
      refine ⟨133937726151155446931853349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178583634868207262575804465 133937726151155446931853349)
      ·
        refine ⟨25113323653341646299722503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133937726151155446931853349 25113323653341646299722503)
        ·
          refine ⟨37669985480012469449583755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25113323653341646299722503 37669985480012469449583755)
          ·
            refine ⟨56504978220018704174375633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37669985480012469449583755 56504978220018704174375633)
            ·
              refine ⟨42378733665014028130781725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56504978220018704174375633 42378733665014028130781725)
              ·
                refine ⟨15892025124380260549043147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42378733665014028130781725 15892025124380260549043147)
                ·
                  refine ⟨23838037686570390823564721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15892025124380260549043147 23838037686570390823564721)
                  ·
                    refine ⟨17878528264927793117673541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23838037686570390823564721 17878528264927793117673541)
                    ·
                      refine ⟨3352224049673961209563789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17878528264927793117673541 3352224049673961209563789)
                      ·
                        rfl

theorem cell23_6528433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_6528433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528433 prefixEnd_6528433 := by exact prefixLift 6528433
  have htrace : WordTrace (prefixWord ++ tailWord_6528433) baseStart_6528433 baseEnd_6528433 := by
    simpa [prefixWord, tailWord_6528433, baseEnd_6528433] using wordTrace_append hprefix tailTrace_6528433
  have hstable : (prefixWord ++ tailWord_6528433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528433).length < 2 ^ (prefixWord ++ tailWord_6528433).sum := by decide
  have hdescent : baseEnd_6528433 < baseStart_6528433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528437 : List Nat := [1, 3, 3, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_6528437 : Nat := 118140960795 + 6528437 * 2 ^ 59
def prefixEnd_6528437 : Nat := 4983230072969 + 3 ^ 40 * 6528437 * 2
def baseEnd_6528437 : Nat := 3352226103596579193913771

theorem tailTrace_6528437 : CollatzResearch.WordTrace tailWord_6528437 prefixEnd_6528437 3352226103596579193913771 := by
  unfold tailWord_6528437
  simp only [CollatzResearch.WordTrace]
  refine ⟨238111659049595192117551565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158741106033063461411701043 238111659049595192117551565)
  ·
    refine ⟨89291872143598197044081837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238111659049595192117551565 89291872143598197044081837)
    ·
      refine ⟨33484452053849323891530689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89291872143598197044081837 33484452053849323891530689)
      ·
        refine ⟨25113339040386992918648017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33484452053849323891530689 25113339040386992918648017)
        ·
          refine ⟨18835004280290244688986013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25113339040386992918648017 18835004280290244688986013)
          ·
            refine ⟨7063126605108841758369755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18835004280290244688986013 7063126605108841758369755)
            ·
              refine ⟨10594689907663262637554633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7063126605108841758369755 10594689907663262637554633)
              ·
                refine ⟨7946017430747446978165975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10594689907663262637554633 7946017430747446978165975)
                ·
                  refine ⟨11919026146121170467248963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7946017430747446978165975 11919026146121170467248963)
                  ·
                    refine ⟨17878539219181755700873445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11919026146121170467248963 17878539219181755700873445)
                    ·
                      refine ⟨3352226103596579193913771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17878539219181755700873445 3352226103596579193913771)
                      ·
                        rfl

theorem cell23_6528437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_6528437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528437 prefixEnd_6528437 := by exact prefixLift 6528437
  have htrace : WordTrace (prefixWord ++ tailWord_6528437) baseStart_6528437 baseEnd_6528437 := by
    simpa [prefixWord, tailWord_6528437, baseEnd_6528437] using wordTrace_append hprefix tailTrace_6528437
  have hstable : (prefixWord ++ tailWord_6528437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528437).length < 2 ^ (prefixWord ++ tailWord_6528437).sum := by decide
  have hdescent : baseEnd_6528437 < baseStart_6528437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528440 : List Nat := [2, 1, 2, 1, 2, 2, 5, 2, 1, 2, 3]
def baseStart_6528440 : Nat := 118140960795 + 6528440 * 2 ^ 59
def prefixEnd_6528440 : Nat := 4983230072969 + 3 ^ 40 * 6528440 * 2
def baseEnd_6528440 : Nat := 3352227644038542682176257

theorem tailTrace_6528440 : CollatzResearch.WordTrace tailWord_6528440 prefixEnd_6528440 3352227644038542682176257 := by
  unfold tailWord_6528440
  simp only [CollatzResearch.WordTrace]
  refine ⟨119055884234292161814955387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158741178979056215753273849 119055884234292161814955387)
  ·
    refine ⟨178583826351438242722433081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119055884234292161814955387 178583826351438242722433081)
    ·
      refine ⟨133937869763578682041824811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178583826351438242722433081 133937869763578682041824811)
      ·
        refine ⟨200906804645368023062737217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133937869763578682041824811 200906804645368023062737217)
        ·
          refine ⟨150680103484026017297052913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200906804645368023062737217 150680103484026017297052913)
          ·
            refine ⟨113010077613019512972789685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150680103484026017297052913 113010077613019512972789685)
            ·
              refine ⟨10594694776220579341199033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113010077613019512972789685 10594694776220579341199033)
              ·
                refine ⟨7946021082165434505899275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10594694776220579341199033 7946021082165434505899275)
                ·
                  refine ⟨11919031623248151758848913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7946021082165434505899275 11919031623248151758848913)
                  ·
                    refine ⟨8939273717436113819136685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11919031623248151758848913 8939273717436113819136685)
                    ·
                      refine ⟨3352227644038542682176257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8939273717436113819136685 3352227644038542682176257)
                      ·
                        rfl

theorem cell23_6528440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 1, 2, 3].length) (baseStart_6528440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528440 prefixEnd_6528440 := by exact prefixLift 6528440
  have htrace : WordTrace (prefixWord ++ tailWord_6528440) baseStart_6528440 baseEnd_6528440 := by
    simpa [prefixWord, tailWord_6528440, baseEnd_6528440] using wordTrace_append hprefix tailTrace_6528440
  have hstable : (prefixWord ++ tailWord_6528440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528440).length < 2 ^ (prefixWord ++ tailWord_6528440).sum := by decide
  have hdescent : baseEnd_6528440 < baseStart_6528440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528487 : List Nat := [1, 1, 5, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_6528487 : Nat := 118140960795 + 6528487 * 2 ^ 59
def prefixEnd_6528487 : Nat := 4983230072969 + 3 ^ 40 * 6528487 * 2
def baseEnd_6528487 : Nat := 3352251777629303998288541

theorem tailTrace_6528487 : CollatzResearch.WordTrace tailWord_6528487 prefixEnd_6528487 3352251777629303998288541 := by
  unfold tailWord_6528487
  simp only [CollatzResearch.WordTrace]
  refine ⟨238113482699414050656871715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158742321799609367104581143 238113482699414050656871715)
  ·
    refine ⟨357170224049121075985307573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238113482699414050656871715 357170224049121075985307573)
    ·
      refine ⟨33484708504605100873622585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 357170224049121075985307573 33484708504605100873622585)
      ·
        refine ⟨25113531378453825655216939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33484708504605100873622585 25113531378453825655216939)
        ·
          refine ⟨37670297067680738482825409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25113531378453825655216939 37670297067680738482825409)
          ·
            refine ⟨28252722800760553862119057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37670297067680738482825409 28252722800760553862119057)
            ·
              refine ⟨21189542100570415396589293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28252722800760553862119057 21189542100570415396589293)
              ·
                refine ⟨7946078287713905773720985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21189542100570415396589293 7946078287713905773720985)
                ·
                  refine ⟨5959558715785429330290739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7946078287713905773720985 5959558715785429330290739)
                  ·
                    refine ⟨8939338073678143995436109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5959558715785429330290739 8939338073678143995436109)
                    ·
                      refine ⟨3352251777629303998288541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8939338073678143995436109 3352251777629303998288541)
                      ·
                        rfl

theorem cell23_6528487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_6528487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528487 prefixEnd_6528487 := by exact prefixLift 6528487
  have htrace : WordTrace (prefixWord ++ tailWord_6528487) baseStart_6528487 baseEnd_6528487 := by
    simpa [prefixWord, tailWord_6528487, baseEnd_6528487] using wordTrace_append hprefix tailTrace_6528487
  have hstable : (prefixWord ++ tailWord_6528487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528487).length < 2 ^ (prefixWord ++ tailWord_6528487).sum := by decide
  have hdescent : baseEnd_6528487 < baseStart_6528487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528533 : List Nat := [1, 3, 2, 1, 3, 2, 1, 3, 7]
def baseStart_6528533 : Nat := 118140960795 + 6528533 * 2 ^ 59
def prefixEnd_6528533 : Nat := 4983230072969 + 3 ^ 40 * 6528533 * 2
def baseEnd_6528533 : Nat := 372475044193267868701481

theorem tailTrace_6528533 : CollatzResearch.WordTrace tailWord_6528533 prefixEnd_6528533 372475044193267868701481 := by
  unfold tailWord_6528533
  simp only [CollatzResearch.WordTrace]
  refine ⟨238115160457247400513046253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158743440304831600342030835 238115160457247400513046253)
  ·
    refine ⟨89293185171467775192392345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238115160457247400513046253 89293185171467775192392345)
    ·
      refine ⟨66969888878600831394294259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89293185171467775192392345 66969888878600831394294259)
      ·
        refine ⟨100454833317901247091441389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66969888878600831394294259 100454833317901247091441389)
        ·
          refine ⟨37670562494212967659290521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100454833317901247091441389 37670562494212967659290521)
          ·
            refine ⟨28252921870659725744467891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37670562494212967659290521 28252921870659725744467891)
            ·
              refine ⟨42379382805989588616701837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28252921870659725744467891 42379382805989588616701837)
              ·
                refine ⟨15892268552246095731263189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42379382805989588616701837 15892268552246095731263189)
                ·
                  refine ⟨372475044193267868701481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15892268552246095731263189 372475044193267868701481)
                  ·
                    rfl

theorem cell23_6528533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 7].length) (baseStart_6528533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528533 prefixEnd_6528533 := by exact prefixLift 6528533
  have htrace : WordTrace (prefixWord ++ tailWord_6528533) baseStart_6528533 baseEnd_6528533 := by
    simpa [prefixWord, tailWord_6528533, baseEnd_6528533] using wordTrace_append hprefix tailTrace_6528533
  have hstable : (prefixWord ++ tailWord_6528533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528533).length < 2 ^ (prefixWord ++ tailWord_6528533).sum := by decide
  have hdescent : baseEnd_6528533 < baseStart_6528533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528544 : List Nat := [2, 1, 1, 6, 1, 3, 1, 1, 1, 4, 2]
def baseStart_6528544 : Nat := 118140960795 + 6528544 * 2 ^ 59
def prefixEnd_6528544 : Nat := 4983230072969 + 3 ^ 40 * 6528544 * 2
def baseEnd_6528544 : Nat := 3352281046026610275275779

theorem tailTrace_6528544 : CollatzResearch.WordTrace tailWord_6528544 prefixEnd_6528544 3352281046026610275275779 := by
  unfold tailWord_6528544
  simp only [CollatzResearch.WordTrace]
  refine ⟨119057780830103774695848343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158743707773471699594464457 119057780830103774695848343)
  ·
    refine ⟨178586671245155662043772515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119057780830103774695848343 178586671245155662043772515)
    ·
      refine ⟨267880006867733493065658773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178586671245155662043772515 267880006867733493065658773)
      ·
        refine ⟨12556875321925007487452755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 267880006867733493065658773 12556875321925007487452755)
        ·
          refine ⟨18835312982887511231179133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12556875321925007487452755 18835312982887511231179133)
          ·
            refine ⟨7063242368582816711692175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18835312982887511231179133 7063242368582816711692175)
            ·
              refine ⟨10594863552874225067538263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7063242368582816711692175 10594863552874225067538263)
              ·
                refine ⟨15892295329311337601307395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10594863552874225067538263 15892295329311337601307395)
                ·
                  refine ⟨23838442993967006401961093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15892295329311337601307395 23838442993967006401961093)
                  ·
                    refine ⟨4469708061368813700367705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23838442993967006401961093 4469708061368813700367705)
                    ·
                      refine ⟨3352281046026610275275779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4469708061368813700367705 3352281046026610275275779)
                      ·
                        rfl

theorem cell23_6528544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_6528544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528544 prefixEnd_6528544 := by exact prefixLift 6528544
  have htrace : WordTrace (prefixWord ++ tailWord_6528544) baseStart_6528544 baseEnd_6528544 := by
    simpa [prefixWord, tailWord_6528544, baseEnd_6528544] using wordTrace_append hprefix tailTrace_6528544
  have hstable : (prefixWord ++ tailWord_6528544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528544).length < 2 ^ (prefixWord ++ tailWord_6528544).sum := by decide
  have hdescent : baseEnd_6528544 < baseStart_6528544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528563 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 1, 7]
def baseStart_6528563 : Nat := 118140960795 + 6528563 * 2 ^ 59
def prefixEnd_6528563 : Nat := 4983230072969 + 3 ^ 40 * 6528563 * 2
def baseEnd_6528563 : Nat := 1117430267386348566979397

theorem tailTrace_6528563 : CollatzResearch.WordTrace tailWord_6528563 prefixEnd_6528563 1117430267386348566979397 := by
  unfold tailWord_6528563
  simp only [CollatzResearch.WordTrace]
  refine ⟨238116254647138715636638343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158744169764759143757758895 238116254647138715636638343)
  ·
    refine ⟨357174381970708073454957515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238116254647138715636638343 357174381970708073454957515)
    ·
      refine ⟨535761572956062110182436273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357174381970708073454957515 535761572956062110182436273)
      ·
        refine ⟨401821179717046582636827205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535761572956062110182436273 401821179717046582636827205)
        ·
          refine ⟨75341471196946234244405101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 401821179717046582636827205 75341471196946234244405101)
          ·
            refine ⟨28253051698854837841651913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75341471196946234244405101 28253051698854837841651913)
            ·
              refine ⟨21189788774141128381238935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28253051698854837841651913 21189788774141128381238935)
              ·
                refine ⟨31784683161211692571858403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21189788774141128381238935 31784683161211692571858403)
                ·
                  refine ⟨47677024741817538857787605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31784683161211692571858403 47677024741817538857787605)
                  ·
                    refine ⟨1117430267386348566979397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47677024741817538857787605 1117430267386348566979397)
                    ·
                      rfl

theorem cell23_6528563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 7].length) (baseStart_6528563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528563 prefixEnd_6528563 := by exact prefixLift 6528563
  have htrace : WordTrace (prefixWord ++ tailWord_6528563) baseStart_6528563 baseEnd_6528563 := by
    simpa [prefixWord, tailWord_6528563, baseEnd_6528563] using wordTrace_append hprefix tailTrace_6528563
  have hstable : (prefixWord ++ tailWord_6528563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528563).length < 2 ^ (prefixWord ++ tailWord_6528563).sum := by decide
  have hdescent : baseEnd_6528563 < baseStart_6528563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528567 : List Nat := [1, 1, 3, 1, 2, 6, 1, 3, 5]
def baseStart_6528567 : Nat := 118140960795 + 6528567 * 2 ^ 59
def prefixEnd_6528567 : Nat := 4983230072969 + 3 ^ 40 * 6528567 * 2
def baseEnd_6528567 : Nat := 372476984009073742809797

theorem tailTrace_6528567 : CollatzResearch.WordTrace tailWord_6528567 prefixEnd_6528567 372476984009073742809797 := by
  unfold tailWord_6528567
  simp only [CollatzResearch.WordTrace]
  refine ⟨238116400539124224319783955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158744267026082816213189303 238116400539124224319783955)
  ·
    refine ⟨357174600808686336479675933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238116400539124224319783955 357174600808686336479675933)
    ·
      refine ⟨133940475303257376179878475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357174600808686336479675933 133940475303257376179878475)
      ·
        refine ⟨200910712954886064269817713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133940475303257376179878475 200910712954886064269817713)
        ·
          refine ⟨150683034716164548202363285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200910712954886064269817713 150683034716164548202363285)
          ·
            refine ⟨7063267252320213196985779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 150683034716164548202363285 7063267252320213196985779)
            ·
              refine ⟨10594900878480319795478669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7063267252320213196985779 10594900878480319795478669)
              ·
                refine ⟨3973087829430119923304501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10594900878480319795478669 3973087829430119923304501)
                ·
                  refine ⟨372476984009073742809797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3973087829430119923304501 372476984009073742809797)
                  ·
                    rfl

theorem cell23_6528567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 5].length) (baseStart_6528567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528567 prefixEnd_6528567 := by exact prefixLift 6528567
  have htrace : WordTrace (prefixWord ++ tailWord_6528567) baseStart_6528567 baseEnd_6528567 := by
    simpa [prefixWord, tailWord_6528567, baseEnd_6528567] using wordTrace_append hprefix tailTrace_6528567
  have hstable : (prefixWord ++ tailWord_6528567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528567).length < 2 ^ (prefixWord ++ tailWord_6528567).sum := by decide
  have hdescent : baseEnd_6528567 < baseStart_6528567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528600 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 1, 6, 2]
def baseStart_6528600 : Nat := 118140960795 + 6528600 * 2 ^ 59
def prefixEnd_6528600 : Nat := 4983230072969 + 3 ^ 40 * 6528600 * 2
def baseEnd_6528600 : Nat := 3352309800943262056175521

theorem tailTrace_6528600 : CollatzResearch.WordTrace tailWord_6528600 prefixEnd_6528600 3352309800943262056175521 := by
  unfold tailWord_6528600
  simp only [CollatzResearch.WordTrace]
  refine ⟨119058802074002335477867627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158745069432003113970490169 119058802074002335477867627)
  ·
    refine ⟨178588203111003503216801441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119058802074002335477867627 178588203111003503216801441)
    ·
      refine ⟨133941152333252627412601081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178588203111003503216801441 133941152333252627412601081)
      ·
        refine ⟨100455864249939470559450811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133941152333252627412601081 100455864249939470559450811)
        ·
          refine ⟨150683796374909205839176217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100455864249939470559450811 150683796374909205839176217)
          ·
            refine ⟨113012847281181904379382163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150683796374909205839176217 113012847281181904379382163)
            ·
              refine ⟨169519270921772856569073245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113012847281181904379382163 169519270921772856569073245)
              ·
                refine ⟨63569726595664821213402467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169519270921772856569073245 63569726595664821213402467)
                ·
                  refine ⟨95354589893497231820103701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63569726595664821213402467 95354589893497231820103701)
                  ·
                    refine ⟨4469746401257682741567361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95354589893497231820103701 4469746401257682741567361)
                    ·
                      refine ⟨3352309800943262056175521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4469746401257682741567361 3352309800943262056175521)
                      ·
                        rfl

theorem cell23_6528600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_6528600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528600 prefixEnd_6528600 := by exact prefixLift 6528600
  have htrace : WordTrace (prefixWord ++ tailWord_6528600) baseStart_6528600 baseEnd_6528600 := by
    simpa [prefixWord, tailWord_6528600, baseEnd_6528600] using wordTrace_append hprefix tailTrace_6528600
  have hstable : (prefixWord ++ tailWord_6528600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528600).length < 2 ^ (prefixWord ++ tailWord_6528600).sum := by decide
  have hdescent : baseEnd_6528600 < baseStart_6528600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528637 : List Nat := [1, 4, 1, 1, 4, 1, 2, 2, 2, 2, 3]
def baseStart_6528637 : Nat := 118140960795 + 6528637 * 2 ^ 59
def prefixEnd_6528637 : Nat := 4983230072969 + 3 ^ 40 * 6528637 * 2
def baseEnd_6528637 : Nat := 3352328799727478411412851

theorem tailTrace_6528637 : CollatzResearch.WordTrace tailWord_6528637 prefixEnd_6528637 3352328799727478411412851 := by
  unfold tailWord_6528637
  simp only [CollatzResearch.WordTrace]
  refine ⟨238118953648870626274832165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158745969099247084183221443 238118953648870626274832165)
  ·
    refine ⟨44647303809163242426531031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238118953648870626274832165 44647303809163242426531031)
    ·
      refine ⟨66970955713744863639796547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44647303809163242426531031 66970955713744863639796547)
      ·
        refine ⟨100456433570617295459694821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66970955713744863639796547 100456433570617295459694821)
        ·
          refine ⟨18835581294490742898692779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100456433570617295459694821 18835581294490742898692779)
          ·
            refine ⟨28253371941736114348039169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18835581294490742898692779 28253371941736114348039169)
            ·
              refine ⟨21190028956302085761029377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28253371941736114348039169 21190028956302085761029377)
              ·
                refine ⟨15892521717226564320772033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21190028956302085761029377 15892521717226564320772033)
                ·
                  refine ⟨11919391287919923240579025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15892521717226564320772033 11919391287919923240579025)
                  ·
                    refine ⟨8939543465939942430434269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11919391287919923240579025 8939543465939942430434269)
                    ·
                      refine ⟨3352328799727478411412851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8939543465939942430434269 3352328799727478411412851)
                      ·
                        rfl

theorem cell23_6528637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_6528637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528637 prefixEnd_6528637 := by exact prefixLift 6528637
  have htrace : WordTrace (prefixWord ++ tailWord_6528637) baseStart_6528637 baseEnd_6528637 := by
    simpa [prefixWord, tailWord_6528637, baseEnd_6528637] using wordTrace_append hprefix tailTrace_6528637
  have hstable : (prefixWord ++ tailWord_6528637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528637).length < 2 ^ (prefixWord ++ tailWord_6528637).sum := by decide
  have hdescent : baseEnd_6528637 < baseStart_6528637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528640 : List Nat := [2, 1, 1, 2, 1, 4, 4, 2, 6]
def baseStart_6528640 : Nat := 118140960795 + 6528640 * 2 ^ 59
def prefixEnd_6528640 : Nat := 4983230072969 + 3 ^ 40 * 6528640 * 2
def baseEnd_6528640 : Nat := 372481148907715766630593

theorem tailTrace_6528640 : CollatzResearch.WordTrace tailWord_6528640 prefixEnd_6528640 372481148907715766630593 := by
  unfold tailWord_6528640
  simp only [CollatzResearch.WordTrace]
  refine ⟨119059531533929878893595687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158746042045239838524794249 119059531533929878893595687)
  ·
    refine ⟨178589297300894818340393531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119059531533929878893595687 178589297300894818340393531)
    ·
      refine ⟨267883945951342227510590297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178589297300894818340393531 267883945951342227510590297)
      ·
        refine ⟨200912959463506670632942723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267883945951342227510590297 200912959463506670632942723)
        ·
          refine ⟨301369439195260005949414085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200912959463506670632942723 301369439195260005949414085)
          ·
            refine ⟨56506769849111251115515141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 301369439195260005949414085 56506769849111251115515141)
            ·
              refine ⟨10595019346708359584159089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56506769849111251115515141 10595019346708359584159089)
              ·
                refine ⟨7946264510031269688119317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10595019346708359584159089 7946264510031269688119317)
                ·
                  refine ⟨372481148907715766630593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7946264510031269688119317 372481148907715766630593)
                  ·
                    rfl

theorem cell23_6528640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 6].length) (baseStart_6528640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528640 prefixEnd_6528640 := by exact prefixLift 6528640
  have htrace : WordTrace (prefixWord ++ tailWord_6528640) baseStart_6528640 baseEnd_6528640 := by
    simpa [prefixWord, tailWord_6528640, baseEnd_6528640] using wordTrace_append hprefix tailTrace_6528640
  have hstable : (prefixWord ++ tailWord_6528640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528640).length < 2 ^ (prefixWord ++ tailWord_6528640).sum := by decide
  have hdescent : baseEnd_6528640 < baseStart_6528640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528643 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 6]
def baseStart_6528643 : Nat := 118140960795 + 6528643 * 2 ^ 59
def prefixEnd_6528643 : Nat := 4983230072969 + 3 ^ 40 * 6528643 * 2
def baseEnd_6528643 : Nat := 3352331880611405387937823

theorem tailTrace_6528643 : CollatzResearch.WordTrace tailWord_6528643 prefixEnd_6528643 3352331880611405387937823 := by
  unfold tailWord_6528643
  simp only [CollatzResearch.WordTrace]
  refine ⟨238119172486848889299550583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158746114991232592866367055 238119172486848889299550583)
  ·
    refine ⟨357178758730273333949325875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238119172486848889299550583 357178758730273333949325875)
    ·
      refine ⟨535768138095410000923988813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357178758730273333949325875 535768138095410000923988813)
      ·
        refine ⟨200913051785778750346495805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 535768138095410000923988813 200913051785778750346495805)
        ·
          refine ⟨75342394419667031379935927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200913051785778750346495805 75342394419667031379935927)
          ·
            refine ⟨113013591629500547069903891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75342394419667031379935927 113013591629500547069903891)
            ·
              refine ⟨169520387444250820604855837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113013591629500547069903891 169520387444250820604855837)
              ·
                refine ⟨63570145291594057726820939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169520387444250820604855837 63570145291594057726820939)
                ·
                  refine ⟨95355217937391086590231409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63570145291594057726820939 95355217937391086590231409)
                  ·
                    refine ⟨71516413453043314942673557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95355217937391086590231409 71516413453043314942673557)
                    ·
                      refine ⟨3352331880611405387937823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71516413453043314942673557 3352331880611405387937823)
                      ·
                        rfl

theorem cell23_6528643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_6528643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528643 prefixEnd_6528643 := by exact prefixLift 6528643
  have htrace : WordTrace (prefixWord ++ tailWord_6528643) baseStart_6528643 baseEnd_6528643 := by
    simpa [prefixWord, tailWord_6528643, baseEnd_6528643] using wordTrace_append hprefix tailTrace_6528643
  have hstable : (prefixWord ++ tailWord_6528643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528643).length < 2 ^ (prefixWord ++ tailWord_6528643).sum := by decide
  have hdescent : baseEnd_6528643 < baseStart_6528643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528671 : List Nat := [1, 1, 2, 7, 1, 2, 1, 1, 2, 2, 3]
def baseStart_6528671 : Nat := 118140960795 + 6528671 * 2 ^ 59
def prefixEnd_6528671 : Nat := 4983230072969 + 3 ^ 40 * 6528671 * 2
def baseEnd_6528671 : Nat := 3352346258069731278387695

theorem tailTrace_6528671 : CollatzResearch.WordTrace tailWord_6528671 prefixEnd_6528671 3352346258069731278387695 := by
  unfold tailWord_6528671
  simp only [CollatzResearch.WordTrace]
  refine ⟨238120193730747450081569867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158746795820498300054379911 238120193730747450081569867)
  ·
    refine ⟨357180290596121175122354801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238120193730747450081569867 357180290596121175122354801)
    ·
      refine ⟨267885217947090881341766101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357180290596121175122354801 267885217947090881341766101)
      ·
        refine ⟨6278559795634942531447643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 267885217947090881341766101 6278559795634942531447643)
        ·
          refine ⟨9417839693452413797171465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6278559795634942531447643 9417839693452413797171465)
          ·
            refine ⟨7063379770089310347878599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9417839693452413797171465 7063379770089310347878599)
            ·
              refine ⟨10595069655133965521817899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7063379770089310347878599 10595069655133965521817899)
              ·
                refine ⟨15892604482700948282726849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10595069655133965521817899 15892604482700948282726849)
                ·
                  refine ⟨11919453362025711212045137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15892604482700948282726849 11919453362025711212045137)
                  ·
                    refine ⟨8939590021519283409033853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11919453362025711212045137 8939590021519283409033853)
                    ·
                      refine ⟨3352346258069731278387695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8939590021519283409033853 3352346258069731278387695)
                      ·
                        rfl

theorem cell23_6528671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_6528671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528671 prefixEnd_6528671 := by exact prefixLift 6528671
  have htrace : WordTrace (prefixWord ++ tailWord_6528671) baseStart_6528671 baseEnd_6528671 := by
    simpa [prefixWord, tailWord_6528671, baseEnd_6528671] using wordTrace_append hprefix tailTrace_6528671
  have hstable : (prefixWord ++ tailWord_6528671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528671).length < 2 ^ (prefixWord ++ tailWord_6528671).sum := by decide
  have hdescent : baseEnd_6528671 < baseStart_6528671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528720 : List Nat := [2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 4]
def baseStart_6528720 : Nat := 118140960795 + 6528720 * 2 ^ 59
def prefixEnd_6528720 : Nat := 4983230072969 + 3 ^ 40 * 6528720 * 2
def baseEnd_6528720 : Nat := 3352371418621801586674969

theorem tailTrace_6528720 : CollatzResearch.WordTrace tailWord_6528720 prefixEnd_6528720 3352371418621801586674969 := by
  unfold tailWord_6528720
  simp only [CollatzResearch.WordTrace]
  refine ⟨119060990453784965725051807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158747987271713287633402409 119060990453784965725051807)
  ·
    refine ⟨178591485680677448587577711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119060990453784965725051807 178591485680677448587577711)
    ·
      refine ⟨267887228521016172881366567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178591485680677448587577711 267887228521016172881366567)
      ·
        refine ⟨401830842781524259322049851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267887228521016172881366567 401830842781524259322049851)
        ·
          refine ⟨602746264172286388983074777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401830842781524259322049851 602746264172286388983074777)
          ·
            refine ⟨452059698129214791737306083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602746264172286388983074777 452059698129214791737306083)
            ·
              refine ⟨678089547193822187605959125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452059698129214791737306083 678089547193822187605959125)
              ·
                refine ⟨15892723762355207522014667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 678089547193822187605959125 15892723762355207522014667)
                ·
                  refine ⟨23839085643532811283022001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15892723762355207522014667 23839085643532811283022001)
                  ·
                    refine ⟨17879314232649608462266501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23839085643532811283022001 17879314232649608462266501)
                    ·
                      refine ⟨3352371418621801586674969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17879314232649608462266501 3352371418621801586674969)
                      ·
                        rfl

theorem cell23_6528720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 4].length) (baseStart_6528720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528720 prefixEnd_6528720 := by exact prefixLift 6528720
  have htrace : WordTrace (prefixWord ++ tailWord_6528720) baseStart_6528720 baseEnd_6528720 := by
    simpa [prefixWord, tailWord_6528720, baseEnd_6528720] using wordTrace_append hprefix tailTrace_6528720
  have hstable : (prefixWord ++ tailWord_6528720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528720).length < 2 ^ (prefixWord ++ tailWord_6528720).sum := by decide
  have hdescent : baseEnd_6528720 < baseStart_6528720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528724 : List Nat := [2, 4, 1, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_6528724 : Nat := 118140960795 + 6528724 * 2 ^ 59
def prefixEnd_6528724 : Nat := 4983230072969 + 3 ^ 40 * 6528724 * 2
def baseEnd_6528724 : Nat := 3352373472544419571024951

theorem tailTrace_6528724 : CollatzResearch.WordTrace tailWord_6528724 prefixEnd_6528724 3352373472544419571024951 := by
  unfold tailWord_6528724
  simp only [CollatzResearch.WordTrace]
  refine ⟨119061063399777720066624613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158748084533036960088832817 119061063399777720066624613)
  ·
    refine ⟨22323949387458322512492115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119061063399777720066624613 22323949387458322512492115)
    ·
      refine ⟨33485924081187483768738173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22323949387458322512492115 33485924081187483768738173)
      ·
        refine ⟨12557221530445306413276815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33485924081187483768738173 12557221530445306413276815)
        ·
          refine ⟨18835832295667959619915223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12557221530445306413276815 18835832295667959619915223)
          ·
            refine ⟨28253748443501939429872835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18835832295667959619915223 28253748443501939429872835)
            ·
              refine ⟨42380622665252909144809253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28253748443501939429872835 42380622665252909144809253)
              ·
                refine ⟨7946366749734920464651735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42380622665252909144809253 7946366749734920464651735)
                ·
                  refine ⟨11919550124602380696977603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7946366749734920464651735 11919550124602380696977603)
                  ·
                    refine ⟨17879325186903571045466405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11919550124602380696977603 17879325186903571045466405)
                    ·
                      refine ⟨3352373472544419571024951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17879325186903571045466405 3352373472544419571024951)
                      ·
                        rfl

theorem cell23_6528724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_6528724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528724 prefixEnd_6528724 := by exact prefixLift 6528724
  have htrace : WordTrace (prefixWord ++ tailWord_6528724) baseStart_6528724 baseEnd_6528724 := by
    simpa [prefixWord, tailWord_6528724, baseEnd_6528724] using wordTrace_append hprefix tailTrace_6528724
  have hstable : (prefixWord ++ tailWord_6528724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528724).length < 2 ^ (prefixWord ++ tailWord_6528724).sum := by decide
  have hdescent : baseEnd_6528724 < baseStart_6528724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528730 : List Nat := [3, 1, 1, 2, 2, 4, 1, 9]
def baseStart_6528730 : Nat := 118140960795 + 6528730 * 2 ^ 59
def prefixEnd_6528730 : Nat := 4983230072969 + 3 ^ 40 * 6528730 * 2
def baseEnd_6528730 : Nat := 124162094571420242501849

theorem tailTrace_6528730 : CollatzResearch.WordTrace tailWord_6528730 prefixEnd_6528730 124162094571420242501849 := by
  unfold tailWord_6528730
  simp only [CollatzResearch.WordTrace]
  refine ⟨59530586409383425789491911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158748230425022468771978429 59530586409383425789491911)
  ·
    refine ⟨89295879614075138684237867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59530586409383425789491911 89295879614075138684237867)
    ·
      refine ⟨133943819421112708026356801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89295879614075138684237867 133943819421112708026356801)
      ·
        refine ⟨100457864565834531019767601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133943819421112708026356801 100457864565834531019767601)
        ·
          refine ⟨75343398424375898264825701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100457864565834531019767601 75343398424375898264825701)
          ·
            refine ⟨14126887204570480924654819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75343398424375898264825701 14126887204570480924654819)
            ·
              refine ⟨21190330806855721386982229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14126887204570480924654819 21190330806855721386982229)
              ·
                refine ⟨124162094571420242501849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21190330806855721386982229 124162094571420242501849)
                ·
                  rfl

theorem cell23_6528730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 9].length) (baseStart_6528730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528730 prefixEnd_6528730 := by exact prefixLift 6528730
  have htrace : WordTrace (prefixWord ++ tailWord_6528730) baseStart_6528730 baseEnd_6528730 := by
    simpa [prefixWord, tailWord_6528730, baseEnd_6528730] using wordTrace_append hprefix tailTrace_6528730
  have hstable : (prefixWord ++ tailWord_6528730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528730).length < 2 ^ (prefixWord ++ tailWord_6528730).sum := by decide
  have hdescent : baseEnd_6528730 < baseStart_6528730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528744 : List Nat := [2, 1, 4, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_6528744 : Nat := 118140960795 + 6528744 * 2 ^ 59
def prefixEnd_6528744 : Nat := 4983230072969 + 3 ^ 40 * 6528744 * 2
def baseEnd_6528744 : Nat := 3352383742157509492774859

theorem tailTrace_6528744 : CollatzResearch.WordTrace tailWord_6528744 prefixEnd_6528744 3352383742157509492774859 := by
  unfold tailWord_6528744
  simp only [CollatzResearch.WordTrace]
  refine ⟨119061428129741491774488643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158748570839655322365984857 119061428129741491774488643)
  ·
    refine ⟨178592142194612237661732965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119061428129741491774488643 178592142194612237661732965)
    ·
      refine ⟨33486026661489794561574931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178592142194612237661732965 33486026661489794561574931)
      ·
        refine ⟨50229039992234691842362397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33486026661489794561574931 50229039992234691842362397)
        ·
          refine ⟨18835889997088009440885899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50229039992234691842362397 18835889997088009440885899)
          ·
            refine ⟨28253834995632014161328849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18835889997088009440885899 28253834995632014161328849)
            ·
              refine ⟨21190376246724010620996637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28253834995632014161328849 21190376246724010620996637)
              ·
                refine ⟨7946391092521503982873739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21190376246724010620996637 7946391092521503982873739)
                ·
                  refine ⟨11919586638782255974310609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7946391092521503982873739 11919586638782255974310609)
                  ·
                    refine ⟨8939689979086691980732957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11919586638782255974310609 8939689979086691980732957)
                    ·
                      refine ⟨3352383742157509492774859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8939689979086691980732957 3352383742157509492774859)
                      ·
                        rfl

theorem cell23_6528744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_6528744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528744 prefixEnd_6528744 := by exact prefixLift 6528744
  have htrace : WordTrace (prefixWord ++ tailWord_6528744) baseStart_6528744 baseEnd_6528744 := by
    simpa [prefixWord, tailWord_6528744, baseEnd_6528744] using wordTrace_append hprefix tailTrace_6528744
  have hstable : (prefixWord ++ tailWord_6528744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528744).length < 2 ^ (prefixWord ++ tailWord_6528744).sum := by decide
  have hdescent : baseEnd_6528744 < baseStart_6528744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528758 : List Nat := [5, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2]
def baseStart_6528758 : Nat := 118140960795 + 6528758 * 2 ^ 59
def prefixEnd_6528758 : Nat := 4983230072969 + 3 ^ 40 * 6528758 * 2
def baseEnd_6528758 : Nat := 3352390930886672437999795

theorem tailTrace_6528758 : CollatzResearch.WordTrace tailWord_6528758 prefixEnd_6528758 3352390930886672437999795 := by
  unfold tailWord_6528758
  simp only [CollatzResearch.WordTrace]
  refine ⟨14882710430089516496249183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158748911254288175959991285 14882710430089516496249183)
  ·
    refine ⟨22324065645134274744373775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14882710430089516496249183 22324065645134274744373775)
    ·
      refine ⟨33486098467701412116560663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22324065645134274744373775 33486098467701412116560663)
      ·
        refine ⟨50229147701552118174840995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33486098467701412116560663 50229147701552118174840995)
        ·
          refine ⟨75343721552328177262261493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50229147701552118174840995 75343721552328177262261493)
          ·
            refine ⟨7063473895530766618337015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75343721552328177262261493 7063473895530766618337015)
            ·
              refine ⟨10595210843296149927505523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7063473895530766618337015 10595210843296149927505523)
              ·
                refine ⟨15892816264944224891258285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10595210843296149927505523 15892816264944224891258285)
                ·
                  refine ⟨5959806099354084334221857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15892816264944224891258285 5959806099354084334221857)
                  ·
                    refine ⟨4469854574515563250666393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5959806099354084334221857 4469854574515563250666393)
                    ·
                      refine ⟨3352390930886672437999795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4469854574515563250666393 3352390930886672437999795)
                      ·
                        rfl

theorem cell23_6528758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_6528758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528758 prefixEnd_6528758 := by exact prefixLift 6528758
  have htrace : WordTrace (prefixWord ++ tailWord_6528758) baseStart_6528758 baseEnd_6528758 := by
    simpa [prefixWord, tailWord_6528758, baseEnd_6528758] using wordTrace_append hprefix tailTrace_6528758
  have hstable : (prefixWord ++ tailWord_6528758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528758).length < 2 ^ (prefixWord ++ tailWord_6528758).sum := by decide
  have hdescent : baseEnd_6528758 < baseStart_6528758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528788 : List Nat := [2, 4, 4, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_6528788 : Nat := 118140960795 + 6528788 * 2 ^ 59
def prefixEnd_6528788 : Nat := 4983230072969 + 3 ^ 40 * 6528788 * 2
def baseEnd_6528788 : Nat := 3352406335306307320624657

theorem tailTrace_6528788 : CollatzResearch.WordTrace tailWord_6528788 prefixEnd_6528788 3352406335306307320624657 := by
  unfold tailWord_6528788
  simp only [CollatzResearch.WordTrace]
  refine ⟨119062230535661789531789509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158749640714215719375719345 119062230535661789531789509)
  ·
    refine ⟨22324168225436585537210533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119062230535661789531789509 22324168225436585537210533)
    ·
      refine ⟨4185781542269359788226975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22324168225436585537210533 4185781542269359788226975)
      ·
        refine ⟨6278672313404039682340463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4185781542269359788226975 6278672313404039682340463)
        ·
          refine ⟨9418008470106059523510695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6278672313404039682340463 9418008470106059523510695)
          ·
            refine ⟨14127012705159089285266043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9418008470106059523510695 14127012705159089285266043)
            ·
              refine ⟨21190519057738633927899065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14127012705159089285266043 21190519057738633927899065)
              ·
                refine ⟨15892889293303975445924299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21190519057738633927899065 15892889293303975445924299)
                ·
                  refine ⟨23839333939955963168886449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15892889293303975445924299 23839333939955963168886449)
                  ·
                    refine ⟨17879500454966972376664837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23839333939955963168886449 17879500454966972376664837)
                    ·
                      refine ⟨3352406335306307320624657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17879500454966972376664837 3352406335306307320624657)
                      ·
                        rfl

theorem cell23_6528788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_6528788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528788 prefixEnd_6528788 := by exact prefixLift 6528788
  have htrace : WordTrace (prefixWord ++ tailWord_6528788) baseStart_6528788 baseEnd_6528788 := by
    simpa [prefixWord, tailWord_6528788, baseEnd_6528788] using wordTrace_append hprefix tailTrace_6528788
  have hstable : (prefixWord ++ tailWord_6528788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528788).length < 2 ^ (prefixWord ++ tailWord_6528788).sum := by decide
  have hdescent : baseEnd_6528788 < baseStart_6528788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528817 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 2, 4, 3]
def baseStart_6528817 : Nat := 118140960795 + 6528817 * 2 ^ 59
def prefixEnd_6528817 : Nat := 4983230072969 + 3 ^ 40 * 6528817 * 2
def baseEnd_6528817 : Nat := 3352421226245287707162023

theorem tailTrace_6528817 : CollatzResearch.WordTrace tailWord_6528817 prefixEnd_6528817 3352421226245287707162023 := by
  unfold tailWord_6528817
  simp only [CollatzResearch.WordTrace]
  refine ⟨238125518788218517016384705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158750345858812344677589803 238125518788218517016384705)
  ·
    refine ⟨178594139091163887762288529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238125518788218517016384705 178594139091163887762288529)
    ·
      refine ⟨133945604318372915821716397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178594139091163887762288529 133945604318372915821716397)
      ·
        refine ⟨50229601619389843433143649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133945604318372915821716397 50229601619389843433143649)
        ·
          refine ⟨37672201214542382574857737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50229601619389843433143649 37672201214542382574857737)
          ·
            refine ⟨28254150910906786931143303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37672201214542382574857737 28254150910906786931143303)
            ·
              refine ⟨42381226366360180396714955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28254150910906786931143303 42381226366360180396714955)
              ·
                refine ⟨63571839549540270595072433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42381226366360180396714955 63571839549540270595072433)
                ·
                  refine ⟨47678879662155202946304325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63571839549540270595072433 47678879662155202946304325)
                  ·
                    refine ⟨8939789936654100552432061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47678879662155202946304325 8939789936654100552432061)
                    ·
                      refine ⟨3352421226245287707162023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8939789936654100552432061 3352421226245287707162023)
                      ·
                        rfl

theorem cell23_6528817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_6528817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528817 prefixEnd_6528817 := by exact prefixLift 6528817
  have htrace : WordTrace (prefixWord ++ tailWord_6528817) baseStart_6528817 baseEnd_6528817 := by
    simpa [prefixWord, tailWord_6528817, baseEnd_6528817] using wordTrace_append hprefix tailTrace_6528817
  have hstable : (prefixWord ++ tailWord_6528817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528817).length < 2 ^ (prefixWord ++ tailWord_6528817).sum := by decide
  have hdescent : baseEnd_6528817 < baseStart_6528817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528831 : List Nat := [1, 1, 2, 2, 6, 1, 2, 1, 1, 4, 2]
def baseStart_6528831 : Nat := 118140960795 + 6528831 * 2 ^ 59
def prefixEnd_6528831 : Nat := 4983230072969 + 3 ^ 40 * 6528831 * 2
def baseEnd_6528831 : Nat := 3352428414974450652386959

theorem tailTrace_6528831 : CollatzResearch.WordTrace tailWord_6528831 prefixEnd_6528831 3352428414974450652386959 := by
  unfold tailWord_6528831
  simp only [CollatzResearch.WordTrace]
  refine ⟨238126029410167797407394347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158750686273445198271596231 238126029410167797407394347)
  ·
    refine ⟨357189044115251696111091521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238126029410167797407394347 357189044115251696111091521)
    ·
      refine ⟨267891783086438772083318641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357189044115251696111091521 267891783086438772083318641)
      ·
        refine ⟨200918837314829079062488981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267891783086438772083318641 200918837314829079062488981)
        ·
          refine ⟨9418070499132613081054171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 200918837314829079062488981 9418070499132613081054171)
          ·
            refine ⟨14127105748698919621581257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9418070499132613081054171 14127105748698919621581257)
            ·
              refine ⟨10595329311524189716185943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14127105748698919621581257 10595329311524189716185943)
              ·
                refine ⟨15892993967286284574278915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10595329311524189716185943 15892993967286284574278915)
                ·
                  refine ⟨23839490950929426861418373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15892993967286284574278915 23839490950929426861418373)
                  ·
                    refine ⟨4469904553299267536515945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23839490950929426861418373 4469904553299267536515945)
                    ·
                      refine ⟨3352428414974450652386959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4469904553299267536515945 3352428414974450652386959)
                      ·
                        rfl

theorem cell23_6528831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 4, 2].length) (baseStart_6528831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528831 prefixEnd_6528831 := by exact prefixLift 6528831
  have htrace : WordTrace (prefixWord ++ tailWord_6528831) baseStart_6528831 baseEnd_6528831 := by
    simpa [prefixWord, tailWord_6528831, baseEnd_6528831] using wordTrace_append hprefix tailTrace_6528831
  have hstable : (prefixWord ++ tailWord_6528831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528831).length < 2 ^ (prefixWord ++ tailWord_6528831).sum := by decide
  have hdescent : baseEnd_6528831 < baseStart_6528831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528877 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_6528877 : Nat := 118140960795 + 6528877 * 2 ^ 59
def prefixEnd_6528877 : Nat := 4983230072969 + 3 ^ 40 * 6528877 * 2
def baseEnd_6528877 : Nat := 3352452035084557472411747

theorem tailTrace_6528877 : CollatzResearch.WordTrace tailWord_6528877 prefixEnd_6528877 3352452035084557472411747 := by
  unfold tailWord_6528877
  simp only [CollatzResearch.WordTrace]
  refine ⟨238127707168001147263568885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158751804778667431509045923 238127707168001147263568885)
  ·
    refine ⟨22324472547000107555959583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 238127707168001147263568885 22324472547000107555959583)
    ·
      refine ⟨33486708820500161333939375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22324472547000107555959583 33486708820500161333939375)
      ·
        refine ⟨50230063230750242000909063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33486708820500161333939375 50230063230750242000909063)
        ·
          refine ⟨75345094846125363001363595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50230063230750242000909063 75345094846125363001363595)
          ·
            refine ⟨113017642269188044502045393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75345094846125363001363595 113017642269188044502045393)
            ·
              refine ⟨84763231701891033376534045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113017642269188044502045393 84763231701891033376534045)
              ·
                refine ⟨31786211888209137516200267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84763231701891033376534045 31786211888209137516200267)
                ·
                  refine ⟨47679317832313706274300401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31786211888209137516200267 47679317832313706274300401)
                  ·
                    refine ⟨35759488374235279705725301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47679317832313706274300401 35759488374235279705725301)
                    ·
                      refine ⟨3352452035084557472411747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35759488374235279705725301 3352452035084557472411747)
                      ·
                        rfl

theorem cell23_6528877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_6528877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528877 prefixEnd_6528877 := by exact prefixLift 6528877
  have htrace : WordTrace (prefixWord ++ tailWord_6528877) baseStart_6528877 baseEnd_6528877 := by
    simpa [prefixWord, tailWord_6528877, baseEnd_6528877] using wordTrace_append hprefix tailTrace_6528877
  have hstable : (prefixWord ++ tailWord_6528877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528877).length < 2 ^ (prefixWord ++ tailWord_6528877).sum := by decide
  have hdescent : baseEnd_6528877 < baseStart_6528877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6528937 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 2, 5, 3]
def baseStart_6528937 : Nat := 118140960795 + 6528937 * 2 ^ 59
def prefixEnd_6528937 : Nat := 4983230072969 + 3 ^ 40 * 6528937 * 2
def baseEnd_6528937 : Nat := 3352482843923827237661471

theorem tailTrace_6528937 : CollatzResearch.WordTrace tailWord_6528937 prefixEnd_6528937 3352482843923827237661471 := by
  unfold tailWord_6528937
  simp only [CollatzResearch.WordTrace]
  refine ⟨238129895547783777510753065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158753263698522518340502043 238129895547783777510753065)
  ·
    refine ⟨178597421660837833133064799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238129895547783777510753065 178597421660837833133064799)
    ·
      refine ⟨267896132491256749699597199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178597421660837833133064799 267896132491256749699597199)
      ·
        refine ⟨401844198736885124549395799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267896132491256749699597199 401844198736885124549395799)
        ·
          refine ⟨602766298105327686824093699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401844198736885124549395799 602766298105327686824093699)
          ·
            refine ⟨904149447157991530236140549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602766298105327686824093699 904149447157991530236140549)
            ·
              refine ⟨169528021342123411919276353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 904149447157991530236140549 169528021342123411919276353)
              ·
                refine ⟨127146016006592558939457265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169528021342123411919276353 127146016006592558939457265)
                ·
                  refine ⟨95359512004944419204592949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127146016006592558939457265 95359512004944419204592949)
                  ·
                    refine ⟨8939954250463539300430589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95359512004944419204592949 8939954250463539300430589)
                    ·
                      refine ⟨3352482843923827237661471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8939954250463539300430589 3352482843923827237661471)
                      ·
                        rfl

theorem cell23_6528937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 5, 3].length) (baseStart_6528937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6528937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6528937 prefixEnd_6528937 := by exact prefixLift 6528937
  have htrace : WordTrace (prefixWord ++ tailWord_6528937) baseStart_6528937 baseEnd_6528937 := by
    simpa [prefixWord, tailWord_6528937, baseEnd_6528937] using wordTrace_append hprefix tailTrace_6528937
  have hstable : (prefixWord ++ tailWord_6528937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6528937).length < 2 ^ (prefixWord ++ tailWord_6528937).sum := by decide
  have hdescent : baseEnd_6528937 < baseStart_6528937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6528937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529005 : List Nat := [1, 5, 1, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_6529005 : Nat := 118140960795 + 6529005 * 2 ^ 59
def prefixEnd_6529005 : Nat := 4983230072969 + 3 ^ 40 * 6529005 * 2
def baseEnd_6529005 : Nat := 3352517760608332971611159

theorem tailTrace_6529005 : CollatzResearch.WordTrace tailWord_6529005 prefixEnd_6529005 3352517760608332971611159 := by
  unfold tailWord_6529005
  simp only [CollatzResearch.WordTrace]
  refine ⟨238132375711537425124228469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158754917141024950082818979 238132375711537425124228469)
  ·
    refine ⟨22324910222956633605396419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 238132375711537425124228469 22324910222956633605396419)
    ·
      refine ⟨33487365334434950408094629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22324910222956633605396419 33487365334434950408094629)
      ·
        refine ⟨6278881000206553201517743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33487365334434950408094629 6278881000206553201517743)
        ·
          refine ⟨9418321500309829802276615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6278881000206553201517743 9418321500309829802276615)
          ·
            refine ⟨14127482250464744703414923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9418321500309829802276615 14127482250464744703414923)
            ·
              refine ⟨21191223375697117055122385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14127482250464744703414923 21191223375697117055122385)
              ·
                refine ⟨15893417531772837791341789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21191223375697117055122385 15893417531772837791341789)
                ·
                  refine ⟨5960031574414814171753171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15893417531772837791341789 5960031574414814171753171)
                  ·
                    refine ⟨8940047361622221257629757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5960031574414814171753171 8940047361622221257629757)
                    ·
                      refine ⟨3352517760608332971611159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8940047361622221257629757 3352517760608332971611159)
                      ·
                        rfl

theorem cell23_6529005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_6529005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529005 prefixEnd_6529005 := by exact prefixLift 6529005
  have htrace : WordTrace (prefixWord ++ tailWord_6529005) baseStart_6529005 baseEnd_6529005 := by
    simpa [prefixWord, tailWord_6529005, baseEnd_6529005] using wordTrace_append hprefix tailTrace_6529005
  have hstable : (prefixWord ++ tailWord_6529005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529005).length < 2 ^ (prefixWord ++ tailWord_6529005).sum := by decide
  have hdescent : baseEnd_6529005 < baseStart_6529005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529022 : List Nat := [4, 2, 2, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_6529022 : Nat := 118140960795 + 6529022 * 2 ^ 59
def prefixEnd_6529022 : Nat := 4983230072969 + 3 ^ 40 * 6529022 * 2
def baseEnd_6529022 : Nat := 3352526489779459405098581

theorem tailTrace_6529022 : CollatzResearch.WordTrace tailWord_6529022 prefixEnd_6529022 3352526489779459405098581 := by
  unfold tailWord_6529022
  simp only [CollatzResearch.WordTrace]
  refine ⟨29766624469059479628449665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158755330501650558018398213 29766624469059479628449665)
  ·
    refine ⟨22324968351794609721337249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29766624469059479628449665 22324968351794609721337249)
    ·
      refine ⟨16743726263845957291002937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22324968351794609721337249 16743726263845957291002937)
      ·
        refine ⟨12557794697884467968252203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16743726263845957291002937 12557794697884467968252203)
        ·
          refine ⟨18836692046826701952378305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12557794697884467968252203 18836692046826701952378305)
          ·
            refine ⟨14127519035120026464283729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18836692046826701952378305 14127519035120026464283729)
            ·
              refine ⟨10595639276340019848212797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14127519035120026464283729 10595639276340019848212797)
              ·
                refine ⟨3973364728627507443079799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10595639276340019848212797 3973364728627507443079799)
                ·
                  refine ⟨5960047092941261164619699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3973364728627507443079799 5960047092941261164619699)
                  ·
                    refine ⟨8940070639411891746929549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5960047092941261164619699 8940070639411891746929549)
                    ·
                      refine ⟨3352526489779459405098581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8940070639411891746929549 3352526489779459405098581)
                      ·
                        rfl

theorem cell23_6529022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_6529022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529022 prefixEnd_6529022 := by exact prefixLift 6529022
  have htrace : WordTrace (prefixWord ++ tailWord_6529022) baseStart_6529022 baseEnd_6529022 := by
    simpa [prefixWord, tailWord_6529022, baseEnd_6529022] using wordTrace_append hprefix tailTrace_6529022
  have hstable : (prefixWord ++ tailWord_6529022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529022).length < 2 ^ (prefixWord ++ tailWord_6529022).sum := by decide
  have hdescent : baseEnd_6529022 < baseStart_6529022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529034 : List Nat := [3, 1, 2, 2, 4, 1, 10]
def baseStart_6529034 : Nat := 118140960795 + 6529034 * 2 ^ 59
def prefixEnd_6529034 : Nat := 4983230072969 + 3 ^ 40 * 6529034 * 2
def baseEnd_6529034 : Nat := 41389291994411276026525

theorem tailTrace_6529034 : CollatzResearch.WordTrace tailWord_6529034 prefixEnd_6529034 41389291994411276026525 := by
  unfold tailWord_6529034
  simp only [CollatzResearch.WordTrace]
  refine ⟨59533358357108090769258539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158755622285621575384689437 59533358357108090769258539)
  ·
    refine ⟨89300037535662136153887809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59533358357108090769258539 89300037535662136153887809)
    ·
      refine ⟨66975028151746602115415857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89300037535662136153887809 66975028151746602115415857)
      ·
        refine ⟨50231271113809951586561893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66975028151746602115415857 50231271113809951586561893)
        ·
          refine ⟨9418363333839365922480355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50231271113809951586561893 9418363333839365922480355)
          ·
            refine ⟨14127545000759048883720533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9418363333839365922480355 14127545000759048883720533)
            ·
              refine ⟨41389291994411276026525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14127545000759048883720533 41389291994411276026525)
              ·
                rfl

theorem cell23_6529034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 10].length) (baseStart_6529034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529034 prefixEnd_6529034 := by exact prefixLift 6529034
  have htrace : WordTrace (prefixWord ++ tailWord_6529034) baseStart_6529034 baseEnd_6529034 := by
    simpa [prefixWord, tailWord_6529034, baseEnd_6529034] using wordTrace_append hprefix tailTrace_6529034
  have hstable : (prefixWord ++ tailWord_6529034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529034).length < 2 ^ (prefixWord ++ tailWord_6529034).sum := by decide
  have hdescent : baseEnd_6529034 < baseStart_6529034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529045 : List Nat := [1, 3, 2, 1, 5, 1, 2, 1, 3, 2, 2]
def baseStart_6529045 : Nat := 118140960795 + 6529045 * 2 ^ 59
def prefixEnd_6529045 : Nat := 4983230072969 + 3 ^ 40 * 6529045 * 2
def baseEnd_6529045 : Nat := 3352538299834512815110975

theorem tailTrace_6529045 : CollatzResearch.WordTrace tailWord_6529045 prefixEnd_6529045 3352538299834512815110975 := by
  unfold tailWord_6529045
  simp only [CollatzResearch.WordTrace]
  refine ⟨238133834631392511955684589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158755889754261674637123059 238133834631392511955684589)
  ·
    refine ⟨89300187986772191983381721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238133834631392511955684589 89300187986772191983381721)
    ·
      refine ⟨66975140990079143987536291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89300187986772191983381721 66975140990079143987536291)
      ·
        refine ⟨100462711485118715981304437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66975140990079143987536291 100462711485118715981304437)
        ·
          refine ⟨9418379201729879623247291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100462711485118715981304437 9418379201729879623247291)
          ·
            refine ⟨14127568802594819434870937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9418379201729879623247291 14127568802594819434870937)
            ·
              refine ⟨10595676601946114576153203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14127568802594819434870937 10595676601946114576153203)
              ·
                refine ⟨15893514902919171864229805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10595676601946114576153203 15893514902919171864229805)
                ·
                  refine ⟨5960068088594689449086177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15893514902919171864229805 5960068088594689449086177)
                  ·
                    refine ⟨4470051066446017086814633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5960068088594689449086177 4470051066446017086814633)
                    ·
                      refine ⟨3352538299834512815110975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4470051066446017086814633 3352538299834512815110975)
                      ·
                        rfl

theorem cell23_6529045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_6529045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529045 prefixEnd_6529045 := by exact prefixLift 6529045
  have htrace : WordTrace (prefixWord ++ tailWord_6529045) baseStart_6529045 baseEnd_6529045 := by
    simpa [prefixWord, tailWord_6529045, baseEnd_6529045] using wordTrace_append hprefix tailTrace_6529045
  have hstable : (prefixWord ++ tailWord_6529045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529045).length < 2 ^ (prefixWord ++ tailWord_6529045).sum := by decide
  have hdescent : baseEnd_6529045 < baseStart_6529045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529061 : List Nat := [1, 3, 1, 2, 2, 3, 3, 1, 1, 3, 3]
def baseStart_6529061 : Nat := 118140960795 + 6529061 * 2 ^ 59
def prefixEnd_6529061 : Nat := 4983230072969 + 3 ^ 40 * 6529061 * 2
def baseEnd_6529061 : Nat := 3352546515524984752510901

theorem tailTrace_6529061 : CollatzResearch.WordTrace tailWord_6529061 prefixEnd_6529061 3352546515524984752510901 := by
  unfold tailWord_6529061
  simp only [CollatzResearch.WordTrace]
  refine ⟨238134418199334546688267037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158756278799556364458844691 238134418199334546688267037)
  ·
    refine ⟨89300406824750455008100139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238134418199334546688267037 89300406824750455008100139)
    ·
      refine ⟨133950610237125682512150209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89300406824750455008100139 133950610237125682512150209)
      ·
        refine ⟨100462957677844261884112657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133950610237125682512150209 100462957677844261884112657)
        ·
          refine ⟨75347218258383196413084493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100462957677844261884112657 75347218258383196413084493)
          ·
            refine ⟨28255206846893698654906685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75347218258383196413084493 28255206846893698654906685)
            ·
              refine ⟨10595702567585136995590007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28255206846893698654906685 10595702567585136995590007)
              ·
                refine ⟨15893553851377705493385011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10595702567585136995590007 15893553851377705493385011)
                ·
                  refine ⟨23840330777066558240077517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15893553851377705493385011 23840330777066558240077517)
                  ·
                    refine ⟨8940124041399959340029069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23840330777066558240077517 8940124041399959340029069)
                    ·
                      refine ⟨3352546515524984752510901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8940124041399959340029069 3352546515524984752510901)
                      ·
                        rfl

theorem cell23_6529061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_6529061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529061 prefixEnd_6529061 := by exact prefixLift 6529061
  have htrace : WordTrace (prefixWord ++ tailWord_6529061) baseStart_6529061 baseEnd_6529061 := by
    simpa [prefixWord, tailWord_6529061, baseEnd_6529061] using wordTrace_append hprefix tailTrace_6529061
  have hstable : (prefixWord ++ tailWord_6529061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529061).length < 2 ^ (prefixWord ++ tailWord_6529061).sum := by decide
  have hdescent : baseEnd_6529061 < baseStart_6529061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529067 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 8]
def baseStart_6529067 : Nat := 118140960795 + 6529067 * 2 ^ 59
def prefixEnd_6529067 : Nat := 4983230072969 + 3 ^ 40 * 6529067 * 2
def baseEnd_6529067 : Nat := 3352549596408911729035873

theorem tailTrace_6529067 : CollatzResearch.WordTrace tailWord_6529067 prefixEnd_6529067 3352549596408911729035873 := by
  unfold tailWord_6529067
  simp only [CollatzResearch.WordTrace]
  refine ⟨238134637037312809712985455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158756424691541873141990303 238134637037312809712985455)
  ·
    refine ⟨357201955555969214569478183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238134637037312809712985455 357201955555969214569478183)
    ·
      refine ⟨535802933333953821854217275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357201955555969214569478183 535802933333953821854217275)
      ·
        refine ⟨803704400000930732781325913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535802933333953821854217275 803704400000930732781325913)
        ·
          refine ⟨602778300000698049585994435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 803704400000930732781325913 602778300000698049585994435)
          ·
            refine ⟨904167450001047074378991653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602778300000698049585994435 904167450001047074378991653)
            ·
              refine ⟨169531396875196326446060935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 904167450001047074378991653 169531396875196326446060935)
              ·
                refine ⟨254297095312794489669091403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169531396875196326446060935 254297095312794489669091403)
                ·
                  refine ⟨381445642969191734503637105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254297095312794489669091403 381445642969191734503637105)
                  ·
                    refine ⟨286084232226893800877727829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 381445642969191734503637105 286084232226893800877727829)
                    ·
                      refine ⟨3352549596408911729035873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 286084232226893800877727829 3352549596408911729035873)
                      ·
                        rfl

theorem cell23_6529067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 8].length) (baseStart_6529067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529067 prefixEnd_6529067 := by exact prefixLift 6529067
  have htrace : WordTrace (prefixWord ++ tailWord_6529067) baseStart_6529067 baseEnd_6529067 := by
    simpa [prefixWord, tailWord_6529067, baseEnd_6529067] using wordTrace_append hprefix tailTrace_6529067
  have hstable : (prefixWord ++ tailWord_6529067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529067).length < 2 ^ (prefixWord ++ tailWord_6529067).sum := by decide
  have hdescent : baseEnd_6529067 < baseStart_6529067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529074 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_6529074 : Nat := 118140960795 + 6529074 * 2 ^ 59
def prefixEnd_6529074 : Nat := 4983230072969 + 3 ^ 40 * 6529074 * 2
def baseEnd_6529074 : Nat := 3352553190773493201648341

theorem tailTrace_6529074 : CollatzResearch.WordTrace tailWord_6529074 prefixEnd_6529074 3352553190773493201648341 := by
  unfold tailWord_6529074
  simp only [CollatzResearch.WordTrace]
  refine ⟨59533723087071862477122569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158756594898858299938993517 59533723087071862477122569)
  ·
    refine ⟨44650292315303896857841927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59533723087071862477122569 44650292315303896857841927)
    ·
      refine ⟨66975438472955845286762891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44650292315303896857841927 66975438472955845286762891)
      ·
        refine ⟨100463157709433767930144337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66975438472955845286762891 100463157709433767930144337)
        ·
          refine ⟨75347368282075325947608253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100463157709433767930144337 75347368282075325947608253)
          ·
            refine ⟨28255263105778247230353095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75347368282075325947608253 28255263105778247230353095)
            ·
              refine ⟨42382894658667370845529643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28255263105778247230353095 42382894658667370845529643)
              ·
                refine ⟨63574341988001056268294465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42382894658667370845529643 63574341988001056268294465)
                ·
                  refine ⟨47680756491000792201220849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63574341988001056268294465 47680756491000792201220849)
                  ·
                    refine ⟨35760567368250594150915637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47680756491000792201220849 35760567368250594150915637)
                    ·
                      refine ⟨3352553190773493201648341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35760567368250594150915637 3352553190773493201648341)
                      ·
                        rfl

theorem cell23_6529074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_6529074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529074 prefixEnd_6529074 := by exact prefixLift 6529074
  have htrace : WordTrace (prefixWord ++ tailWord_6529074) baseStart_6529074 baseEnd_6529074 := by
    simpa [prefixWord, tailWord_6529074, baseEnd_6529074] using wordTrace_append hprefix tailTrace_6529074
  have hstable : (prefixWord ++ tailWord_6529074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529074).length < 2 ^ (prefixWord ++ tailWord_6529074).sum := by decide
  have hdescent : baseEnd_6529074 < baseStart_6529074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529078 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_6529078 : Nat := 118140960795 + 6529078 * 2 ^ 59
def prefixEnd_6529078 : Nat := 4983230072969 + 3 ^ 40 * 6529078 * 2
def baseEnd_6529078 : Nat := 3352555244696111185998323

theorem tailTrace_6529078 : CollatzResearch.WordTrace tailWord_6529078 prefixEnd_6529078 3352555244696111185998323 := by
  unfold tailWord_6529078
  simp only [CollatzResearch.WordTrace]
  refine ⟨14883439890017059911977243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158756692160181972394423925 14883439890017059911977243)
  ·
    refine ⟨22325159835025589867965865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14883439890017059911977243 22325159835025589867965865)
    ·
      refine ⟨16743869876269192400974399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22325159835025589867965865 16743869876269192400974399)
      ·
        refine ⟨25115804814403788601461599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16743869876269192400974399 25115804814403788601461599)
        ·
          refine ⟨37673707221605682902192399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25115804814403788601461599 37673707221605682902192399)
          ·
            refine ⟨56510560832408524353288599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37673707221605682902192399 56510560832408524353288599)
            ·
              refine ⟨84765841248612786529932899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56510560832408524353288599 84765841248612786529932899)
              ·
                refine ⟨127148761872919179794899349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84765841248612786529932899 127148761872919179794899349)
                ·
                  refine ⟨5960098212793086552885907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127148761872919179794899349 5960098212793086552885907)
                  ·
                    refine ⟨8940147319189629829328861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5960098212793086552885907 8940147319189629829328861)
                    ·
                      refine ⟨3352555244696111185998323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8940147319189629829328861 3352555244696111185998323)
                      ·
                        rfl

theorem cell23_6529078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_6529078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529078 prefixEnd_6529078 := by exact prefixLift 6529078
  have htrace : WordTrace (prefixWord ++ tailWord_6529078) baseStart_6529078 baseEnd_6529078 := by
    simpa [prefixWord, tailWord_6529078, baseEnd_6529078] using wordTrace_append hprefix tailTrace_6529078
  have hstable : (prefixWord ++ tailWord_6529078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529078).length < 2 ^ (prefixWord ++ tailWord_6529078).sum := by decide
  have hdescent : baseEnd_6529078 < baseStart_6529078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529088 : List Nat := [2, 1, 1, 2, 2, 4, 2, 3, 1, 3, 2]
def baseStart_6529088 : Nat := 118140960795 + 6529088 * 2 ^ 59
def prefixEnd_6529088 : Nat := 4983230072969 + 3 ^ 40 * 6529088 * 2
def baseEnd_6529088 : Nat := 3352560379502656146873277

theorem tailTrace_6529088 : CollatzResearch.WordTrace tailWord_6529088 prefixEnd_6529088 3352560379502656146873277 := by
  unfold tailWord_6529088
  simp only [CollatzResearch.WordTrace]
  refine ⟨119067701485118365149749959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158756935313491153532999945 119067701485118365149749959)
  ·
    refine ⟨178601552227677547724624939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119067701485118365149749959 178601552227677547724624939)
    ·
      refine ⟨267902328341516321586937409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178601552227677547724624939 267902328341516321586937409)
      ·
        refine ⟨200926746256137241190203057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267902328341516321586937409 200926746256137241190203057)
        ·
          refine ⟨150695059692102930892652293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200926746256137241190203057 150695059692102930892652293)
          ·
            refine ⟨28255323692269299542372305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150695059692102930892652293 28255323692269299542372305)
            ·
              refine ⟨21191492769201974656779229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28255323692269299542372305 21191492769201974656779229)
              ·
                refine ⟨7946809788450740496292211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21191492769201974656779229 7946809788450740496292211)
                ·
                  refine ⟨11920214682676110744438317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7946809788450740496292211 11920214682676110744438317)
                  ·
                    refine ⟨4470080506003541529164369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11920214682676110744438317 4470080506003541529164369)
                    ·
                      refine ⟨3352560379502656146873277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4470080506003541529164369 3352560379502656146873277)
                      ·
                        rfl

theorem cell23_6529088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 1, 3, 2].length) (baseStart_6529088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529088 prefixEnd_6529088 := by exact prefixLift 6529088
  have htrace : WordTrace (prefixWord ++ tailWord_6529088) baseStart_6529088 baseEnd_6529088 := by
    simpa [prefixWord, tailWord_6529088, baseEnd_6529088] using wordTrace_append hprefix tailTrace_6529088
  have hstable : (prefixWord ++ tailWord_6529088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529088).length < 2 ^ (prefixWord ++ tailWord_6529088).sum := by decide
  have hdescent : baseEnd_6529088 < baseStart_6529088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529101 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_6529101 : Nat := 118140960795 + 6529101 * 2 ^ 59
def prefixEnd_6529101 : Nat := 4983230072969 + 3 ^ 40 * 6529101 * 2
def baseEnd_6529101 : Nat := 3352567054751164596010717

theorem tailTrace_6529101 : CollatzResearch.WordTrace tailWord_6529101 prefixEnd_6529101 3352567054751164596010717 := by
  unfold tailWord_6529101
  simp only [CollatzResearch.WordTrace]
  refine ⟨238135877119189633519723157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158757251412793089013148771 238135877119189633519723157)
  ·
    refine ⟨11162619239962014071237023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 238135877119189633519723157 11162619239962014071237023)
    ·
      refine ⟨16743928859943021106855535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11162619239962014071237023 16743928859943021106855535)
      ·
        refine ⟨25115893289914531660283303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16743928859943021106855535 25115893289914531660283303)
        ·
          refine ⟨37673839934871797490424955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25115893289914531660283303 37673839934871797490424955)
          ·
            refine ⟨56510759902307696235637433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37673839934871797490424955 56510759902307696235637433)
            ·
              refine ⟨42383069926730772176728075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56510759902307696235637433 42383069926730772176728075)
              ·
                refine ⟨63574604890096158265092113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42383069926730772176728075 63574604890096158265092113)
                ·
                  refine ⟨47680953667572118698819085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63574604890096158265092113 47680953667572118698819085)
                  ·
                    refine ⟨17880357625339544512057157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47680953667572118698819085 17880357625339544512057157)
                    ·
                      refine ⟨3352567054751164596010717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17880357625339544512057157 3352567054751164596010717)
                      ·
                        rfl

theorem cell23_6529101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_6529101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529101 prefixEnd_6529101 := by exact prefixLift 6529101
  have htrace : WordTrace (prefixWord ++ tailWord_6529101) baseStart_6529101 baseEnd_6529101 := by
    simpa [prefixWord, tailWord_6529101, baseEnd_6529101] using wordTrace_append hprefix tailTrace_6529101
  have hstable : (prefixWord ++ tailWord_6529101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529101).length < 2 ^ (prefixWord ++ tailWord_6529101).sum := by decide
  have hdescent : baseEnd_6529101 < baseStart_6529101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529114 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4]
def baseStart_6529114 : Nat := 118140960795 + 6529114 * 2 ^ 59
def prefixEnd_6529114 : Nat := 4983230072969 + 3 ^ 40 * 6529114 * 2
def baseEnd_6529114 : Nat := 3352573729999673045148157

theorem tailTrace_6529114 : CollatzResearch.WordTrace tailWord_6529114 prefixEnd_6529114 3352573729999673045148157 := by
  unfold tailWord_6529114
  simp only [CollatzResearch.WordTrace]
  refine ⟨59534087817035634184986599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158757567512095024493297597 59534087817035634184986599)
  ·
    refine ⟨89301131725553451277479899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59534087817035634184986599 89301131725553451277479899)
    ·
      refine ⟨133951697588330176916219849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89301131725553451277479899 133951697588330176916219849)
      ·
        refine ⟨100463773191247632687164887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133951697588330176916219849 100463773191247632687164887)
        ·
          refine ⟨150695659786871449030747331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100463773191247632687164887 150695659786871449030747331)
          ·
            refine ⟨226043489680307173546120997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150695659786871449030747331 226043489680307173546120997)
            ·
              refine ⟨42383154315057595039897687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226043489680307173546120997 42383154315057595039897687)
              ·
                refine ⟨63574731472586392559846531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42383154315057595039897687 63574731472586392559846531)
                ·
                  refine ⟨95362097208879588839769797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63574731472586392559846531 95362097208879588839769797)
                  ·
                    refine ⟨17880393226664922907456837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95362097208879588839769797 17880393226664922907456837)
                    ·
                      refine ⟨3352573729999673045148157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17880393226664922907456837 3352573729999673045148157)
                      ·
                        rfl

theorem cell23_6529114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_6529114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529114 prefixEnd_6529114 := by exact prefixLift 6529114
  have htrace : WordTrace (prefixWord ++ tailWord_6529114) baseStart_6529114 baseEnd_6529114 := by
    simpa [prefixWord, tailWord_6529114, baseEnd_6529114] using wordTrace_append hprefix tailTrace_6529114
  have hstable : (prefixWord ++ tailWord_6529114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529114).length < 2 ^ (prefixWord ++ tailWord_6529114).sum := by decide
  have hdescent : baseEnd_6529114 < baseStart_6529114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529124 : List Nat := [2, 3, 1, 1, 2, 1, 2, 4, 7]
def baseStart_6529124 : Nat := 118140960795 + 6529124 * 2 ^ 59
def prefixEnd_6529124 : Nat := 4983230072969 + 3 ^ 40 * 6529124 * 2
def baseEnd_6529124 : Nat := 372508762756246445113679

theorem tailTrace_6529124 : CollatzResearch.WordTrace tailWord_6529124 prefixEnd_6529124 372508762756246445113679 := by
  unfold tailWord_6529124
  simp only [CollatzResearch.WordTrace]
  refine ⟨119068357999053154223905213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158757810665404205631873617 119068357999053154223905213)
  ·
    refine ⟨44650634249644932833964455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119068357999053154223905213 44650634249644932833964455)
    ·
      refine ⟨66975951374467399250946683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44650634249644932833964455 66975951374467399250946683)
      ·
        refine ⟨100463927061701098876420025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66975951374467399250946683 100463927061701098876420025)
        ·
          refine ⟨75347945296275824157315019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100463927061701098876420025 75347945296275824157315019)
          ·
            refine ⟨113021917944413736235972529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75347945296275824157315019 113021917944413736235972529)
            ·
              refine ⟨84766438458310302176979397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113021917944413736235972529 84766438458310302176979397)
              ·
                refine ⟨15893707210933181658183637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84766438458310302176979397 15893707210933181658183637)
                ·
                  refine ⟨372508762756246445113679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15893707210933181658183637 372508762756246445113679)
                  ·
                    rfl

theorem cell23_6529124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_6529124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529124 prefixEnd_6529124 := by exact prefixLift 6529124
  have htrace : WordTrace (prefixWord ++ tailWord_6529124) baseStart_6529124 baseEnd_6529124 := by
    simpa [prefixWord, tailWord_6529124, baseEnd_6529124] using wordTrace_append hprefix tailTrace_6529124
  have hstable : (prefixWord ++ tailWord_6529124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529124).length < 2 ^ (prefixWord ++ tailWord_6529124).sum := by decide
  have hdescent : baseEnd_6529124 < baseStart_6529124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529161 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 1, 7, 2]
def baseStart_6529161 : Nat := 118140960795 + 6529161 * 2 ^ 59
def prefixEnd_6529161 : Nat := 4983230072969 + 3 ^ 40 * 6529161 * 2
def baseEnd_6529161 : Nat := 3352597863590434361260441

theorem tailTrace_6529161 : CollatzResearch.WordTrace tailWord_6529161 prefixEnd_6529161 3352597863590434361260441 := by
  unfold tailWord_6529161
  simp only [CollatzResearch.WordTrace]
  refine ⟨238138065498972263766907337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158758710332648175844604891 238138065498972263766907337)
  ·
    refine ⟨178603549124229197825180503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238138065498972263766907337 178603549124229197825180503)
    ·
      refine ⟨267905323686343796737770755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178603549124229197825180503 267905323686343796737770755)
      ·
        refine ⟨401857985529515695106656133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267905323686343796737770755 401857985529515695106656133)
        ·
          refine ⟨75348372286784192832498025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 401857985529515695106656133 75348372286784192832498025)
          ·
            refine ⟨56511279215088144624373519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75348372286784192832498025 56511279215088144624373519)
            ·
              refine ⟨84766918822632216936560279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56511279215088144624373519 84766918822632216936560279)
              ·
                refine ⟨127150378233948325404840419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84766918822632216936560279 127150378233948325404840419)
                ·
                  refine ⟨190725567350922488107260629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127150378233948325404840419 190725567350922488107260629)
                  ·
                    refine ⟨4470130484787245815013921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 190725567350922488107260629 4470130484787245815013921)
                    ·
                      refine ⟨3352597863590434361260441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4470130484787245815013921 3352597863590434361260441)
                      ·
                        rfl

theorem cell23_6529161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 7, 2].length) (baseStart_6529161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529161 prefixEnd_6529161 := by exact prefixLift 6529161
  have htrace : WordTrace (prefixWord ++ tailWord_6529161) baseStart_6529161 baseEnd_6529161 := by
    simpa [prefixWord, tailWord_6529161, baseEnd_6529161] using wordTrace_append hprefix tailTrace_6529161
  have hstable : (prefixWord ++ tailWord_6529161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529161).length < 2 ^ (prefixWord ++ tailWord_6529161).sum := by decide
  have hdescent : baseEnd_6529161 < baseStart_6529161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529211 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 3]
def baseStart_6529211 : Nat := 118140960795 + 6529211 * 2 ^ 59
def prefixEnd_6529211 : Nat := 4983230072969 + 3 ^ 40 * 6529211 * 2
def baseEnd_6529211 : Nat := 3352623537623159165635211

theorem tailTrace_6529211 : CollatzResearch.WordTrace tailWord_6529211 prefixEnd_6529211 3352623537623159165635211 := by
  unfold tailWord_6529211
  simp only [CollatzResearch.WordTrace]
  refine ⟨238139889148791122306227487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158759926099194081537484991 238139889148791122306227487)
  ·
    refine ⟨357209833723186683459341231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238139889148791122306227487 357209833723186683459341231)
    ·
      refine ⟨535814750584780025189011847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357209833723186683459341231 535814750584780025189011847)
      ·
        refine ⟨803722125877170037783517771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535814750584780025189011847 803722125877170037783517771)
        ·
          refine ⟨1205583188815755056675276657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 803722125877170037783517771 1205583188815755056675276657)
          ·
            refine ⟨904187391611816292506457493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1205583188815755056675276657 904187391611816292506457493)
            ·
              refine ⟨42383783981803888711240195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 904187391611816292506457493 42383783981803888711240195)
              ·
                refine ⟨63575675972705833066860293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42383783981803888711240195 63575675972705833066860293)
                ·
                  refine ⟨11920439244882343700036305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63575675972705833066860293 11920439244882343700036305)
                  ·
                    refine ⟨8940329433661757775027229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11920439244882343700036305 8940329433661757775027229)
                    ·
                      refine ⟨3352623537623159165635211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8940329433661757775027229 3352623537623159165635211)
                      ·
                        rfl

theorem cell23_6529211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 3].length) (baseStart_6529211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529211 prefixEnd_6529211 := by exact prefixLift 6529211
  have htrace : WordTrace (prefixWord ++ tailWord_6529211) baseStart_6529211 baseEnd_6529211 := by
    simpa [prefixWord, tailWord_6529211, baseEnd_6529211] using wordTrace_append hprefix tailTrace_6529211
  have hstable : (prefixWord ++ tailWord_6529211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529211).length < 2 ^ (prefixWord ++ tailWord_6529211).sum := by decide
  have hdescent : baseEnd_6529211 < baseStart_6529211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529278 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_6529278 : Nat := 118140960795 + 6529278 * 2 ^ 59
def prefixEnd_6529278 : Nat := 4983230072969 + 3 ^ 40 * 6529278 * 2
def baseEnd_6529278 : Nat := 1117552646942336801165801

theorem tailTrace_6529278 : CollatzResearch.WordTrace tailWord_6529278 prefixEnd_6529278 1117552646942336801165801 := by
  unfold tailWord_6529278
  simp only [CollatzResearch.WordTrace]
  refine ⟨29767791604943549093614561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158761555226365595165944325 29767791604943549093614561)
  ·
    refine ⟨22325843703707661820210921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29767791604943549093614561 22325843703707661820210921)
    ·
      refine ⟨16744382777780746365158191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22325843703707661820210921 16744382777780746365158191)
      ·
        refine ⟨25116574166671119547737287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16744382777780746365158191 25116574166671119547737287)
        ·
          refine ⟨37674861250006679321605931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25116574166671119547737287 37674861250006679321605931)
          ·
            refine ⟨56512291875010018982408897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37674861250006679321605931 56512291875010018982408897)
            ·
              refine ⟨42384218906257514236806673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56512291875010018982408897 42384218906257514236806673)
              ·
                refine ⟨31788164179693135677605005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42384218906257514236806673 31788164179693135677605005)
                ·
                  refine ⟨11920561567384925879101877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31788164179693135677605005 11920561567384925879101877)
                  ·
                    refine ⟨1117552646942336801165801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11920561567384925879101877 1117552646942336801165801)
                    ·
                      rfl

theorem cell23_6529278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_6529278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529278 prefixEnd_6529278 := by exact prefixLift 6529278
  have htrace : WordTrace (prefixWord ++ tailWord_6529278) baseStart_6529278 baseEnd_6529278 := by
    simpa [prefixWord, tailWord_6529278, baseEnd_6529278] using wordTrace_append hprefix tailTrace_6529278
  have hstable : (prefixWord ++ tailWord_6529278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529278).length < 2 ^ (prefixWord ++ tailWord_6529278).sum := by decide
  have hdescent : baseEnd_6529278 < baseStart_6529278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529282 : List Nat := [3, 4, 1, 1, 2, 3, 2, 1, 6]
def baseStart_6529282 : Nat := 118140960795 + 6529282 * 2 ^ 59
def prefixEnd_6529282 : Nat := 4983230072969 + 3 ^ 40 * 6529282 * 2
def baseEnd_6529282 : Nat := 372517777194403154205265

theorem tailTrace_6529282 : CollatzResearch.WordTrace tailWord_6529282 prefixEnd_6529282 372517777194403154205265 := by
  unfold tailWord_6529282
  simp only [CollatzResearch.WordTrace]
  refine ⟨59535619682883475358015525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158761652487689267621374733 59535619682883475358015525)
  ·
    refine ⟨11162928690540651629627911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59535619682883475358015525 11162928690540651629627911)
    ·
      refine ⟨16744393035810977444441867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11162928690540651629627911 16744393035810977444441867)
      ·
        refine ⟨25116589553716466166662801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16744393035810977444441867 25116589553716466166662801)
        ·
          refine ⟨18837442165287349624997101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25116589553716466166662801 18837442165287349624997101)
          ·
            refine ⟨7064040811982756109373913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18837442165287349624997101 7064040811982756109373913)
            ·
              refine ⟨5298030608987067082030435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7064040811982756109373913 5298030608987067082030435)
              ·
                refine ⟨7947045913480600623045653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5298030608987067082030435 7947045913480600623045653)
                ·
                  refine ⟨372517777194403154205265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7947045913480600623045653 372517777194403154205265)
                  ·
                    rfl

theorem cell23_6529282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_6529282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529282 prefixEnd_6529282 := by exact prefixLift 6529282
  have htrace : WordTrace (prefixWord ++ tailWord_6529282) baseStart_6529282 baseEnd_6529282 := by
    simpa [prefixWord, tailWord_6529282, baseEnd_6529282] using wordTrace_append hprefix tailTrace_6529282
  have hstable : (prefixWord ++ tailWord_6529282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529282).length < 2 ^ (prefixWord ++ tailWord_6529282).sum := by decide
  have hdescent : baseEnd_6529282 < baseStart_6529282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529291 : List Nat := [1, 1, 1, 1, 5, 2, 2, 3, 1, 6]
def baseStart_6529291 : Nat := 118140960795 + 6529291 * 2 ^ 59
def prefixEnd_6529291 : Nat := 4983230072969 + 3 ^ 40 * 6529291 * 2
def baseEnd_6529291 : Nat := 1117554872025172950878281

theorem tailTrace_6529291 : CollatzResearch.WordTrace tailWord_6529291 prefixEnd_6529291 1117554872025172950878281 := by
  unfold tailWord_6529291
  simp only [CollatzResearch.WordTrace]
  refine ⟨238142806988501295969139727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158761871325667530646093151 238142806988501295969139727)
  ·
    refine ⟨357214210482751943953709591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238142806988501295969139727 357214210482751943953709591)
    ·
      refine ⟨535821315724127915930564387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357214210482751943953709591 535821315724127915930564387)
      ·
        refine ⟨803731973586191873895846581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535821315724127915930564387 803731973586191873895846581)
        ·
          refine ⟨75349872523705488177735617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 803731973586191873895846581 75349872523705488177735617)
          ·
            refine ⟨56512404392779116133301713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75349872523705488177735617 56512404392779116133301713)
            ·
              refine ⟨42384303294584337099976285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56512404392779116133301713 42384303294584337099976285)
              ·
                refine ⟨15894113735469126412491107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42384303294584337099976285 15894113735469126412491107)
                ·
                  refine ⟨23841170603203689618736661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15894113735469126412491107 23841170603203689618736661)
                  ·
                    refine ⟨1117554872025172950878281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23841170603203689618736661 1117554872025172950878281)
                    ·
                      rfl

theorem cell23_6529291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 6].length) (baseStart_6529291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529291 prefixEnd_6529291 := by exact prefixLift 6529291
  have htrace : WordTrace (prefixWord ++ tailWord_6529291) baseStart_6529291 baseEnd_6529291 := by
    simpa [prefixWord, tailWord_6529291, baseEnd_6529291] using wordTrace_append hprefix tailTrace_6529291
  have hstable : (prefixWord ++ tailWord_6529291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529291).length < 2 ^ (prefixWord ++ tailWord_6529291).sum := by decide
  have hdescent : baseEnd_6529291 < baseStart_6529291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529301 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_6529301 : Nat := 118140960795 + 6529301 * 2 ^ 59
def prefixEnd_6529301 : Nat := 4983230072969 + 3 ^ 40 * 6529301 * 2
def baseEnd_6529301 : Nat := 3352669750882063813509797

theorem tailTrace_6529301 : CollatzResearch.WordTrace tailWord_6529301 prefixEnd_6529301 3352669750882063813509797 := by
  unfold tailWord_6529301
  simp only [CollatzResearch.WordTrace]
  refine ⟨238143171718465067677003757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158762114478976711784669171 238143171718465067677003757)
  ·
    refine ⟨89303689394424400378876409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238143171718465067677003757 89303689394424400378876409)
    ·
      refine ⟨66977767045818300284157307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89303689394424400378876409 66977767045818300284157307)
      ·
        refine ⟨100466650568727450426235961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66977767045818300284157307 100466650568727450426235961)
        ·
          refine ⟨75349987926545587819676971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100466650568727450426235961 75349987926545587819676971)
          ·
            refine ⟨113024981889818381729515457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75349987926545587819676971 113024981889818381729515457)
            ·
              refine ⟨84768736417363786297136593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113024981889818381729515457 84768736417363786297136593)
              ·
                refine ⟨63576552313022839722852445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84768736417363786297136593 63576552313022839722852445)
                ·
                  refine ⟨23841207117383564896069667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63576552313022839722852445 23841207117383564896069667)
                  ·
                    refine ⟨35761810676075347344104501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23841207117383564896069667 35761810676075347344104501)
                    ·
                      refine ⟨3352669750882063813509797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35761810676075347344104501 3352669750882063813509797)
                      ·
                        rfl

theorem cell23_6529301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_6529301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529301 prefixEnd_6529301 := by exact prefixLift 6529301
  have htrace : WordTrace (prefixWord ++ tailWord_6529301) baseStart_6529301 baseEnd_6529301 := by
    simpa [prefixWord, tailWord_6529301, baseEnd_6529301] using wordTrace_append hprefix tailTrace_6529301
  have hstable : (prefixWord ++ tailWord_6529301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529301).length < 2 ^ (prefixWord ++ tailWord_6529301).sum := by decide
  have hdescent : baseEnd_6529301 < baseStart_6529301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529315 : List Nat := [1, 1, 1, 4, 2, 2, 5, 1, 1, 1, 4]
def baseStart_6529315 : Nat := 118140960795 + 6529315 * 2 ^ 59
def prefixEnd_6529315 : Nat := 4983230072969 + 3 ^ 40 * 6529315 * 2
def baseEnd_6529315 : Nat := 3352676939611226758734733

theorem tailTrace_6529315 : CollatzResearch.WordTrace tailWord_6529315 prefixEnd_6529315 3352676939611226758734733 := by
  unfold tailWord_6529315
  simp only [CollatzResearch.WordTrace]
  refine ⟨238143682340414348068013399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158762454893609565378675599 238143682340414348068013399)
  ·
    refine ⟨357215523510621522102020099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238143682340414348068013399 357215523510621522102020099)
    ·
      refine ⟨535823285265932283153030149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357215523510621522102020099 535823285265932283153030149)
      ·
        refine ⟨100466865987362303091193153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 535823285265932283153030149 100466865987362303091193153)
        ·
          refine ⟨75350149490521727318394865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100466865987362303091193153 75350149490521727318394865)
          ·
            refine ⟨56512612117891295488796149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75350149490521727318394865 56512612117891295488796149)
            ·
              refine ⟨5298057386052308952074639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56512612117891295488796149 5298057386052308952074639)
              ·
                refine ⟨7947086079078463428111959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5298057386052308952074639 7947086079078463428111959)
                ·
                  refine ⟨11920629118617695142167939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7947086079078463428111959 11920629118617695142167939)
                  ·
                    refine ⟨17880943677926542713251909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11920629118617695142167939 17880943677926542713251909)
                    ·
                      refine ⟨3352676939611226758734733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17880943677926542713251909 3352676939611226758734733)
                      ·
                        rfl

theorem cell23_6529315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_6529315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529315 prefixEnd_6529315 := by exact prefixLift 6529315
  have htrace : WordTrace (prefixWord ++ tailWord_6529315) baseStart_6529315 baseEnd_6529315 := by
    simpa [prefixWord, tailWord_6529315, baseEnd_6529315] using wordTrace_append hprefix tailTrace_6529315
  have hstable : (prefixWord ++ tailWord_6529315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529315).length < 2 ^ (prefixWord ++ tailWord_6529315).sum := by decide
  have hdescent : baseEnd_6529315 < baseStart_6529315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529326 : List Nat := [4, 1, 3, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_6529326 : Nat := 118140960795 + 6529326 * 2 ^ 59
def prefixEnd_6529326 : Nat := 4983230072969 + 3 ^ 40 * 6529326 * 2
def baseEnd_6529326 : Nat := 3352682587898426215697183

theorem tailTrace_6529326 : CollatzResearch.WordTrace tailWord_6529326 prefixEnd_6529326 3352682587898426215697183 := by
  unfold tailWord_6529326
  simp only [CollatzResearch.WordTrace]
  refine ⟨29768010442921812118332979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158762722362249664631109221 29768010442921812118332979)
  ·
    refine ⟨44652015664382718177499469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29768010442921812118332979 44652015664382718177499469)
    ·
      refine ⟨16744505874143519316562301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44652015664382718177499469 16744505874143519316562301)
      ·
        refine ⟨6279189702803819743710863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16744505874143519316562301 6279189702803819743710863)
        ·
          refine ⟨9418784554205729615566295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6279189702803819743710863 9418784554205729615566295)
          ·
            refine ⟨14128176831308594423349443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9418784554205729615566295 14128176831308594423349443)
            ·
              refine ⟨21192265246962891635024165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14128176831308594423349443 21192265246962891635024165)
              ·
                refine ⟨3973549733805542181567031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21192265246962891635024165 3973549733805542181567031)
                ·
                  refine ⟨5960324600708313272350547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3973549733805542181567031 5960324600708313272350547)
                  ·
                    refine ⟨8940486901062469908525821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5960324600708313272350547 8940486901062469908525821)
                    ·
                      refine ⟨3352682587898426215697183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8940486901062469908525821 3352682587898426215697183)
                      ·
                        rfl

theorem cell23_6529326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_6529326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529326 prefixEnd_6529326 := by exact prefixLift 6529326
  have htrace : WordTrace (prefixWord ++ tailWord_6529326) baseStart_6529326 baseEnd_6529326 := by
    simpa [prefixWord, tailWord_6529326, baseEnd_6529326] using wordTrace_append hprefix tailTrace_6529326
  have hstable : (prefixWord ++ tailWord_6529326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529326).length < 2 ^ (prefixWord ++ tailWord_6529326).sum := by decide
  have hdescent : baseEnd_6529326 < baseStart_6529326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529338 : List Nat := [3, 1, 1, 1, 4, 4, 1, 8]
def baseStart_6529338 : Nat := 118140960795 + 6529338 * 2 ^ 59
def prefixEnd_6529338 : Nat := 4983230072969 + 3 ^ 40 * 6529338 * 2
def baseEnd_6529338 : Nat := 124173657395047413657301

theorem tailTrace_6529338 : CollatzResearch.WordTrace tailWord_6529338 prefixEnd_6529338 124173657395047413657301 := by
  unfold tailWord_6529338
  simp only [CollatzResearch.WordTrace]
  refine ⟨59536130304832755749025167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158763014146220681997400445 59536130304832755749025167)
  ·
    refine ⟨89304195457249133623537751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59536130304832755749025167 89304195457249133623537751)
    ·
      refine ⟨133956293185873700435306627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89304195457249133623537751 133956293185873700435306627)
      ·
        refine ⟨200934439778810550652959941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133956293185873700435306627 200934439778810550652959941)
        ·
          refine ⟨37675207458526978247429989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200934439778810550652959941 37675207458526978247429989)
          ·
            refine ⟨7064101398473808421393123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37675207458526978247429989 7064101398473808421393123)
            ·
              refine ⟨10596152097710712632089685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7064101398473808421393123 10596152097710712632089685)
              ·
                refine ⟨124173657395047413657301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10596152097710712632089685 124173657395047413657301)
                ·
                  rfl

theorem cell23_6529338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 8].length) (baseStart_6529338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529338 prefixEnd_6529338 := by exact prefixLift 6529338
  have htrace : WordTrace (prefixWord ++ tailWord_6529338) baseStart_6529338 baseEnd_6529338 := by
    simpa [prefixWord, tailWord_6529338, baseEnd_6529338] using wordTrace_append hprefix tailTrace_6529338
  have hstable : (prefixWord ++ tailWord_6529338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529338).length < 2 ^ (prefixWord ++ tailWord_6529338).sum := by decide
  have hdescent : baseEnd_6529338 < baseStart_6529338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529351 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 2, 7]
def baseStart_6529351 : Nat := 118140960795 + 6529351 * 2 ^ 59
def prefixEnd_6529351 : Nat := 4983230072969 + 3 ^ 40 * 6529351 * 2
def baseEnd_6529351 : Nat := 1117565141638262872628189

theorem tailTrace_6529351 : CollatzResearch.WordTrace tailWord_6529351 prefixEnd_6529351 1117565141638262872628189 := by
  unfold tailWord_6529351
  simp only [CollatzResearch.WordTrace]
  refine ⟨238144995368283926216323907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158763330245522617477549271 238144995368283926216323907)
  ·
    refine ⟨357217493052425889324485861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238144995368283926216323907 357217493052425889324485861)
    ·
      refine ⟨66978279947329854248341099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 357217493052425889324485861 66978279947329854248341099)
      ·
        refine ⟨100467419920994781372511649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66978279947329854248341099 100467419920994781372511649)
        ·
          refine ⟨75350564940746086029383737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100467419920994781372511649 75350564940746086029383737)
          ·
            refine ⟨56512923705559564522037803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75350564940746086029383737 56512923705559564522037803)
            ·
              refine ⟨84769385558339346783056705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56512923705559564522037803 84769385558339346783056705)
              ·
                refine ⟨63577039168754510087292529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84769385558339346783056705 63577039168754510087292529)
                ·
                  refine ⟨47682779376565882565469397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63577039168754510087292529 47682779376565882565469397)
                  ·
                    refine ⟨1117565141638262872628189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47682779376565882565469397 1117565141638262872628189)
                    ·
                      rfl

theorem cell23_6529351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_6529351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529351 prefixEnd_6529351 := by exact prefixLift 6529351
  have htrace : WordTrace (prefixWord ++ tailWord_6529351) baseStart_6529351 baseEnd_6529351 := by
    simpa [prefixWord, tailWord_6529351, baseEnd_6529351] using wordTrace_append hprefix tailTrace_6529351
  have hstable : (prefixWord ++ tailWord_6529351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529351).length < 2 ^ (prefixWord ++ tailWord_6529351).sum := by decide
  have hdescent : baseEnd_6529351 < baseStart_6529351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529391 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 5]
def baseStart_6529391 : Nat := 118140960795 + 6529391 * 2 ^ 59
def prefixEnd_6529391 : Nat := 4983230072969 + 3 ^ 40 * 6529391 * 2
def baseEnd_6529391 : Nat := 3352715964140968461384383

theorem tailTrace_6529391 : CollatzResearch.WordTrace tailWord_6529391 prefixEnd_6529391 3352715964140968461384383 := by
  unfold tailWord_6529391
  simp only [CollatzResearch.WordTrace]
  refine ⟨238146454288139013047780027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158764302858759342031853351 238146454288139013047780027)
  ·
    refine ⟨357219681432208519571670041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238146454288139013047780027 357219681432208519571670041)
    ·
      refine ⟨267914761074156389678752531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357219681432208519571670041 267914761074156389678752531)
      ·
        refine ⟨401872141611234584518128797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267914761074156389678752531 401872141611234584518128797)
        ·
          refine ⟨150702053104212969194298299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401872141611234584518128797 150702053104212969194298299)
          ·
            refine ⟨226053079656319453791447449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150702053104212969194298299 226053079656319453791447449)
            ·
              refine ⟨169539809742239590343585587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226053079656319453791447449 169539809742239590343585587)
              ·
                refine ⟨254309714613359385515378381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169539809742239590343585587 254309714613359385515378381)
                ·
                  refine ⟨95366142980009769568266893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254309714613359385515378381 95366142980009769568266893)
                  ·
                    refine ⟨35762303617503663588100085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95366142980009769568266893 35762303617503663588100085)
                    ·
                      refine ⟨3352715964140968461384383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35762303617503663588100085 3352715964140968461384383)
                      ·
                        rfl

theorem cell23_6529391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_6529391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529391 prefixEnd_6529391 := by exact prefixLift 6529391
  have htrace : WordTrace (prefixWord ++ tailWord_6529391) baseStart_6529391 baseEnd_6529391 := by
    simpa [prefixWord, tailWord_6529391, baseEnd_6529391] using wordTrace_append hprefix tailTrace_6529391
  have hstable : (prefixWord ++ tailWord_6529391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529391).length < 2 ^ (prefixWord ++ tailWord_6529391).sum := by decide
  have hdescent : baseEnd_6529391 < baseStart_6529391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529409 : List Nat := [1, 2, 4, 3, 1, 2, 2, 2, 1, 3, 2]
def baseStart_6529409 : Nat := 118140960795 + 6529409 * 2 ^ 59
def prefixEnd_6529409 : Nat := 4983230072969 + 3 ^ 40 * 6529409 * 2
def baseEnd_6529409 : Nat := 3352725206792749390959301

theorem tailTrace_6529409 : CollatzResearch.WordTrace tailWord_6529409 prefixEnd_6529409 3352725206792749390959301 := by
  unfold tailWord_6529409
  simp only [CollatzResearch.WordTrace]
  refine ⟨238147110802073802121935281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158764740534715868081290187 238147110802073802121935281)
  ·
    refine ⟨178610333101555351591451461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238147110802073802121935281 178610333101555351591451461)
    ·
      refine ⟨33489437456541628423397149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178610333101555351591451461 33489437456541628423397149)
      ·
        refine ⟨12558539046203110658773931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33489437456541628423397149 12558539046203110658773931)
        ·
          refine ⟨18837808569304665988160897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12558539046203110658773931 18837808569304665988160897)
          ·
            refine ⟨14128356426978499491120673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18837808569304665988160897 14128356426978499491120673)
            ·
              refine ⟨10596267320233874618340505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14128356426978499491120673 10596267320233874618340505)
              ·
                refine ⟨7947200490175405963755379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10596267320233874618340505 7947200490175405963755379)
                ·
                  refine ⟨11920800735263108945633069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7947200490175405963755379 11920800735263108945633069)
                  ·
                    refine ⟨4470300275723665854612401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11920800735263108945633069 4470300275723665854612401)
                    ·
                      refine ⟨3352725206792749390959301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4470300275723665854612401 3352725206792749390959301)
                      ·
                        rfl

theorem cell23_6529409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_6529409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529409 prefixEnd_6529409 := by exact prefixLift 6529409
  have htrace : WordTrace (prefixWord ++ tailWord_6529409) baseStart_6529409 baseEnd_6529409 := by
    simpa [prefixWord, tailWord_6529409, baseEnd_6529409] using wordTrace_append hprefix tailTrace_6529409
  have hstable : (prefixWord ++ tailWord_6529409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529409).length < 2 ^ (prefixWord ++ tailWord_6529409).sum := by decide
  have hdescent : baseEnd_6529409 < baseStart_6529409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529450 : List Nat := [3, 1, 6, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_6529450 : Nat := 118140960795 + 6529450 * 2 ^ 59
def prefixEnd_6529450 : Nat := 4983230072969 + 3 ^ 40 * 6529450 * 2
def baseEnd_6529450 : Nat := 3352746259499583730546613

theorem tailTrace_6529450 : CollatzResearch.WordTrace tailWord_6529450 prefixEnd_6529450 3352746259499583730546613 := by
  unfold tailWord_6529450
  simp only [CollatzResearch.WordTrace]
  refine ⟨59537151548731316531044451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158765737463283510749451869 59537151548731316531044451)
  ·
    refine ⟨89305727323096974796566677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59537151548731316531044451 89305727323096974796566677)
    ·
      refine ⟨4186205968270170693589063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89305727323096974796566677 4186205968270170693589063)
      ·
        refine ⟨6279308952405256040383595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4186205968270170693589063 6279308952405256040383595)
        ·
          refine ⟨9418963428607884060575393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6279308952405256040383595 9418963428607884060575393)
          ·
            refine ⟨7064222571455913045431545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9418963428607884060575393 7064222571455913045431545)
            ·
              refine ⟨5298166928591934784073659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7064222571455913045431545 5298166928591934784073659)
              ·
                refine ⟨7947250392887902176110489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5298166928591934784073659 7947250392887902176110489)
                ·
                  refine ⟨5960437794665926632082867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7947250392887902176110489 5960437794665926632082867)
                  ·
                    refine ⟨8940656691998889948124301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5960437794665926632082867 8940656691998889948124301)
                    ·
                      refine ⟨3352746259499583730546613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8940656691998889948124301 3352746259499583730546613)
                      ·
                        rfl

theorem cell23_6529450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_6529450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529450 prefixEnd_6529450 := by exact prefixLift 6529450
  have htrace : WordTrace (prefixWord ++ tailWord_6529450) baseStart_6529450 baseEnd_6529450 := by
    simpa [prefixWord, tailWord_6529450, baseEnd_6529450] using wordTrace_append hprefix tailTrace_6529450
  have hstable : (prefixWord ++ tailWord_6529450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529450).length < 2 ^ (prefixWord ++ tailWord_6529450).sum := by decide
  have hdescent : baseEnd_6529450 < baseStart_6529450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529458 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 4, 5]
def baseStart_6529458 : Nat := 118140960795 + 6529458 * 2 ^ 59
def prefixEnd_6529458 : Nat := 4983230072969 + 3 ^ 40 * 6529458 * 2
def baseEnd_6529458 : Nat := 1117583455781606566415525

theorem tailTrace_6529458 : CollatzResearch.WordTrace tailWord_6529458 prefixEnd_6529458 1117583455781606566415525 := by
  unfold tailWord_6529458
  simp only [CollatzResearch.WordTrace]
  refine ⟨59537224494724070872617257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158765931985930855660312685 59537224494724070872617257)
  ·
    refine ⟨44652918371043053154462943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59537224494724070872617257 44652918371043053154462943)
    ·
      refine ⟨66979377556564579731694415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44652918371043053154462943 66979377556564579731694415)
      ·
        refine ⟨100469066334846869597541623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66979377556564579731694415 100469066334846869597541623)
        ·
          refine ⟨150703599502270304396312435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100469066334846869597541623 150703599502270304396312435)
          ·
            refine ⟨226055399253405456594468653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150703599502270304396312435 226055399253405456594468653)
            ·
              refine ⟨84770774720027046222925745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226055399253405456594468653 84770774720027046222925745)
              ·
                refine ⟨63578081040020284667194309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84770774720027046222925745 63578081040020284667194309)
                ·
                  refine ⟨11920890195003803375098933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63578081040020284667194309 11920890195003803375098933)
                  ·
                    refine ⟨1117583455781606566415525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11920890195003803375098933 1117583455781606566415525)
                    ·
                      rfl

theorem cell23_6529458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_6529458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529458 prefixEnd_6529458 := by exact prefixLift 6529458
  have htrace : WordTrace (prefixWord ++ tailWord_6529458) baseStart_6529458 baseEnd_6529458 := by
    simpa [prefixWord, tailWord_6529458, baseEnd_6529458] using wordTrace_append hprefix tailTrace_6529458
  have hstable : (prefixWord ++ tailWord_6529458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529458).length < 2 ^ (prefixWord ++ tailWord_6529458).sum := by decide
  have hdescent : baseEnd_6529458 < baseStart_6529458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529460 : List Nat := [2, 5, 2, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_6529460 : Nat := 118140960795 + 6529460 * 2 ^ 59
def prefixEnd_6529460 : Nat := 4983230072969 + 3 ^ 40 * 6529460 * 2
def baseEnd_6529460 : Nat := 3352751394306128691421567

theorem tailTrace_6529460 : CollatzResearch.WordTrace tailWord_6529460 prefixEnd_6529460 3352751394306128691421567 := by
  unfold tailWord_6529460
  simp only [CollatzResearch.WordTrace]
  refine ⟨119074485462444518916020917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158765980616592691888027889 119074485462444518916020917)
  ·
    refine ⟨11163233012104173648376961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119074485462444518916020917 11163233012104173648376961)
    ·
      refine ⟨8372424759078130236282721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11163233012104173648376961 8372424759078130236282721)
      ·
        refine ⟨6279318569308597677212041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8372424759078130236282721 6279318569308597677212041)
        ·
          refine ⟨4709488926981448257909031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6279318569308597677212041 4709488926981448257909031)
          ·
            refine ⟨7064233390472172386863547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4709488926981448257909031 7064233390472172386863547)
            ·
              refine ⟨10596350085708258580295321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7064233390472172386863547 10596350085708258580295321)
              ·
                refine ⟨7947262564281193935221491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10596350085708258580295321 7947262564281193935221491)
                ·
                  refine ⟨11920893846421790902832237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7947262564281193935221491 11920893846421790902832237)
                  ·
                    refine ⟨4470335192408171588562089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11920893846421790902832237 4470335192408171588562089)
                    ·
                      refine ⟨3352751394306128691421567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4470335192408171588562089 3352751394306128691421567)
                      ·
                        rfl

theorem cell23_6529460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_6529460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529460 prefixEnd_6529460 := by exact prefixLift 6529460
  have htrace : WordTrace (prefixWord ++ tailWord_6529460) baseStart_6529460 baseEnd_6529460 := by
    simpa [prefixWord, tailWord_6529460, baseEnd_6529460] using wordTrace_append hprefix tailTrace_6529460
  have hstable : (prefixWord ++ tailWord_6529460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529460).length < 2 ^ (prefixWord ++ tailWord_6529460).sum := by decide
  have hdescent : baseEnd_6529460 < baseStart_6529460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529498 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5]
def baseStart_6529498 : Nat := 118140960795 + 6529498 * 2 ^ 59
def prefixEnd_6529498 : Nat := 4983230072969 + 3 ^ 40 * 6529498 * 2
def baseEnd_6529498 : Nat := 3352770906570999542746391

theorem tailTrace_6529498 : CollatzResearch.WordTrace tailWord_6529498 prefixEnd_6529498 3352770906570999542746391 := by
  unfold tailWord_6529498
  simp only [CollatzResearch.WordTrace]
  refine ⟨59537589224687842580481287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158766904599167580214616765 59537589224687842580481287)
  ·
    refine ⟨89306383837031763870721931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59537589224687842580481287 89306383837031763870721931)
    ·
      refine ⟨133959575755547645806082897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89306383837031763870721931 133959575755547645806082897)
      ·
        refine ⟨100469681816660734354562173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133959575755547645806082897 100469681816660734354562173)
        ·
          refine ⟨37676130681247775382960815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100469681816660734354562173 37676130681247775382960815)
          ·
            refine ⟨56514196021871663074441223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37676130681247775382960815 56514196021871663074441223)
            ·
              refine ⟨84771294032807494611661835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56514196021871663074441223 84771294032807494611661835)
              ·
                refine ⟨127156941049211241917492753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84771294032807494611661835 127156941049211241917492753)
                ·
                  refine ⟨95367705786908431438119565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127156941049211241917492753 95367705786908431438119565)
                  ·
                    refine ⟨35762889670090661789294837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95367705786908431438119565 35762889670090661789294837)
                    ·
                      refine ⟨3352770906570999542746391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35762889670090661789294837 3352770906570999542746391)
                      ·
                        rfl

theorem cell23_6529498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_6529498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529498 prefixEnd_6529498 := by exact prefixLift 6529498
  have htrace : WordTrace (prefixWord ++ tailWord_6529498) baseStart_6529498 baseEnd_6529498 := by
    simpa [prefixWord, tailWord_6529498, baseEnd_6529498] using wordTrace_append hprefix tailTrace_6529498
  have hstable : (prefixWord ++ tailWord_6529498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529498).length < 2 ^ (prefixWord ++ tailWord_6529498).sum := by decide
  have hdescent : baseEnd_6529498 < baseStart_6529498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529505 : List Nat := [1, 2, 3, 1, 2, 2, 2, 3, 3, 4]
def baseStart_6529505 : Nat := 118140960795 + 6529505 * 2 ^ 59
def prefixEnd_6529505 : Nat := 4983230072969 + 3 ^ 40 * 6529505 * 2
def baseEnd_6529505 : Nat := 1117591500311860338452953

theorem tailTrace_6529505 : CollatzResearch.WordTrace tailWord_6529505 prefixEnd_6529505 1117591500311860338452953 := by
  unfold tailWord_6529505
  simp only [CollatzResearch.WordTrace]
  refine ⟨238150612209726010517429969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158767074806484007011619979 238150612209726010517429969)
  ·
    refine ⟨178612959157294507888072477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238150612209726010517429969 178612959157294507888072477)
    ·
      refine ⟨66979859683985440458027179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178612959157294507888072477 66979859683985440458027179)
      ·
        refine ⟨100469789525978160687040769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66979859683985440458027179 100469789525978160687040769)
        ·
          refine ⟨75352342144483620515280577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100469789525978160687040769 75352342144483620515280577)
          ·
            refine ⟨56514256608362715386460433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75352342144483620515280577 56514256608362715386460433)
            ·
              refine ⟨42385692456272036539845325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56514256608362715386460433 42385692456272036539845325)
              ·
                refine ⟨15894634671102013702441997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42385692456272036539845325 15894634671102013702441997)
                ·
                  refine ⟨5960488001663255138415749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15894634671102013702441997 5960488001663255138415749)
                  ·
                    refine ⟨1117591500311860338452953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5960488001663255138415749 1117591500311860338452953)
                    ·
                      rfl

theorem cell23_6529505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_6529505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529505 prefixEnd_6529505 := by exact prefixLift 6529505
  have htrace : WordTrace (prefixWord ++ tailWord_6529505) baseStart_6529505 baseEnd_6529505 := by
    simpa [prefixWord, tailWord_6529505, baseEnd_6529505] using wordTrace_append hprefix tailTrace_6529505
  have hstable : (prefixWord ++ tailWord_6529505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529505).length < 2 ^ (prefixWord ++ tailWord_6529505).sum := by decide
  have hdescent : baseEnd_6529505 < baseStart_6529505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529508 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_6529508 : Nat := 118140960795 + 6529508 * 2 ^ 59
def prefixEnd_6529508 : Nat := 4983230072969 + 3 ^ 40 * 6529508 * 2
def baseEnd_6529508 : Nat := 3352776041377544503621345

theorem tailTrace_6529508 : CollatzResearch.WordTrace tailWord_6529508 prefixEnd_6529508 3352776041377544503621345 := by
  unfold tailWord_6529508
  simp only [CollatzResearch.WordTrace]
  refine ⟨119075360814357571014894589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158767147752476761353192785 119075360814357571014894589)
  ·
    refine ⟨44653260305384089130585471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119075360814357571014894589 44653260305384089130585471)
    ·
      refine ⟨66979890458076133695878207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44653260305384089130585471 66979890458076133695878207)
      ·
        refine ⟨100469835687114200543817311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66979890458076133695878207 100469835687114200543817311)
        ·
          refine ⟨150704753530671300815725967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100469835687114200543817311 150704753530671300815725967)
          ·
            refine ⟨226057130296006951223588951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150704753530671300815725967 226057130296006951223588951)
            ·
              refine ⟨339085695444010426835383427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226057130296006951223588951 339085695444010426835383427)
              ·
                refine ⟨508628543166015640253075141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339085695444010426835383427 508628543166015640253075141)
                ·
                  refine ⟨95367851843627932547451589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 508628543166015640253075141 95367851843627932547451589)
                  ·
                    refine ⟨17881472220680237352647173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95367851843627932547451589 17881472220680237352647173)
                    ·
                      refine ⟨3352776041377544503621345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17881472220680237352647173 3352776041377544503621345)
                      ·
                        rfl

theorem cell23_6529508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_6529508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529508 prefixEnd_6529508 := by exact prefixLift 6529508
  have htrace : WordTrace (prefixWord ++ tailWord_6529508) baseStart_6529508 baseEnd_6529508 := by
    simpa [prefixWord, tailWord_6529508, baseEnd_6529508] using wordTrace_append hprefix tailTrace_6529508
  have hstable : (prefixWord ++ tailWord_6529508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529508).length < 2 ^ (prefixWord ++ tailWord_6529508).sum := by decide
  have hdescent : baseEnd_6529508 < baseStart_6529508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529512 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 2, 4, 2]
def baseStart_6529512 : Nat := 118140960795 + 6529512 * 2 ^ 59
def prefixEnd_6529512 : Nat := 4983230072969 + 3 ^ 40 * 6529512 * 2
def baseEnd_6529512 : Nat := 3352778095300162487971327

theorem tailTrace_6529512 : CollatzResearch.WordTrace tailWord_6529512 prefixEnd_6529512 3352778095300162487971327 := by
  unfold tailWord_6529512
  simp only [CollatzResearch.WordTrace]
  refine ⟨119075433760350325356467395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158767245013800433808623193 119075433760350325356467395)
  ·
    refine ⟨178613150640525488034701093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119075433760350325356467395 178613150640525488034701093)
    ·
      refine ⟨33489965745098529006506455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178613150640525488034701093 33489965745098529006506455)
      ·
        refine ⟨50234948617647793509759683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33489965745098529006506455 50234948617647793509759683)
        ·
          refine ⟨75352422926471690264639525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50234948617647793509759683 75352422926471690264639525)
          ·
            refine ⟨14128579298713441924619911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75352422926471690264639525 14128579298713441924619911)
            ·
              refine ⟨21192868948070162886929867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14128579298713441924619911 21192868948070162886929867)
              ·
                refine ⟨31789303422105244330394801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21192868948070162886929867 31789303422105244330394801)
                ·
                  refine ⟨23841977566578933247796101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31789303422105244330394801 23841977566578933247796101)
                  ·
                    refine ⟨4470370793733549983961769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23841977566578933247796101 4470370793733549983961769)
                    ·
                      refine ⟨3352778095300162487971327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4470370793733549983961769 3352778095300162487971327)
                      ·
                        rfl

theorem cell23_6529512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_6529512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529512 prefixEnd_6529512 := by exact prefixLift 6529512
  have htrace : WordTrace (prefixWord ++ tailWord_6529512) baseStart_6529512 baseEnd_6529512 := by
    simpa [prefixWord, tailWord_6529512, baseEnd_6529512] using wordTrace_append hprefix tailTrace_6529512
  have hstable : (prefixWord ++ tailWord_6529512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529512).length < 2 ^ (prefixWord ++ tailWord_6529512).sum := by decide
  have hdescent : baseEnd_6529512 < baseStart_6529512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529556 : List Nat := [2, 4, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_6529556 : Nat := 118140960795 + 6529556 * 2 ^ 59
def prefixEnd_6529556 : Nat := 4983230072969 + 3 ^ 40 * 6529556 * 2
def baseEnd_6529556 : Nat := 1117600229482986771940375

theorem tailTrace_6529556 : CollatzResearch.WordTrace tailWord_6529556 prefixEnd_6529556 1117600229482986771940375 := by
  unfold tailWord_6529556
  simp only [CollatzResearch.WordTrace]
  refine ⟨119076236166270623113768261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158768314888360830818357681 119076236166270623113768261)
  ·
    refine ⟨22326794281175741833831549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119076236166270623113768261 22326794281175741833831549)
    ·
      refine ⟨8372547855440903187686831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22326794281175741833831549 8372547855440903187686831)
      ·
        refine ⟨12558821783161354781530247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8372547855440903187686831 12558821783161354781530247)
        ·
          refine ⟨18838232674742032172295371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12558821783161354781530247 18838232674742032172295371)
          ·
            refine ⟨28257349012113048258443057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18838232674742032172295371 28257349012113048258443057)
            ·
              refine ⟨21193011759084786193832293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28257349012113048258443057 21193011759084786193832293)
              ·
                refine ⟨3973689704828397411343555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21193011759084786193832293 3973689704828397411343555)
                ·
                  refine ⟨5960534557242596117015333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3973689704828397411343555 5960534557242596117015333)
                  ·
                    refine ⟨1117600229482986771940375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5960534557242596117015333 1117600229482986771940375)
                    ·
                      rfl

theorem cell23_6529556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_6529556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529556 prefixEnd_6529556 := by exact prefixLift 6529556
  have htrace : WordTrace (prefixWord ++ tailWord_6529556) baseStart_6529556 baseEnd_6529556 := by
    simpa [prefixWord, tailWord_6529556, baseEnd_6529556] using wordTrace_append hprefix tailTrace_6529556
  have hstable : (prefixWord ++ tailWord_6529556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529556).length < 2 ^ (prefixWord ++ tailWord_6529556).sum := by decide
  have hdescent : baseEnd_6529556 < baseStart_6529556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529562 : List Nat := [3, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3]
def baseStart_6529562 : Nat := 118140960795 + 6529562 * 2 ^ 59
def prefixEnd_6529562 : Nat := 4983230072969 + 3 ^ 40 * 6529562 * 2
def baseEnd_6529562 : Nat := 3352803769332887292346097

theorem tailTrace_6529562 : CollatzResearch.WordTrace tailWord_6529562 prefixEnd_6529562 3352803769332887292346097 := by
  unfold tailWord_6529562
  simp only [CollatzResearch.WordTrace]
  refine ⟨59538172792629877313063735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158768460780346339501503293 59538172792629877313063735)
  ·
    refine ⟨89307259188944815969595603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59538172792629877313063735 89307259188944815969595603)
    ·
      refine ⟨133960888783417223954393405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89307259188944815969595603 133960888783417223954393405)
      ·
        refine ⟨50235333293781458982897527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133960888783417223954393405 50235333293781458982897527)
        ·
          refine ⟨75352999940672188474346291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50235333293781458982897527 75352999940672188474346291)
          ·
            refine ⟨113029499911008282711519437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75352999940672188474346291 113029499911008282711519437)
            ·
              refine ⟨42386062466628106016819789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113029499911008282711519437 42386062466628106016819789)
              ·
                refine ⟨15894773424985539756307421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42386062466628106016819789 15894773424985539756307421)
                ·
                  refine ⟨5960540034369577408615283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15894773424985539756307421 5960540034369577408615283)
                  ·
                    refine ⟨8940810051554366112922925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5960540034369577408615283 8940810051554366112922925)
                    ·
                      refine ⟨3352803769332887292346097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8940810051554366112922925 3352803769332887292346097)
                      ·
                        rfl

theorem cell23_6529562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_6529562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529562 prefixEnd_6529562 := by exact prefixLift 6529562
  have htrace : WordTrace (prefixWord ++ tailWord_6529562) baseStart_6529562 baseEnd_6529562 := by
    simpa [prefixWord, tailWord_6529562, baseEnd_6529562] using wordTrace_append hprefix tailTrace_6529562
  have hstable : (prefixWord ++ tailWord_6529562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529562).length < 2 ^ (prefixWord ++ tailWord_6529562).sum := by decide
  have hdescent : baseEnd_6529562 < baseStart_6529562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529585 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 3, 1, 4]
def baseStart_6529585 : Nat := 118140960795 + 6529585 * 2 ^ 59
def prefixEnd_6529585 : Nat := 4983230072969 + 3 ^ 40 * 6529585 * 2
def baseEnd_6529585 : Nat := 3352815579387940702358491

theorem tailTrace_6529585 : CollatzResearch.WordTrace tailWord_6529585 prefixEnd_6529585 3352815579387940702358491 := by
  unfold tailWord_6529585
  simp only [CollatzResearch.WordTrace]
  refine ⟨238153530049436184180342209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158769020032957456120228139 238153530049436184180342209)
  ·
    refine ⟨178615147537077138135256657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238153530049436184180342209 178615147537077138135256657)
    ·
      refine ⟨133961360652807853601442493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178615147537077138135256657 133961360652807853601442493)
      ·
        refine ⟨50235510244802945100540935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133961360652807853601442493 50235510244802945100540935)
        ·
          refine ⟨75353265367204417650811403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50235510244802945100540935 75353265367204417650811403)
          ·
            refine ⟨113029898050806626476217105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75353265367204417650811403 113029898050806626476217105)
            ·
              refine ⟨84772423538104969857162829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113029898050806626476217105 84772423538104969857162829)
              ·
                refine ⟨31789658826789363696436061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84772423538104969857162829 31789658826789363696436061)
                ·
                  refine ⟨11921122060046011386163523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31789658826789363696436061 11921122060046011386163523)
                  ·
                    refine ⟨17881683090069017079245285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11921122060046011386163523 17881683090069017079245285)
                    ·
                      refine ⟨3352815579387940702358491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17881683090069017079245285 3352815579387940702358491)
                      ·
                        rfl

theorem cell23_6529585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_6529585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529585 prefixEnd_6529585 := by exact prefixLift 6529585
  have htrace : WordTrace (prefixWord ++ tailWord_6529585) baseStart_6529585 baseEnd_6529585 := by
    simpa [prefixWord, tailWord_6529585, baseEnd_6529585] using wordTrace_append hprefix tailTrace_6529585
  have hstable : (prefixWord ++ tailWord_6529585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529585).length < 2 ^ (prefixWord ++ tailWord_6529585).sum := by decide
  have hdescent : baseEnd_6529585 < baseStart_6529585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529596 : List Nat := [2, 2, 2, 2, 3, 1, 3, 3, 1, 1, 3]
def baseStart_6529596 : Nat := 118140960795 + 6529596 * 2 ^ 59
def prefixEnd_6529596 : Nat := 4983230072969 + 3 ^ 40 * 6529596 * 2
def baseEnd_6529596 : Nat := 3352821227675140159320941

theorem tailTrace_6529596 : CollatzResearch.WordTrace tailWord_6529596 prefixEnd_6529596 3352821227675140159320941 := by
  unfold tailWord_6529596
  simp only [CollatzResearch.WordTrace]
  refine ⟨119076965626198166529496321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158769287501597555372661761 119076965626198166529496321)
  ·
    refine ⟨89307724219648624897122241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119076965626198166529496321 89307724219648624897122241)
    ·
      refine ⟨66980793164736468672841681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89307724219648624897122241 66980793164736468672841681)
      ·
        refine ⟨50235594873552351504631261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66980793164736468672841681 50235594873552351504631261)
        ·
          refine ⟨18838348077582131814236723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50235594873552351504631261 18838348077582131814236723)
          ·
            refine ⟨28257522116373197721355085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18838348077582131814236723 28257522116373197721355085)
            ·
              refine ⟨10596570793639949145508157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28257522116373197721355085 10596570793639949145508157)
              ·
                refine ⟨3973714047614980929565559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10596570793639949145508157 3973714047614980929565559)
                ·
                  refine ⟨5960571071422471394348339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3973714047614980929565559 5960571071422471394348339)
                  ·
                    refine ⟨8940856607133707091522509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5960571071422471394348339 8940856607133707091522509)
                    ·
                      refine ⟨3352821227675140159320941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8940856607133707091522509 3352821227675140159320941)
                      ·
                        rfl

theorem cell23_6529596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_6529596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529596 prefixEnd_6529596 := by exact prefixLift 6529596
  have htrace : WordTrace (prefixWord ++ tailWord_6529596) baseStart_6529596 baseEnd_6529596 := by
    simpa [prefixWord, tailWord_6529596, baseEnd_6529596] using wordTrace_append hprefix tailTrace_6529596
  have hstable : (prefixWord ++ tailWord_6529596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529596).length < 2 ^ (prefixWord ++ tailWord_6529596).sum := by decide
  have hdescent : baseEnd_6529596 < baseStart_6529596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529605 : List Nat := [1, 3, 1, 1, 1, 5, 1, 3, 1, 1, 5]
def baseStart_6529605 : Nat := 118140960795 + 6529605 * 2 ^ 59
def prefixEnd_6529605 : Nat := 4983230072969 + 3 ^ 40 * 6529605 * 2
def baseEnd_6529605 : Nat := 3352825849001030624108399

theorem tailTrace_6529605 : CollatzResearch.WordTrace tailWord_6529605 prefixEnd_6529605 3352825849001030624108399 := by
  unfold tailWord_6529605
  simp only [CollatzResearch.WordTrace]
  refine ⟨238154259509363727596070269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158769506339575818397380179 238154259509363727596070269)
  ·
    refine ⟨89307847316011397848526351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238154259509363727596070269 89307847316011397848526351)
    ·
      refine ⟨133961770974017096772789527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89307847316011397848526351 133961770974017096772789527)
      ·
        refine ⟨200942656461025645159184291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133961770974017096772789527 200942656461025645159184291)
        ·
          refine ⟨301413984691538467738776437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200942656461025645159184291 301413984691538467738776437)
          ·
            refine ⟨28257561064831731350510291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 301413984691538467738776437 28257561064831731350510291)
            ·
              refine ⟨42386341597247597025765437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28257561064831731350510291 42386341597247597025765437)
              ·
                refine ⟨15894878098967848884662039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42386341597247597025765437 15894878098967848884662039)
                ·
                  refine ⟨23842317148451773326993059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15894878098967848884662039 23842317148451773326993059)
                  ·
                    refine ⟨35763475722677659990489589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23842317148451773326993059 35763475722677659990489589)
                    ·
                      refine ⟨3352825849001030624108399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35763475722677659990489589 3352825849001030624108399)
                      ·
                        rfl

theorem cell23_6529605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_6529605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529605 prefixEnd_6529605 := by exact prefixLift 6529605
  have htrace : WordTrace (prefixWord ++ tailWord_6529605) baseStart_6529605 baseEnd_6529605 := by
    simpa [prefixWord, tailWord_6529605, baseEnd_6529605] using wordTrace_append hprefix tailTrace_6529605
  have hstable : (prefixWord ++ tailWord_6529605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529605).length < 2 ^ (prefixWord ++ tailWord_6529605).sum := by decide
  have hdescent : baseEnd_6529605 < baseStart_6529605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529606 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_6529606 : Nat := 118140960795 + 6529606 * 2 ^ 59
def prefixEnd_6529606 : Nat := 4983230072969 + 3 ^ 40 * 6529606 * 2
def baseEnd_6529606 : Nat := 3352826362481685120195895

theorem tailTrace_6529606 : CollatzResearch.WordTrace tailWord_6529606 prefixEnd_6529606 3352826362481685120195895 := by
  unfold tailWord_6529606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7442321749448753273964271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158769530654906736511237781 7442321749448753273964271)
  ·
    refine ⟨11163482624173129910946407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7442321749448753273964271 11163482624173129910946407)
    ·
      refine ⟨16745223936259694866419611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11163482624173129910946407 16745223936259694866419611)
      ·
        refine ⟨25117835904389542299629417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16745223936259694866419611 25117835904389542299629417)
        ·
          refine ⟨18838376928292156724722063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25117835904389542299629417 18838376928292156724722063)
          ·
            refine ⟨28257565392438235087083095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18838376928292156724722063 28257565392438235087083095)
            ·
              refine ⟨42386348088657352630624643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28257565392438235087083095 42386348088657352630624643)
              ·
                refine ⟨63579522132986028945936965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42386348088657352630624643 63579522132986028945936965)
                ·
                  refine ⟨11921160399934880427363181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63579522132986028945936965 11921160399934880427363181)
                  ·
                    refine ⟨4470435149975580160261193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11921160399934880427363181 4470435149975580160261193)
                    ·
                      refine ⟨3352826362481685120195895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4470435149975580160261193 3352826362481685120195895)
                      ·
                        rfl

theorem cell23_6529606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_6529606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529606 prefixEnd_6529606 := by exact prefixLift 6529606
  have htrace : WordTrace (prefixWord ++ tailWord_6529606) baseStart_6529606 baseEnd_6529606 := by
    simpa [prefixWord, tailWord_6529606, baseEnd_6529606] using wordTrace_append hprefix tailTrace_6529606
  have hstable : (prefixWord ++ tailWord_6529606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529606).length < 2 ^ (prefixWord ++ tailWord_6529606).sum := by decide
  have hdescent : baseEnd_6529606 < baseStart_6529606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529612 : List Nat := [2, 2, 1, 3, 1, 2, 2, 4, 2, 4]
def baseStart_6529612 : Nat := 118140960795 + 6529612 * 2 ^ 59
def prefixEnd_6529612 : Nat := 4983230072969 + 3 ^ 40 * 6529612 * 2
def baseEnd_6529612 : Nat := 1117609814455204032240289

theorem tailTrace_6529612 : CollatzResearch.WordTrace tailWord_6529612 prefixEnd_6529612 1117609814455204032240289 := by
  unfold tailWord_6529612
  simp only [CollatzResearch.WordTrace]
  refine ⟨119077257410169183895787545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158769676546892245194383393 119077257410169183895787545)
  ·
    refine ⟨89307943057626887921840659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119077257410169183895787545 89307943057626887921840659)
    ·
      refine ⟨133961914586440331882760989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89307943057626887921840659 133961914586440331882760989)
      ·
        refine ⟨50235717969915124456035371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133961914586440331882760989 50235717969915124456035371)
        ·
          refine ⟨75353576954872686684053057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50235717969915124456035371 75353576954872686684053057)
          ·
            refine ⟨56515182716154515013039793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75353576954872686684053057 56515182716154515013039793)
            ·
              refine ⟨42386387037115886259779845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56515182716154515013039793 42386387037115886259779845)
              ·
                refine ⟨7947447569459228673708721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42386387037115886259779845 7947447569459228673708721)
                ·
                  refine ⟨5960585677094421505281541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7947447569459228673708721 5960585677094421505281541)
                  ·
                    refine ⟨1117609814455204032240289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5960585677094421505281541 1117609814455204032240289)
                    ·
                      rfl

theorem cell23_6529612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_6529612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529612 prefixEnd_6529612 := by exact prefixLift 6529612
  have htrace : WordTrace (prefixWord ++ tailWord_6529612) baseStart_6529612 baseEnd_6529612 := by
    simpa [prefixWord, tailWord_6529612, baseEnd_6529612] using wordTrace_append hprefix tailTrace_6529612
  have hstable : (prefixWord ++ tailWord_6529612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529612).length < 2 ^ (prefixWord ++ tailWord_6529612).sum := by decide
  have hdescent : baseEnd_6529612 < baseStart_6529612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529669 : List Nat := [1, 3, 1, 1, 4, 2, 1, 4, 2, 1, 3]
def baseStart_6529669 : Nat := 118140960795 + 6529669 * 2 ^ 59
def prefixEnd_6529669 : Nat := 4983230072969 + 3 ^ 40 * 6529669 * 2
def baseEnd_6529669 : Nat := 3352858711762918373708105

theorem tailTrace_6529669 : CollatzResearch.WordTrace tailWord_6529669 prefixEnd_6529669 3352858711762918373708105 := by
  unfold tailWord_6529669
  simp only [CollatzResearch.WordTrace]
  refine ⟨238156593781131866526400061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158771062520754577684266707 238156593781131866526400061)
  ·
    refine ⟨89308722667924449947400023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238156593781131866526400061 89308722667924449947400023)
    ·
      refine ⟨133963084001886674921100035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89308722667924449947400023 133963084001886674921100035)
      ·
        refine ⟨200944626002830012381650053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133963084001886674921100035 200944626002830012381650053)
        ·
          refine ⟨37677117375530627321559385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200944626002830012381650053 37677117375530627321559385)
          ·
            refine ⟨28257838031647970491169539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37677117375530627321559385 28257838031647970491169539)
            ·
              refine ⟨42386757047471955736754309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28257838031647970491169539 42386757047471955736754309)
              ·
                refine ⟨7947516946400991700641433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42386757047471955736754309 7947516946400991700641433)
                ·
                  refine ⟨5960637709800743775481075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7947516946400991700641433 5960637709800743775481075)
                  ·
                    refine ⟨8940956564701115663221613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5960637709800743775481075 8940956564701115663221613)
                    ·
                      refine ⟨3352858711762918373708105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8940956564701115663221613 3352858711762918373708105)
                      ·
                        rfl

theorem cell23_6529669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 1, 3].length) (baseStart_6529669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529669 prefixEnd_6529669 := by exact prefixLift 6529669
  have htrace : WordTrace (prefixWord ++ tailWord_6529669) baseStart_6529669 baseEnd_6529669 := by
    simpa [prefixWord, tailWord_6529669, baseEnd_6529669] using wordTrace_append hprefix tailTrace_6529669
  have hstable : (prefixWord ++ tailWord_6529669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529669).length < 2 ^ (prefixWord ++ tailWord_6529669).sum := by decide
  have hdescent : baseEnd_6529669 < baseStart_6529669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529705 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 4, 2, 4]
def baseStart_6529705 : Nat := 118140960795 + 6529705 * 2 ^ 59
def prefixEnd_6529705 : Nat := 4983230072969 + 3 ^ 40 * 6529705 * 2
def baseEnd_6529705 : Nat := 3352877197066480232857939

theorem tailTrace_6529705 : CollatzResearch.WordTrace tailWord_6529705 prefixEnd_6529705 3352877197066480232857939 := by
  unfold tailWord_6529705
  simp only [CollatzResearch.WordTrace]
  refine ⟨238157906809001444674710569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158771937872667629783140379 238157906809001444674710569)
  ·
    refine ⟨178618430106751083506032927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238157906809001444674710569 178618430106751083506032927)
    ·
      refine ⟨267927645160126625259049391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178618430106751083506032927 267927645160126625259049391)
      ·
        refine ⟨401891467740189937888574087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267927645160126625259049391 401891467740189937888574087)
        ·
          refine ⟨602837201610284906832861131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401891467740189937888574087 602837201610284906832861131)
          ·
            refine ⟨904255802415427360249291697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602837201610284906832861131 904255802415427360249291697)
            ·
              refine ⟨678191851811570520186968773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 904255802415427360249291697 678191851811570520186968773)
              ·
                refine ⟨127160972214669472535056645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 678191851811570520186968773 127160972214669472535056645)
                ·
                  refine ⟨23842682290250526100323121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127160972214669472535056645 23842682290250526100323121)
                  ·
                    refine ⟨17882011717687894575242341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23842682290250526100323121 17882011717687894575242341)
                    ·
                      refine ⟨3352877197066480232857939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17882011717687894575242341 3352877197066480232857939)
                      ·
                        rfl

theorem cell23_6529705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_6529705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529705 prefixEnd_6529705 := by exact prefixLift 6529705
  have htrace : WordTrace (prefixWord ++ tailWord_6529705) baseStart_6529705 baseEnd_6529705 := by
    simpa [prefixWord, tailWord_6529705, baseEnd_6529705] using wordTrace_append hprefix tailTrace_6529705
  have hstable : (prefixWord ++ tailWord_6529705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529705).length < 2 ^ (prefixWord ++ tailWord_6529705).sum := by decide
  have hdescent : baseEnd_6529705 < baseStart_6529705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529713 : List Nat := [1, 2, 2, 6, 1, 1, 1, 3, 1, 3, 2]
def baseStart_6529713 : Nat := 118140960795 + 6529713 * 2 ^ 59
def prefixEnd_6529713 : Nat := 4983230072969 + 3 ^ 40 * 6529713 * 2
def baseEnd_6529713 : Nat := 3352881304911716201557903

theorem tailTrace_6529713 : CollatzResearch.WordTrace tailWord_6529713 prefixEnd_6529713 3352881304911716201557903 := by
  unfold tailWord_6529713
  simp only [CollatzResearch.WordTrace]
  refine ⟨238158198592972462041001793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158772132395314974694001195 238158198592972462041001793)
  ·
    refine ⟨178618648944729346530751345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238158198592972462041001793 178618648944729346530751345)
    ·
      refine ⟨133963986708547009898063509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178618648944729346530751345 133963986708547009898063509)
      ·
        refine ⟨6279561876963141088971727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 133963986708547009898063509 6279561876963141088971727)
        ·
          refine ⟨9419342815444711633457591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6279561876963141088971727 9419342815444711633457591)
          ·
            refine ⟨14129014223167067450186387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9419342815444711633457591 14129014223167067450186387)
            ·
              refine ⟨21193521334750601175279581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14129014223167067450186387 21193521334750601175279581)
              ·
                refine ⟨7947570500531475440729843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21193521334750601175279581 7947570500531475440729843)
                ·
                  refine ⟨11921355750797213161094765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7947570500531475440729843 11921355750797213161094765)
                  ·
                    refine ⟨4470508406548954935410537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11921355750797213161094765 4470508406548954935410537)
                    ·
                      refine ⟨3352881304911716201557903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4470508406548954935410537 3352881304911716201557903)
                      ·
                        rfl

theorem cell23_6529713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_6529713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529713 prefixEnd_6529713 := by exact prefixLift 6529713
  have htrace : WordTrace (prefixWord ++ tailWord_6529713) baseStart_6529713 baseEnd_6529713 := by
    simpa [prefixWord, tailWord_6529713, baseEnd_6529713] using wordTrace_append hprefix tailTrace_6529713
  have hstable : (prefixWord ++ tailWord_6529713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529713).length < 2 ^ (prefixWord ++ tailWord_6529713).sum := by decide
  have hdescent : baseEnd_6529713 < baseStart_6529713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529726 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2]
def baseStart_6529726 : Nat := 118140960795 + 6529726 * 2 ^ 59
def prefixEnd_6529726 : Nat := 4983230072969 + 3 ^ 40 * 6529726 * 2
def baseEnd_6529726 : Nat := 3352887980160224650695343

theorem tailTrace_6529726 : CollatzResearch.WordTrace tailWord_6529726 prefixEnd_6529726 3352887980160224650695343 := by
  unfold tailWord_6529726
  simp only [CollatzResearch.WordTrace]
  refine ⟨29769834092740670657653129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158772448494616910174150021 29769834092740670657653129)
  ·
    refine ⟨22327375569555502993239847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29769834092740670657653129 22327375569555502993239847)
    ·
      refine ⟨33491063354333254489859771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22327375569555502993239847 33491063354333254489859771)
      ·
        refine ⟨50236595031499881734789657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33491063354333254489859771 50236595031499881734789657)
        ·
          refine ⟨37677446273624911301092243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50236595031499881734789657 37677446273624911301092243)
          ·
            refine ⟨56516169410437366951638365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37677446273624911301092243 56516169410437366951638365)
            ·
              refine ⟨21193563528914012606864387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56516169410437366951638365 21193563528914012606864387)
              ·
                refine ⟨31790345293371018910296581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21193563528914012606864387 31790345293371018910296581)
                ·
                  refine ⟨5960689742507066045680609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31790345293371018910296581 5960689742507066045680609)
                  ·
                    refine ⟨4470517306880299534260457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5960689742507066045680609 4470517306880299534260457)
                    ·
                      refine ⟨3352887980160224650695343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4470517306880299534260457 3352887980160224650695343)
                      ·
                        rfl

theorem cell23_6529726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_6529726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529726 prefixEnd_6529726 := by exact prefixLift 6529726
  have htrace : WordTrace (prefixWord ++ tailWord_6529726) baseStart_6529726 baseEnd_6529726 := by
    simpa [prefixWord, tailWord_6529726, baseEnd_6529726] using wordTrace_append hprefix tailTrace_6529726
  have hstable : (prefixWord ++ tailWord_6529726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529726).length < 2 ^ (prefixWord ++ tailWord_6529726).sum := by decide
  have hdescent : baseEnd_6529726 < baseStart_6529726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529732 : List Nat := [2, 3, 3, 1, 1, 2, 1, 3, 7]
def baseStart_6529732 : Nat := 118140960795 + 6529732 * 2 ^ 59
def prefixEnd_6529732 : Nat := 4983230072969 + 3 ^ 40 * 6529732 * 2
def baseEnd_6529732 : Nat := 372543451227127958580035

theorem tailTrace_6529732 : CollatzResearch.WordTrace tailWord_6529732 prefixEnd_6529732 372543451227127958580035 := by
  unfold tailWord_6529732
  simp only [CollatzResearch.WordTrace]
  refine ⟨119079445789951814142971725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158772594386602418857295633 119079445789951814142971725)
  ·
    refine ⟨44654792171231930303614397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119079445789951814142971725 44654792171231930303614397)
    ·
      refine ⟨16745547064211973863855399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44654792171231930303614397 16745547064211973863855399)
      ·
        refine ⟨25118320596317960795783099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16745547064211973863855399 25118320596317960795783099)
        ·
          refine ⟨37677480894476941193674649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25118320596317960795783099 37677480894476941193674649)
          ·
            refine ⟨28258110670857705895255987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37677480894476941193674649 28258110670857705895255987)
            ·
              refine ⟨42387166006286558842883981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28258110670857705895255987 42387166006286558842883981)
              ·
                refine ⟨15895187252357459566081493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42387166006286558842883981 15895187252357459566081493)
                ·
                  refine ⟨372543451227127958580035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15895187252357459566081493 372543451227127958580035)
                  ·
                    rfl

theorem cell23_6529732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_6529732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529732 prefixEnd_6529732 := by exact prefixLift 6529732
  have htrace : WordTrace (prefixWord ++ tailWord_6529732) baseStart_6529732 baseEnd_6529732 := by
    simpa [prefixWord, tailWord_6529732, baseEnd_6529732] using wordTrace_append hprefix tailTrace_6529732
  have hstable : (prefixWord ++ tailWord_6529732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529732).length < 2 ^ (prefixWord ++ tailWord_6529732).sum := by decide
  have hdescent : baseEnd_6529732 < baseStart_6529732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529745 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 3, 7]
def baseStart_6529745 : Nat := 118140960795 + 6529745 * 2 ^ 59
def prefixEnd_6529745 : Nat := 4983230072969 + 3 ^ 40 * 6529745 * 2
def baseEnd_6529745 : Nat := 1117632578764220025452585

theorem tailTrace_6529745 : CollatzResearch.WordTrace tailWord_6529745 prefixEnd_6529745 1117632578764220025452585 := by
  unfold tailWord_6529745
  simp only [CollatzResearch.WordTrace]
  refine ⟨238159365728856531506166689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158772910485904354337444459 238159365728856531506166689)
  ·
    refine ⟨178619524296642398629625017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238159365728856531506166689 178619524296642398629625017)
    ·
      refine ⟨133964643222481798972218763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178619524296642398629625017 133964643222481798972218763)
      ·
        refine ⟨200946964833722698458328145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133964643222481798972218763 200946964833722698458328145)
        ·
          refine ⟨150710223625292023843746109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200946964833722698458328145 150710223625292023843746109)
          ·
            refine ⟨56516333859484508941404791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150710223625292023843746109 56516333859484508941404791)
            ·
              refine ⟨84774500789226763412107187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56516333859484508941404791 84774500789226763412107187)
              ·
                refine ⟨127161751183840145118160781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84774500789226763412107187 127161751183840145118160781)
                ·
                  refine ⟨47685656693940054419310293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127161751183840145118160781 47685656693940054419310293)
                  ·
                    refine ⟨1117632578764220025452585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47685656693940054419310293 1117632578764220025452585)
                    ·
                      rfl

theorem cell23_6529745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_6529745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529745 prefixEnd_6529745 := by exact prefixLift 6529745
  have htrace : WordTrace (prefixWord ++ tailWord_6529745) baseStart_6529745 baseEnd_6529745 := by
    simpa [prefixWord, tailWord_6529745, baseEnd_6529745] using wordTrace_append hprefix tailTrace_6529745
  have hstable : (prefixWord ++ tailWord_6529745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529745).length < 2 ^ (prefixWord ++ tailWord_6529745).sum := by decide
  have hdescent : baseEnd_6529745 < baseStart_6529745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529842 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_6529842 : Nat := 118140960795 + 6529842 * 2 ^ 59
def prefixEnd_6529842 : Nat := 4983230072969 + 3 ^ 40 * 6529842 * 2
def baseEnd_6529842 : Nat := 3352947543916146196844809

theorem tailTrace_6529842 : CollatzResearch.WordTrace tailWord_6529842 prefixEnd_6529842 3352947543916146196844809 := by
  unfold tailWord_6529842
  simp only [CollatzResearch.WordTrace]
  refine ⟨59540725902376279268111945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158775269073003411381631853 59540725902376279268111945)
  ·
    refine ⟨44655544426782209451083959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59540725902376279268111945 44655544426782209451083959)
    ·
      refine ⟨66983316640173314176625939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44655544426782209451083959 66983316640173314176625939)
      ·
        refine ⟨100474974960259971264938909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66983316640173314176625939 100474974960259971264938909)
        ·
          refine ⟨37678115610097489224352091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100474974960259971264938909 37678115610097489224352091)
          ·
            refine ⟨56517173415146233836528137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37678115610097489224352091 56517173415146233836528137)
            ·
              refine ⟨42387880061359675377396103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56517173415146233836528137 42387880061359675377396103)
              ·
                refine ⟨63581820092039513066094155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42387880061359675377396103 63581820092039513066094155)
                ·
                  refine ⟨95372730138059269599141233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63581820092039513066094155 95372730138059269599141233)
                  ·
                    refine ⟨71529547603544452199355925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95372730138059269599141233 71529547603544452199355925)
                    ·
                      refine ⟨3352947543916146196844809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71529547603544452199355925 3352947543916146196844809)
                      ·
                        rfl

theorem cell23_6529842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_6529842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529842 prefixEnd_6529842 := by exact prefixLift 6529842
  have htrace : WordTrace (prefixWord ++ tailWord_6529842) baseStart_6529842 baseEnd_6529842 := by
    simpa [prefixWord, tailWord_6529842, baseEnd_6529842] using wordTrace_append hprefix tailTrace_6529842
  have hstable : (prefixWord ++ tailWord_6529842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529842).length < 2 ^ (prefixWord ++ tailWord_6529842).sum := by decide
  have hdescent : baseEnd_6529842 < baseStart_6529842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529843 : List Nat := [1, 1, 1, 2, 6, 1, 4, 2, 1, 4]
def baseStart_6529843 : Nat := 118140960795 + 6529843 * 2 ^ 59
def prefixEnd_6529843 : Nat := 4983230072969 + 3 ^ 40 * 6529843 * 2
def baseEnd_6529843 : Nat := 1117649352465600230977435

theorem tailTrace_6529843 : CollatzResearch.WordTrace tailWord_6529843 prefixEnd_6529843 1117649352465600230977435 := by
  unfold tailWord_6529843
  simp only [CollatzResearch.WordTrace]
  refine ⟨238162940082501494243234183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158775293388334329495489455 238162940082501494243234183)
  ·
    refine ⟨357244410123752241364851275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238162940082501494243234183 357244410123752241364851275)
    ·
      refine ⟨535866615185628362047276913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357244410123752241364851275 535866615185628362047276913)
      ·
        refine ⟨401899961389221271535457685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535866615185628362047276913 401899961389221271535457685)
        ·
          refine ⟨18839060690119747103224579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 401899961389221271535457685 18839060690119747103224579)
          ·
            refine ⟨28258591035179620654836869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18839060690119747103224579 28258591035179620654836869)
            ·
              refine ⟨5298485819096178872781913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28258591035179620654836869 5298485819096178872781913)
              ·
                refine ⟨3973864364322134154586435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5298485819096178872781913 3973864364322134154586435)
                ·
                  refine ⟨5960796546483201231879653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3973864364322134154586435 5960796546483201231879653)
                  ·
                    refine ⟨1117649352465600230977435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5960796546483201231879653 1117649352465600230977435)
                    ·
                      rfl

theorem cell23_6529843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 1, 4].length) (baseStart_6529843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529843 prefixEnd_6529843 := by exact prefixLift 6529843
  have htrace : WordTrace (prefixWord ++ tailWord_6529843) baseStart_6529843 baseEnd_6529843 := by
    simpa [prefixWord, tailWord_6529843, baseEnd_6529843] using wordTrace_append hprefix tailTrace_6529843
  have hstable : (prefixWord ++ tailWord_6529843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529843).length < 2 ^ (prefixWord ++ tailWord_6529843).sum := by decide
  have hdescent : baseEnd_6529843 < baseStart_6529843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529859 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 1, 5, 2]
def baseStart_6529859 : Nat := 118140960795 + 6529859 * 2 ^ 59
def prefixEnd_6529859 : Nat := 4983230072969 + 3 ^ 40 * 6529859 * 2
def baseEnd_6529859 : Nat := 3352956273087272630332231

theorem tailTrace_6529859 : CollatzResearch.WordTrace tailWord_6529859 prefixEnd_6529859 3352956273087272630332231 := by
  unfold tailWord_6529859
  simp only [CollatzResearch.WordTrace]
  refine ⟨238163523650443528975816631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158775682433629019317211087 238163523650443528975816631)
  ·
    refine ⟨357245285475665293463724947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238163523650443528975816631 357245285475665293463724947)
    ·
      refine ⟨535867928213497940195587421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357245285475665293463724947 535867928213497940195587421)
      ·
        refine ⟨200950473080061727573345283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 535867928213497940195587421 200950473080061727573345283)
        ·
          refine ⟨301425709620092591360017925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200950473080061727573345283 301425709620092591360017925)
          ·
            refine ⟨56517320553767360880003361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 301425709620092591360017925 56517320553767360880003361)
            ·
              refine ⟨42387990415325520660002521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56517320553767360880003361 42387990415325520660002521)
              ·
                refine ⟨31790992811494140495001891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42387990415325520660002521 31790992811494140495001891)
                ·
                  refine ⟨47686489217241210742502837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31790992811494140495001891 47686489217241210742502837)
                  ·
                    refine ⟨4470608364116363507109641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47686489217241210742502837 4470608364116363507109641)
                    ·
                      refine ⟨3352956273087272630332231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4470608364116363507109641 3352956273087272630332231)
                      ·
                        rfl

theorem cell23_6529859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 5, 2].length) (baseStart_6529859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529859 prefixEnd_6529859 := by exact prefixLift 6529859
  have htrace : WordTrace (prefixWord ++ tailWord_6529859) baseStart_6529859 baseEnd_6529859 := by
    simpa [prefixWord, tailWord_6529859, baseEnd_6529859] using wordTrace_append hprefix tailTrace_6529859
  have hstable : (prefixWord ++ tailWord_6529859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529859).length < 2 ^ (prefixWord ++ tailWord_6529859).sum := by decide
  have hdescent : baseEnd_6529859 < baseStart_6529859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529909 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_6529909 : Nat := 118140960795 + 6529909 * 2 ^ 59
def prefixEnd_6529909 : Nat := 4983230072969 + 3 ^ 40 * 6529909 * 2
def baseEnd_6529909 : Nat := 3352981947119997434707001

theorem tailTrace_6529909 : CollatzResearch.WordTrace tailWord_6529909 prefixEnd_6529909 3352981947119997434707001 := by
  unfold tailWord_6529909
  simp only [CollatzResearch.WordTrace]
  refine ⟨238165347300262387515136781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158776898200174925010091187 238165347300262387515136781)
  ·
    refine ⟨89312005237598395318176293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238165347300262387515136781 89312005237598395318176293)
    ·
      refine ⟨16746000982049699122158055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89312005237598395318176293 16746000982049699122158055)
      ·
        refine ⟨25119001473074548683237083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16746000982049699122158055 25119001473074548683237083)
        ·
          refine ⟨37678502209611823024855625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25119001473074548683237083 37678502209611823024855625)
          ·
            refine ⟨28258876657208867268641719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37678502209611823024855625 28258876657208867268641719)
            ·
              refine ⟨42388314985813300902962579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28258876657208867268641719 42388314985813300902962579)
              ·
                refine ⟨63582472478719951354443869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42388314985813300902962579 63582472478719951354443869)
                ·
                  refine ⟨23843427179519981757916451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63582472478719951354443869 23843427179519981757916451)
                  ·
                    refine ⟨35765140769279972636874677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23843427179519981757916451 35765140769279972636874677)
                    ·
                      refine ⟨3352981947119997434707001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35765140769279972636874677 3352981947119997434707001)
                      ·
                        rfl

theorem cell23_6529909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_6529909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529909 prefixEnd_6529909 := by exact prefixLift 6529909
  have htrace : WordTrace (prefixWord ++ tailWord_6529909) baseStart_6529909 baseEnd_6529909 := by
    simpa [prefixWord, tailWord_6529909, baseEnd_6529909] using wordTrace_append hprefix tailTrace_6529909
  have hstable : (prefixWord ++ tailWord_6529909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529909).length < 2 ^ (prefixWord ++ tailWord_6529909).sum := by decide
  have hdescent : baseEnd_6529909 < baseStart_6529909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529919 : List Nat := [1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 4]
def baseStart_6529919 : Nat := 118140960795 + 6529919 * 2 ^ 59
def prefixEnd_6529919 : Nat := 4983230072969 + 3 ^ 40 * 6529919 * 2
def baseEnd_6529919 : Nat := 3352987081926542395581955

theorem tailTrace_6529919 : CollatzResearch.WordTrace tailWord_6529919 prefixEnd_6529919 3352987081926542395581955 := by
  unfold tailWord_6529919
  simp only [CollatzResearch.WordTrace]
  refine ⟨238165712030226159223000811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158777141353484106148667207 238165712030226159223000811)
  ·
    refine ⟨357248568045339238834501217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238165712030226159223000811 357248568045339238834501217)
    ·
      refine ⟨267936426034004429125875913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357248568045339238834501217 267936426034004429125875913)
      ·
        refine ⟨200952319525503321844406935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267936426034004429125875913 200952319525503321844406935)
        ·
          refine ⟨301428479288254982766610403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200952319525503321844406935 301428479288254982766610403)
          ·
            refine ⟨452142718932382474149915605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301428479288254982766610403 452142718932382474149915605)
            ·
              refine ⟨10597094974977714237888647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 452142718932382474149915605 10597094974977714237888647)
              ·
                refine ⟨15895642462466571356832971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10597094974977714237888647 15895642462466571356832971)
                ·
                  refine ⟨23843463693699857035249457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15895642462466571356832971 23843463693699857035249457)
                  ·
                    refine ⟨17882597770274892776437093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23843463693699857035249457 17882597770274892776437093)
                    ·
                      refine ⟨3352987081926542395581955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17882597770274892776437093 3352987081926542395581955)
                      ·
                        rfl

theorem cell23_6529919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_6529919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529919 prefixEnd_6529919 := by exact prefixLift 6529919
  have htrace : WordTrace (prefixWord ++ tailWord_6529919) baseStart_6529919 baseEnd_6529919 := by
    simpa [prefixWord, tailWord_6529919, baseEnd_6529919] using wordTrace_append hprefix tailTrace_6529919
  have hstable : (prefixWord ++ tailWord_6529919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529919).length < 2 ^ (prefixWord ++ tailWord_6529919).sum := by decide
  have hdescent : baseEnd_6529919 < baseStart_6529919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529929 : List Nat := [1, 2, 1, 1, 5, 2, 4, 7]
def baseStart_6529929 : Nat := 118140960795 + 6529929 * 2 ^ 59
def prefixEnd_6529929 : Nat := 4983230072969 + 3 ^ 40 * 6529929 * 2
def baseEnd_6529929 : Nat := 124184896916040272461367

theorem tailTrace_6529929 : CollatzResearch.WordTrace tailWord_6529929 prefixEnd_6529929 124184896916040272461367 := by
  unfold tailWord_6529929
  simp only [CollatzResearch.WordTrace]
  refine ⟨238166076760189930930864841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158777384506793287287243227 238166076760189930930864841)
  ·
    refine ⟨178624557570142448198148631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238166076760189930930864841 178624557570142448198148631)
    ·
      refine ⟨267936836355213672297222947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178624557570142448198148631 267936836355213672297222947)
      ·
        refine ⟨401905254532820508445834421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267936836355213672297222947 401905254532820508445834421)
        ·
          refine ⟨37678617612451922666796977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 401905254532820508445834421 37678617612451922666796977)
          ·
            refine ⟨28258963209338942000097733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37678617612451922666796977 28258963209338942000097733)
            ·
              refine ⟨5298555601751051625018325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28258963209338942000097733 5298555601751051625018325)
              ·
                refine ⟨124184896916040272461367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5298555601751051625018325 124184896916040272461367)
                ·
                  rfl

theorem cell23_6529929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 7].length) (baseStart_6529929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529929 prefixEnd_6529929 := by exact prefixLift 6529929
  have htrace : WordTrace (prefixWord ++ tailWord_6529929) baseStart_6529929 baseEnd_6529929 := by
    simpa [prefixWord, tailWord_6529929, baseEnd_6529929] using wordTrace_append hprefix tailTrace_6529929
  have hstable : (prefixWord ++ tailWord_6529929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529929).length < 2 ^ (prefixWord ++ tailWord_6529929).sum := by decide
  have hdescent : baseEnd_6529929 < baseStart_6529929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529946 : List Nat := [3, 1, 1, 4, 4, 1, 9]
def baseStart_6529946 : Nat := 118140960795 + 6529946 * 2 ^ 59
def prefixEnd_6529946 : Nat := 4983230072969 + 3 ^ 40 * 6529946 * 2
def baseEnd_6529946 : Nat := 41395073406224861604251

theorem tailTrace_6529946 : CollatzResearch.WordTrace tailWord_6529946 prefixEnd_6529946 41395073406224861604251 := by
  unfold tailWord_6529946
  simp only [CollatzResearch.WordTrace]
  refine ⟨59541674200282085708558423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158777797867418895222822461 59541674200282085708558423)
  ·
    refine ⟨89312511300423128562837635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59541674200282085708558423 89312511300423128562837635)
    ·
      refine ⟨133968766950634692844256453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89312511300423128562837635 133968766950634692844256453)
      ·
        refine ⟨25119143803244004908298085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133968766950634692844256453 25119143803244004908298085)
        ·
          refine ⟨4709839463108250920305891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25119143803244004908298085 4709839463108250920305891)
          ·
            refine ⟨7064759194662376380458837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4709839463108250920305891 7064759194662376380458837)
            ·
              refine ⟨41395073406224861604251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7064759194662376380458837 41395073406224861604251)
              ·
                rfl

theorem cell23_6529946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 9].length) (baseStart_6529946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529946 prefixEnd_6529946 := by exact prefixLift 6529946
  have htrace : WordTrace (prefixWord ++ tailWord_6529946) baseStart_6529946 baseEnd_6529946 := by
    simpa [prefixWord, tailWord_6529946, baseEnd_6529946] using wordTrace_append hprefix tailTrace_6529946
  have hstable : (prefixWord ++ tailWord_6529946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529946).length < 2 ^ (prefixWord ++ tailWord_6529946).sum := by decide
  have hdescent : baseEnd_6529946 < baseStart_6529946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529956 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 4, 1, 3]
def baseStart_6529956 : Nat := 118140960795 + 6529956 * 2 ^ 59
def prefixEnd_6529956 : Nat := 4983230072969 + 3 ^ 40 * 6529956 * 2
def baseEnd_6529956 : Nat := 3353006080710758750819285

theorem tailTrace_6529956 : CollatzResearch.WordTrace tailWord_6529956 prefixEnd_6529956 3353006080710758750819285 := by
  unfold tailWord_6529956
  simp only [CollatzResearch.WordTrace]
  refine ⟨119083530765546057271048861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158778041020728076361398481 119083530765546057271048861)
  ·
    refine ⟨44656324037079771476643323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119083530765546057271048861 44656324037079771476643323)
    ·
      refine ⟨66984486055619657214964985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44656324037079771476643323 66984486055619657214964985)
      ·
        refine ⟨50238364541714742911223739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66984486055619657214964985 50238364541714742911223739)
        ·
          refine ⟨75357546812572114366835609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50238364541714742911223739 75357546812572114366835609)
          ·
            refine ⟨56518160109429085775126707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75357546812572114366835609 56518160109429085775126707)
            ·
              refine ⟨84777240164143628662690061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56518160109429085775126707 84777240164143628662690061)
              ·
                refine ⟨31791465061553860748508773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84777240164143628662690061 31791465061553860748508773)
                ·
                  refine ⟨5960899699041348890345395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31791465061553860748508773 5960899699041348890345395)
                  ·
                    refine ⟨8941349548562023335518093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5960899699041348890345395 8941349548562023335518093)
                    ·
                      refine ⟨3353006080710758750819285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8941349548562023335518093 3353006080710758750819285)
                      ·
                        rfl

theorem cell23_6529956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_6529956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529956 prefixEnd_6529956 := by exact prefixLift 6529956
  have htrace : WordTrace (prefixWord ++ tailWord_6529956) baseStart_6529956 baseEnd_6529956 := by
    simpa [prefixWord, tailWord_6529956, baseEnd_6529956] using wordTrace_append hprefix tailTrace_6529956
  have hstable : (prefixWord ++ tailWord_6529956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529956).length < 2 ^ (prefixWord ++ tailWord_6529956).sum := by decide
  have hdescent : baseEnd_6529956 < baseStart_6529956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529973 : List Nat := [1, 3, 3, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_6529973 : Nat := 118140960795 + 6529973 * 2 ^ 59
def prefixEnd_6529973 : Nat := 4983230072969 + 3 ^ 40 * 6529973 * 2
def baseEnd_6529973 : Nat := 3353014809881885184306707

theorem tailTrace_6529973 : CollatzResearch.WordTrace tailWord_6529973 prefixEnd_6529973 3353014809881885184306707 := by
  unfold tailWord_6529973
  simp only [CollatzResearch.WordTrace]
  refine ⟨238167681572030526445466573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158778454381353684296977715 238167681572030526445466573)
  ·
    refine ⟨89312880589511447417049965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238167681572030526445466573 89312880589511447417049965)
    ·
      refine ⟨33492330221066792781393737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89312880589511447417049965 33492330221066792781393737)
      ·
        refine ⟨25119247665800094586045303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33492330221066792781393737 25119247665800094586045303)
        ·
          refine ⟨37678871498700141879067955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25119247665800094586045303 37678871498700141879067955)
          ·
            refine ⟨56518307248050212818601933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37678871498700141879067955 56518307248050212818601933)
            ·
              refine ⟨21194365218018829806975725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56518307248050212818601933 21194365218018829806975725)
              ·
                refine ⟨7947886956757061177615897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21194365218018829806975725 7947886956757061177615897)
                ·
                  refine ⟨5960915217567795883211923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7947886956757061177615897 5960915217567795883211923)
                  ·
                    refine ⟨8941372826351693824817885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5960915217567795883211923 8941372826351693824817885)
                    ·
                      refine ⟨3353014809881885184306707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8941372826351693824817885 3353014809881885184306707)
                      ·
                        rfl

theorem cell23_6529973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_6529973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529973 prefixEnd_6529973 := by exact prefixLift 6529973
  have htrace : WordTrace (prefixWord ++ tailWord_6529973) baseStart_6529973 baseEnd_6529973 := by
    simpa [prefixWord, tailWord_6529973, baseEnd_6529973] using wordTrace_append hprefix tailTrace_6529973
  have hstable : (prefixWord ++ tailWord_6529973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529973).length < 2 ^ (prefixWord ++ tailWord_6529973).sum := by decide
  have hdescent : baseEnd_6529973 < baseStart_6529973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529974 : List Nat := [5, 1, 4, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_6529974 : Nat := 118140960795 + 6529974 * 2 ^ 59
def prefixEnd_6529974 : Nat := 4983230072969 + 3 ^ 40 * 6529974 * 2
def baseEnd_6529974 : Nat := 3353015323362539680394203

theorem tailTrace_6529974 : CollatzResearch.WordTrace tailWord_6529974 prefixEnd_6529974 3353015323362539680394203 := by
  unfold tailWord_6529974
  simp only [CollatzResearch.WordTrace]
  refine ⟨14885482377814181476015811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158778478696684602410835317 14885482377814181476015811)
  ·
    refine ⟨22328223566721272214023717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14885482377814181476015811 22328223566721272214023717)
    ·
      refine ⟨4186541918760238540129447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22328223566721272214023717 4186541918760238540129447)
      ·
        refine ⟨6279812878140357810194171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4186541918760238540129447 6279812878140357810194171)
        ·
          refine ⟨9419719317210536715291257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6279812878140357810194171 9419719317210536715291257)
          ·
            refine ⟨7064789487907902536468443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9419719317210536715291257 7064789487907902536468443)
            ·
              refine ⟨10597184231861853804702665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7064789487907902536468443 10597184231861853804702665)
              ·
                refine ⟨7947888173896390353526999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10597184231861853804702665 7947888173896390353526999)
                ·
                  refine ⟨11921832260844585530290499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7947888173896390353526999 11921832260844585530290499)
                  ·
                    refine ⟨17882748391266878295435749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11921832260844585530290499 17882748391266878295435749)
                    ·
                      refine ⟨3353015323362539680394203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17882748391266878295435749 3353015323362539680394203)
                      ·
                        rfl

theorem cell23_6529974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_6529974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529974 prefixEnd_6529974 := by exact prefixLift 6529974
  have htrace : WordTrace (prefixWord ++ tailWord_6529974) baseStart_6529974 baseEnd_6529974 := by
    simpa [prefixWord, tailWord_6529974, baseEnd_6529974] using wordTrace_append hprefix tailTrace_6529974
  have hstable : (prefixWord ++ tailWord_6529974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529974).length < 2 ^ (prefixWord ++ tailWord_6529974).sum := by decide
  have hdescent : baseEnd_6529974 < baseStart_6529974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6529999 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 5]
def baseStart_6529999 : Nat := 118140960795 + 6529999 * 2 ^ 59
def prefixEnd_6529999 : Nat := 4983230072969 + 3 ^ 40 * 6529999 * 2
def baseEnd_6529999 : Nat := 3353028160378902082581587

theorem tailTrace_6529999 : CollatzResearch.WordTrace tailWord_6529999 prefixEnd_6529999 3353028160378902082581587 := by
  unfold tailWord_6529999
  simp only [CollatzResearch.WordTrace]
  refine ⟨238168629869936332885913051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158779086579957555257275367 238168629869936332885913051)
  ·
    refine ⟨357252944804904499328869577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238168629869936332885913051 357252944804904499328869577)
    ·
      refine ⟨267939708603678374496652183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357252944804904499328869577 267939708603678374496652183)
      ·
        refine ⟨401909562905517561744978275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267939708603678374496652183 401909562905517561744978275)
        ·
          refine ⟨602864344358276342617467413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401909562905517561744978275 602864344358276342617467413)
          ·
            refine ⟨28259266141794203560193785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 602864344358276342617467413 28259266141794203560193785)
            ·
              refine ⟨21194449606345652670145339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28259266141794203560193785 21194449606345652670145339)
              ·
                refine ⟨31791674409518479005218009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21194449606345652670145339 31791674409518479005218009)
                ·
                  refine ⟨23843755807138859253913507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31791674409518479005218009 23843755807138859253913507)
                  ·
                    refine ⟨35765633710708288880870261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23843755807138859253913507 35765633710708288880870261)
                    ·
                      refine ⟨3353028160378902082581587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35765633710708288880870261 3353028160378902082581587)
                      ·
                        rfl

theorem cell23_6529999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_6529999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6529999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6529999 prefixEnd_6529999 := by exact prefixLift 6529999
  have htrace : WordTrace (prefixWord ++ tailWord_6529999) baseStart_6529999 baseEnd_6529999 := by
    simpa [prefixWord, tailWord_6529999, baseEnd_6529999] using wordTrace_append hprefix tailTrace_6529999
  have hstable : (prefixWord ++ tailWord_6529999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6529999).length < 2 ^ (prefixWord ++ tailWord_6529999).sum := by decide
  have hdescent : baseEnd_6529999 < baseStart_6529999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6529999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530019 : List Nat := [1, 1, 1, 6, 1, 1, 2, 3, 7]
def baseStart_6530019 : Nat := 118140960795 + 6530019 * 2 ^ 59
def prefixEnd_6530019 : Nat := 4983230072969 + 3 ^ 40 * 6530019 * 2
def baseEnd_6530019 : Nat := 372559825554665778259055

theorem tailTrace_6530019 : CollatzResearch.WordTrace tailWord_6530019 prefixEnd_6530019 372559825554665778259055 := by
  unfold tailWord_6530019
  simp only [CollatzResearch.WordTrace]
  refine ⟨238169359329863876301641111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158779572886575917534427407 238169359329863876301641111)
  ·
    refine ⟨357254038994795814452461667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238169359329863876301641111 357254038994795814452461667)
    ·
      refine ⟨535881058492193721678692501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357254038994795814452461667 535881058492193721678692501)
      ·
        refine ⟨25119424616821580703688711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 535881058492193721678692501 25119424616821580703688711)
        ·
          refine ⟨37679136925232371055533067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25119424616821580703688711 37679136925232371055533067)
          ·
            refine ⟨56518705387848556583299601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37679136925232371055533067 56518705387848556583299601)
            ·
              refine ⟨42389029040886417437474701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56518705387848556583299601 42389029040886417437474701)
              ·
                refine ⟨15895885890332406539053013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42389029040886417437474701 15895885890332406539053013)
                ·
                  refine ⟨372559825554665778259055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15895885890332406539053013 372559825554665778259055)
                  ·
                    rfl

theorem cell23_6530019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 7].length) (baseStart_6530019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530019 prefixEnd_6530019 := by exact prefixLift 6530019
  have htrace : WordTrace (prefixWord ++ tailWord_6530019) baseStart_6530019 baseEnd_6530019 := by
    simpa [prefixWord, tailWord_6530019, baseEnd_6530019] using wordTrace_append hprefix tailTrace_6530019
  have hstable : (prefixWord ++ tailWord_6530019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530019).length < 2 ^ (prefixWord ++ tailWord_6530019).sum := by decide
  have hdescent : baseEnd_6530019 < baseStart_6530019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530026 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_6530026 : Nat := 118140960795 + 6530026 * 2 ^ 59
def prefixEnd_6530026 : Nat := 4983230072969 + 3 ^ 40 * 6530026 * 2
def baseEnd_6530026 : Nat := 3353042024356573476943963

theorem tailTrace_6530026 : CollatzResearch.WordTrace tailWord_6530026 prefixEnd_6530026 3353042024356573476943963 := by
  unfold tailWord_6530026
  simp only [CollatzResearch.WordTrace]
  refine ⟨59542403660209629124286483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158779743093892344331430621 59542403660209629124286483)
  ·
    refine ⟨89313605490314443686429725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59542403660209629124286483 89313605490314443686429725)
    ·
      refine ⟨33492602058867916382411147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89313605490314443686429725 33492602058867916382411147)
      ·
        refine ⟨50238903088301874573616721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33492602058867916382411147 50238903088301874573616721)
        ·
          refine ⟨37679177316226405930212541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50238903088301874573616721 37679177316226405930212541)
          ·
            refine ⟨14129691493584902223829703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37679177316226405930212541 14129691493584902223829703)
            ·
              refine ⟨21194537240377353335744555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14129691493584902223829703 21194537240377353335744555)
              ·
                refine ⟨31791805860566030003616833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21194537240377353335744555 31791805860566030003616833)
                ·
                  refine ⟨23843854395424522502712625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31791805860566030003616833 23843854395424522502712625)
                  ·
                    refine ⟨17882890796568391877034469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23843854395424522502712625 17882890796568391877034469)
                    ·
                      refine ⟨3353042024356573476943963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17882890796568391877034469 3353042024356573476943963)
                      ·
                        rfl

theorem cell23_6530026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_6530026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530026 prefixEnd_6530026 := by exact prefixLift 6530026
  have htrace : WordTrace (prefixWord ++ tailWord_6530026) baseStart_6530026 baseEnd_6530026 := by
    simpa [prefixWord, tailWord_6530026, baseEnd_6530026] using wordTrace_append hprefix tailTrace_6530026
  have hstable : (prefixWord ++ tailWord_6530026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530026).length < 2 ^ (prefixWord ++ tailWord_6530026).sum := by decide
  have hdescent : baseEnd_6530026 < baseStart_6530026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530030 : List Nat := [4, 1, 2, 1, 4, 1, 2, 1, 1, 4, 2]
def baseStart_6530030 : Nat := 118140960795 + 6530030 * 2 ^ 59
def prefixEnd_6530030 : Nat := 4983230072969 + 3 ^ 40 * 6530030 * 2
def baseEnd_6530030 : Nat := 3353044078279191461293945

theorem tailTrace_6530030 : CollatzResearch.WordTrace tailWord_6530030 prefixEnd_6530030 3353044078279191461293945 := by
  unfold tailWord_6530030
  simp only [CollatzResearch.WordTrace]
  refine ⟨29771220066603003147536443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158779840355216016786861029 29771220066603003147536443)
  ·
    refine ⟨44656830099904504721304665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29771220066603003147536443 44656830099904504721304665)
    ·
      refine ⟨33492622574928378540978499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44656830099904504721304665 33492622574928378540978499)
      ·
        refine ⟨50238933862392567811467749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33492622574928378540978499 50238933862392567811467749)
        ·
          refine ⟨9419800099198606464650203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50238933862392567811467749 9419800099198606464650203)
          ·
            refine ⟨14129700148797909696975305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9419800099198606464650203 14129700148797909696975305)
            ·
              refine ⟨10597275111598432272731479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14129700148797909696975305 10597275111598432272731479)
              ·
                refine ⟨15895912667397648409097219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10597275111598432272731479 15895912667397648409097219)
                ·
                  refine ⟨23843869001096472613645829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15895912667397648409097219 23843869001096472613645829)
                  ·
                    refine ⟨4470725437705588615058593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23843869001096472613645829 4470725437705588615058593)
                    ·
                      refine ⟨3353044078279191461293945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4470725437705588615058593 3353044078279191461293945)
                      ·
                        rfl

theorem cell23_6530030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_6530030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530030 prefixEnd_6530030 := by exact prefixLift 6530030
  have htrace : WordTrace (prefixWord ++ tailWord_6530030) baseStart_6530030 baseEnd_6530030 := by
    simpa [prefixWord, tailWord_6530030, baseEnd_6530030] using wordTrace_append hprefix tailTrace_6530030
  have hstable : (prefixWord ++ tailWord_6530030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530030).length < 2 ^ (prefixWord ++ tailWord_6530030).sum := by decide
  have hdescent : baseEnd_6530030 < baseStart_6530030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530096 : List Nat := [2, 1, 1, 1, 2, 4, 1, 4, 3, 4]
def baseStart_6530096 : Nat := 118140960795 + 6530096 * 2 ^ 59
def prefixEnd_6530096 : Nat := 4983230072969 + 3 ^ 40 * 6530096 * 2
def baseEnd_6530096 : Nat := 1117692656000796067689547

theorem tailTrace_6530096 : CollatzResearch.WordTrace tailWord_6530096 prefixEnd_6530096 1117692656000796067689547 := by
  unfold tailWord_6530096
  simp only [CollatzResearch.WordTrace]
  refine ⟨119086083875292459226097071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158781445167056612301462761 119086083875292459226097071)
  ·
    refine ⟨178629125812938688839145607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119086083875292459226097071 178629125812938688839145607)
    ·
      refine ⟨267943688719408033258718411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178629125812938688839145607 267943688719408033258718411)
      ·
        refine ⟨401915533079112049888077617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267943688719408033258718411 401915533079112049888077617)
        ·
          refine ⟨301436649809334037416058213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401915533079112049888077617 301436649809334037416058213)
          ·
            refine ⟨56519371839250132015510915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 301436649809334037416058213 56519371839250132015510915)
            ·
              refine ⟨84779057758875198023266373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56519371839250132015510915 84779057758875198023266373)
              ·
                refine ⟨15896073329789099629362445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84779057758875198023266373 15896073329789099629362445)
                ·
                  refine ⟨5961027498670912361010917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15896073329789099629362445 5961027498670912361010917)
                  ·
                    refine ⟨1117692656000796067689547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5961027498670912361010917 1117692656000796067689547)
                    ·
                      rfl

theorem cell23_6530096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 3, 4].length) (baseStart_6530096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530096 prefixEnd_6530096 := by exact prefixLift 6530096
  have htrace : WordTrace (prefixWord ++ tailWord_6530096) baseStart_6530096 baseEnd_6530096 := by
    simpa [prefixWord, tailWord_6530096, baseEnd_6530096] using wordTrace_append hprefix tailTrace_6530096
  have hstable : (prefixWord ++ tailWord_6530096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530096).length < 2 ^ (prefixWord ++ tailWord_6530096).sum := by decide
  have hdescent : baseEnd_6530096 < baseStart_6530096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530099 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 4]
def baseStart_6530099 : Nat := 118140960795 + 6530099 * 2 ^ 59
def prefixEnd_6530099 : Nat := 4983230072969 + 3 ^ 40 * 6530099 * 2
def baseEnd_6530099 : Nat := 3353079508444351691331127

theorem tailTrace_6530099 : CollatzResearch.WordTrace tailWord_6530099 prefixEnd_6530099 3353079508444351691331127 := by
  unfold tailWord_6530099
  simp only [CollatzResearch.WordTrace]
  refine ⟨238172277169574049964553351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158781518113049366643035567 238172277169574049964553351)
  ·
    refine ⟨357258415754361074946830027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238172277169574049964553351 357258415754361074946830027)
    ·
      refine ⟨535887623631541612420245041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357258415754361074946830027 535887623631541612420245041)
      ·
        refine ⟨401915717723656209315183781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535887623631541612420245041 401915717723656209315183781)
        ·
          refine ⟨75359197073185539246596959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 401915717723656209315183781 75359197073185539246596959)
          ·
            refine ⟨113038795609778308869895439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75359197073185539246596959 113038795609778308869895439)
            ·
              refine ⟨169558193414667463304843159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113038795609778308869895439 169558193414667463304843159)
              ·
                refine ⟨254337290122001194957264739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169558193414667463304843159 254337290122001194957264739)
                ·
                  refine ⟨381505935183001792435897109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254337290122001194957264739 381505935183001792435897109)
                  ·
                    refine ⟨17883090711703209020432677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 381505935183001792435897109 17883090711703209020432677)
                    ·
                      refine ⟨3353079508444351691331127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17883090711703209020432677 3353079508444351691331127)
                      ·
                        rfl

theorem cell23_6530099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_6530099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530099 prefixEnd_6530099 := by exact prefixLift 6530099
  have htrace : WordTrace (prefixWord ++ tailWord_6530099) baseStart_6530099 baseEnd_6530099 := by
    simpa [prefixWord, tailWord_6530099, baseEnd_6530099] using wordTrace_append hprefix tailTrace_6530099
  have hstable : (prefixWord ++ tailWord_6530099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530099).length < 2 ^ (prefixWord ++ tailWord_6530099).sum := by decide
  have hdescent : baseEnd_6530099 < baseStart_6530099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530106 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3]
def baseStart_6530106 : Nat := 118140960795 + 6530106 * 2 ^ 59
def prefixEnd_6530106 : Nat := 4983230072969 + 3 ^ 40 * 6530106 * 2
def baseEnd_6530106 : Nat := 3353083102808933163943595

theorem tailTrace_6530106 : CollatzResearch.WordTrace tailWord_6530106 prefixEnd_6530106 3353083102808933163943595 := by
  unfold tailWord_6530106
  simp only [CollatzResearch.WordTrace]
  refine ⟨59543133120137172540014543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158781688320365793440038781 59543133120137172540014543)
  ·
    refine ⟨89314699680205758810021815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59543133120137172540014543 89314699680205758810021815)
    ·
      refine ⟨133972049520308638215032723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89314699680205758810021815 133972049520308638215032723)
      ·
        refine ⟨200958074280462957322549085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133972049520308638215032723 200958074280462957322549085)
        ·
          refine ⟨75359277855173608995955907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200958074280462957322549085 75359277855173608995955907)
          ·
            refine ⟨113038916782760413493933861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75359277855173608995955907 113038916782760413493933861)
            ·
              refine ⟨21194796896767577530112599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113038916782760413493933861 21194796896767577530112599)
              ·
                refine ⟨31792195345151366295168899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21194796896767577530112599 31792195345151366295168899)
                ·
                  refine ⟨47688293017727049442753349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31792195345151366295168899 47688293017727049442753349)
                  ·
                    refine ⟨8941554940823821770516253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47688293017727049442753349 8941554940823821770516253)
                    ·
                      refine ⟨3353083102808933163943595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8941554940823821770516253 3353083102808933163943595)
                      ·
                        rfl

theorem cell23_6530106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_6530106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530106 prefixEnd_6530106 := by exact prefixLift 6530106
  have htrace : WordTrace (prefixWord ++ tailWord_6530106) baseStart_6530106 baseEnd_6530106 := by
    simpa [prefixWord, tailWord_6530106, baseEnd_6530106] using wordTrace_append hprefix tailTrace_6530106
  have hstable : (prefixWord ++ tailWord_6530106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530106).length < 2 ^ (prefixWord ++ tailWord_6530106).sum := by decide
  have hdescent : baseEnd_6530106 < baseStart_6530106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530126 : List Nat := [4, 1, 1, 1, 1, 3, 2, 4, 6]
def baseStart_6530126 : Nat := 118140960795 + 6530126 * 2 ^ 59
def prefixEnd_6530126 : Nat := 4983230072969 + 3 ^ 40 * 6530126 * 2
def baseEnd_6530126 : Nat := 372565930269113676188167

theorem tailTrace_6530126 : CollatzResearch.WordTrace tailWord_6530126 prefixEnd_6530126 372565930269113676188167 := by
  unfold tailWord_6530126
  simp only [CollatzResearch.WordTrace]
  refine ⟨29771657742559529196973279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158782174626984155717190821 29771657742559529196973279)
  ·
    refine ⟨44657486613839293795459919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29771657742559529196973279 44657486613839293795459919)
    ·
      refine ⟨66986229920758940693189879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44657486613839293795459919 66986229920758940693189879)
      ·
        refine ⟨100479344881138411039784819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66986229920758940693189879 100479344881138411039784819)
        ·
          refine ⟨150719017321707616559677229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100479344881138411039784819 150719017321707616559677229)
          ·
            refine ⟨56519631495640356209878961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150719017321707616559677229 56519631495640356209878961)
            ·
              refine ⟨42389723621730267157409221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56519631495640356209878961 42389723621730267157409221)
              ·
                refine ⟨7948073179074425092014229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42389723621730267157409221 7948073179074425092014229)
                ·
                  refine ⟨372565930269113676188167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7948073179074425092014229 372565930269113676188167)
                  ·
                    rfl

theorem cell23_6530126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_6530126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530126 prefixEnd_6530126 := by exact prefixLift 6530126
  have htrace : WordTrace (prefixWord ++ tailWord_6530126) baseStart_6530126 baseEnd_6530126 := by
    simpa [prefixWord, tailWord_6530126, baseEnd_6530126] using wordTrace_append hprefix tailTrace_6530126
  have hstable : (prefixWord ++ tailWord_6530126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530126).length < 2 ^ (prefixWord ++ tailWord_6530126).sum := by decide
  have hdescent : baseEnd_6530126 < baseStart_6530126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530129 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 8]
def baseStart_6530129 : Nat := 118140960795 + 6530129 * 2 ^ 59
def prefixEnd_6530129 : Nat := 4983230072969 + 3 ^ 40 * 6530129 * 2
def baseEnd_6530129 : Nat := 3353094912863986573955989

theorem tailTrace_6530129 : CollatzResearch.WordTrace tailWord_6530129 prefixEnd_6530129 3353094912863986573955989 := by
  unfold tailWord_6530129
  simp only [CollatzResearch.WordTrace]
  refine ⟨238173371359465365088145441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158782247572976910058763627 238173371359465365088145441)
  ·
    refine ⟨178630028519599023816109081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238173371359465365088145441 178630028519599023816109081)
    ·
      refine ⟨133972521389699267862081811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178630028519599023816109081 133972521389699267862081811)
      ·
        refine ⟨200958782084548901793122717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133972521389699267862081811 200958782084548901793122717)
        ·
          refine ⟨75359543281705838172421019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200958782084548901793122717 75359543281705838172421019)
          ·
            refine ⟨113039314922558757258631529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75359543281705838172421019 113039314922558757258631529)
            ·
              refine ⟨84779486191919067943973647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113039314922558757258631529 84779486191919067943973647)
              ·
                refine ⟨127169229287878601915960471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84779486191919067943973647 127169229287878601915960471)
                ·
                  refine ⟨190753843931817902873940707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127169229287878601915960471 190753843931817902873940707)
                  ·
                    refine ⟨286130765897726854310911061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 190753843931817902873940707 286130765897726854310911061)
                    ·
                      refine ⟨3353094912863986573955989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 286130765897726854310911061 3353094912863986573955989)
                      ·
                        rfl

theorem cell23_6530129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_6530129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530129 prefixEnd_6530129 := by exact prefixLift 6530129
  have htrace : WordTrace (prefixWord ++ tailWord_6530129) baseStart_6530129 baseEnd_6530129 := by
    simpa [prefixWord, tailWord_6530129, baseEnd_6530129] using wordTrace_append hprefix tailTrace_6530129
  have hstable : (prefixWord ++ tailWord_6530129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530129).length < 2 ^ (prefixWord ++ tailWord_6530129).sum := by decide
  have hdescent : baseEnd_6530129 < baseStart_6530129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530130 : List Nat := [3, 2, 2, 1, 3, 3, 1, 1, 3, 4]
def baseStart_6530130 : Nat := 118140960795 + 6530130 * 2 ^ 59
def prefixEnd_6530130 : Nat := 4983230072969 + 3 ^ 40 * 6530130 * 2
def baseEnd_6530130 : Nat := 1117698475448213690014495

theorem tailTrace_6530130 : CollatzResearch.WordTrace tailWord_6530130 prefixEnd_6530130 1117698475448213690014495 := by
  unfold tailWord_6530130
  simp only [CollatzResearch.WordTrace]
  refine ⟨59543351958115435564732961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158782271888307828172621229 59543351958115435564732961)
  ·
    refine ⟨44657513968586576673549721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59543351958115435564732961 44657513968586576673549721)
    ·
      refine ⟨33493135476439932505162291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44657513968586576673549721 33493135476439932505162291)
      ·
        refine ⟨50239703214659898757743437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33493135476439932505162291 50239703214659898757743437)
        ·
          refine ⟨18839888705497462034153789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50239703214659898757743437 18839888705497462034153789)
          ·
            refine ⟨7064958264561548262807671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18839888705497462034153789 7064958264561548262807671)
            ·
              refine ⟨10597437396842322394211507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7064958264561548262807671 10597437396842322394211507)
              ·
                refine ⟨15896156095263483591317261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10597437396842322394211507 15896156095263483591317261)
                ·
                  refine ⟨5961058535723806346743973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15896156095263483591317261 5961058535723806346743973)
                  ·
                    refine ⟨1117698475448213690014495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5961058535723806346743973 1117698475448213690014495)
                    ·
                      rfl

theorem cell23_6530130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_6530130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530130 prefixEnd_6530130 := by exact prefixLift 6530130
  have htrace : WordTrace (prefixWord ++ tailWord_6530130) baseStart_6530130 baseEnd_6530130 := by
    simpa [prefixWord, tailWord_6530130, baseEnd_6530130] using wordTrace_append hprefix tailTrace_6530130
  have hstable : (prefixWord ++ tailWord_6530130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530130).length < 2 ^ (prefixWord ++ tailWord_6530130).sum := by decide
  have hdescent : baseEnd_6530130 < baseStart_6530130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530156 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 3, 5]
def baseStart_6530156 : Nat := 118140960795 + 6530156 * 2 ^ 59
def prefixEnd_6530156 : Nat := 4983230072969 + 3 ^ 40 * 6530156 * 2
def baseEnd_6530156 : Nat := 1117702925613885989439455

theorem tailTrace_6530156 : CollatzResearch.WordTrace tailWord_6530156 prefixEnd_6530156 1117702925613885989439455 := by
  unfold tailWord_6530156
  simp only [CollatzResearch.WordTrace]
  refine ⟨119087178065183774349689161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158782904086911699132918881 119087178065183774349689161)
  ·
    refine ⟨89315383548887830762266871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119087178065183774349689161 89315383548887830762266871)
    ·
      refine ⟨133973075323331746143400307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89315383548887830762266871 133973075323331746143400307)
      ·
        refine ⟨200959612984997619215100461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133973075323331746143400307 200959612984997619215100461)
        ·
          refine ⟨75359854869374107205662673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200959612984997619215100461 75359854869374107205662673)
          ·
            refine ⟨56519891152030580404247005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75359854869374107205662673 56519891152030580404247005)
            ·
              refine ⟨21194959182011467651592627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56519891152030580404247005 21194959182011467651592627)
              ·
                refine ⟨31792438773017201477388941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21194959182011467651592627 31792438773017201477388941)
                ·
                  refine ⟨11922164539881450554020853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31792438773017201477388941 11922164539881450554020853)
                  ·
                    refine ⟨1117702925613885989439455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11922164539881450554020853 1117702925613885989439455)
                    ·
                      rfl

theorem cell23_6530156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_6530156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530156 prefixEnd_6530156 := by exact prefixLift 6530156
  have htrace : WordTrace (prefixWord ++ tailWord_6530156) baseStart_6530156 baseEnd_6530156 := by
    simpa [prefixWord, tailWord_6530156, baseEnd_6530156] using wordTrace_append hprefix tailTrace_6530156
  have hstable : (prefixWord ++ tailWord_6530156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530156).length < 2 ^ (prefixWord ++ tailWord_6530156).sum := by decide
  have hdescent : baseEnd_6530156 < baseStart_6530156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530180 : List Nat := [2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2]
def baseStart_6530180 : Nat := 118140960795 + 6530180 * 2 ^ 59
def prefixEnd_6530180 : Nat := 4983230072969 + 3 ^ 40 * 6530180 * 2
def baseEnd_6530180 : Nat := 3353121100377365874418255

theorem tailTrace_6530180 : CollatzResearch.WordTrace tailWord_6530180 prefixEnd_6530180 3353121100377365874418255 := by
  unfold tailWord_6530180
  simp only [CollatzResearch.WordTrace]
  refine ⟨119087615741140300399125997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158783487654853733865501329 119087615741140300399125997)
  ·
    refine ⟨44657855902927612649672249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119087615741140300399125997 44657855902927612649672249)
    ·
      refine ⟨33493391927195709487254187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44657855902927612649672249 33493391927195709487254187)
      ·
        refine ⟨50240087890793564230881281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33493391927195709487254187 50240087890793564230881281)
        ·
          refine ⟨37680065918095173173160961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50240087890793564230881281 37680065918095173173160961)
          ·
            refine ⟨28260049438571379879870721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37680065918095173173160961 28260049438571379879870721)
            ·
              refine ⟨21195037078928534909903041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28260049438571379879870721 21195037078928534909903041)
              ·
                refine ⟨15896277809196401182427281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21195037078928534909903041 15896277809196401182427281)
                ·
                  refine ⟨11922208356897300886820461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15896277809196401182427281 11922208356897300886820461)
                  ·
                    refine ⟨4470828133836487832557673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11922208356897300886820461 4470828133836487832557673)
                    ·
                      refine ⟨3353121100377365874418255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4470828133836487832557673 3353121100377365874418255)
                      ·
                        rfl

theorem cell23_6530180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_6530180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530180 prefixEnd_6530180 := by exact prefixLift 6530180
  have htrace : WordTrace (prefixWord ++ tailWord_6530180) baseStart_6530180 baseEnd_6530180 := by
    simpa [prefixWord, tailWord_6530180, baseEnd_6530180] using wordTrace_append hprefix tailTrace_6530180
  have hstable : (prefixWord ++ tailWord_6530180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530180).length < 2 ^ (prefixWord ++ tailWord_6530180).sum := by decide
  have hdescent : baseEnd_6530180 < baseStart_6530180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530186 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 3, 6]
def baseStart_6530186 : Nat := 118140960795 + 6530186 * 2 ^ 59
def prefixEnd_6530186 : Nat := 4983230072969 + 3 ^ 40 * 6530186 * 2
def baseEnd_6530186 : Nat := 1117708060420430950314409

theorem tailTrace_6530186 : CollatzResearch.WordTrace tailWord_6530186 prefixEnd_6530186 1117708060420430950314409 := by
  unfold tailWord_6530186
  simp only [CollatzResearch.WordTrace]
  refine ⟨59543862580064715955742603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158783633546839242548646941 59543862580064715955742603)
  ·
    refine ⟨89315793870097073933613905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59543862580064715955742603 89315793870097073933613905)
    ·
      refine ⟨66986845402572805450210429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89315793870097073933613905 66986845402572805450210429)
      ·
        refine ⟨25120067025964802043828911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66986845402572805450210429 25120067025964802043828911)
        ·
          refine ⟨37680100538947203065743367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25120067025964802043828911 37680100538947203065743367)
          ·
            refine ⟨56520150808420804598615051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37680100538947203065743367 56520150808420804598615051)
            ·
              refine ⟨84780226212631206897922577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56520150808420804598615051 84780226212631206897922577)
              ·
                refine ⟨63585169659473405173441933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84780226212631206897922577 63585169659473405173441933)
                ·
                  refine ⟨23844438622302526940040725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63585169659473405173441933 23844438622302526940040725)
                  ·
                    refine ⟨1117708060420430950314409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23844438622302526940040725 1117708060420430950314409)
                    ·
                      rfl

theorem cell23_6530186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_6530186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530186 prefixEnd_6530186 := by exact prefixLift 6530186
  have htrace : WordTrace (prefixWord ++ tailWord_6530186) baseStart_6530186 baseEnd_6530186 := by
    simpa [prefixWord, tailWord_6530186, baseEnd_6530186] using wordTrace_append hprefix tailTrace_6530186
  have hstable : (prefixWord ++ tailWord_6530186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530186).length < 2 ^ (prefixWord ++ tailWord_6530186).sum := by decide
  have hdescent : baseEnd_6530186 < baseStart_6530186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530213 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 3, 2, 3]
def baseStart_6530213 : Nat := 118140960795 + 6530213 * 2 ^ 59
def prefixEnd_6530213 : Nat := 4983230072969 + 3 ^ 40 * 6530213 * 2
def baseEnd_6530213 : Nat := 3353138045238964245305603

theorem tailTrace_6530213 : CollatzResearch.WordTrace tailWord_6530213 prefixEnd_6530213 3353138045238964245305603 := by
  unfold tailWord_6530213
  simp only [CollatzResearch.WordTrace]
  refine ⟨238176435091161047434203293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158784290060774031622802195 238176435091161047434203293)
  ·
    refine ⟨89316163159185392787826235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238176435091161047434203293 89316163159185392787826235)
    ·
      refine ⟨133974244738778089181739353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89316163159185392787826235 133974244738778089181739353)
      ·
        refine ⟨100480683554083566886304515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133974244738778089181739353 100480683554083566886304515)
        ·
          refine ⟨150721025331125350329456773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100480683554083566886304515 150721025331125350329456773)
          ·
            refine ⟨28260192249586003186773145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150721025331125350329456773 28260192249586003186773145)
            ·
              refine ⟨21195144187189502390079859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28260192249586003186773145 21195144187189502390079859)
              ·
                refine ⟨31792716280784253585119789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21195144187189502390079859 31792716280784253585119789)
                ·
                  refine ⟨11922268605294095094419921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31792716280784253585119789 11922268605294095094419921)
                  ·
                    refine ⟨8941701453970571320814941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11922268605294095094419921 8941701453970571320814941)
                    ·
                      refine ⟨3353138045238964245305603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8941701453970571320814941 3353138045238964245305603)
                      ·
                        rfl

theorem cell23_6530213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_6530213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530213 prefixEnd_6530213 := by exact prefixLift 6530213
  have htrace : WordTrace (prefixWord ++ tailWord_6530213) baseStart_6530213 baseEnd_6530213 := by
    simpa [prefixWord, tailWord_6530213, baseEnd_6530213] using wordTrace_append hprefix tailTrace_6530213
  have hstable : (prefixWord ++ tailWord_6530213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530213).length < 2 ^ (prefixWord ++ tailWord_6530213).sum := by decide
  have hdescent : baseEnd_6530213 < baseStart_6530213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530227 : List Nat := [1, 1, 1, 2, 3, 2, 3, 5, 1, 2, 2]
def baseStart_6530227 : Nat := 118140960795 + 6530227 * 2 ^ 59
def prefixEnd_6530227 : Nat := 4983230072969 + 3 ^ 40 * 6530227 * 2
def baseEnd_6530227 : Nat := 3353145233968127190530539

theorem tailTrace_6530227 : CollatzResearch.WordTrace tailWord_6530227 prefixEnd_6530227 3353145233968127190530539 := by
  unfold tailWord_6530227
  simp only [CollatzResearch.WordTrace]
  refine ⟨238176945713110327825212935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158784630475406885216808623 238176945713110327825212935)
  ·
    refine ⟨357265418569665491737819403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238176945713110327825212935 357265418569665491737819403)
    ·
      refine ⟨535898127854498237606729105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357265418569665491737819403 535898127854498237606729105)
      ·
        refine ⟨401923595890873678205046829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535898127854498237606729105 401923595890873678205046829)
        ·
          refine ⟨150721348459077629326892561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401923595890873678205046829 150721348459077629326892561)
          ·
            refine ⟨113041011344308221995169421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150721348459077629326892561 113041011344308221995169421)
            ·
              refine ⟨42390379254115583248188533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113041011344308221995169421 42390379254115583248188533)
              ·
                refine ⟨3974098055073335929517675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42390379254115583248188533 3974098055073335929517675)
                ·
                  refine ⟨5961147082610003894276513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974098055073335929517675 5961147082610003894276513)
                  ·
                    refine ⟨4470860311957502920707385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5961147082610003894276513 4470860311957502920707385)
                    ·
                      refine ⟨3353145233968127190530539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4470860311957502920707385 3353145233968127190530539)
                      ·
                        rfl

theorem cell23_6530227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 1, 2, 2].length) (baseStart_6530227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530227 prefixEnd_6530227 := by exact prefixLift 6530227
  have htrace : WordTrace (prefixWord ++ tailWord_6530227) baseStart_6530227 baseEnd_6530227 := by
    simpa [prefixWord, tailWord_6530227, baseEnd_6530227] using wordTrace_append hprefix tailTrace_6530227
  have hstable : (prefixWord ++ tailWord_6530227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530227).length < 2 ^ (prefixWord ++ tailWord_6530227).sum := by decide
  have hdescent : baseEnd_6530227 < baseStart_6530227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530244 : List Nat := [2, 3, 3, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_6530244 : Nat := 118140960795 + 6530244 * 2 ^ 59
def prefixEnd_6530244 : Nat := 4983230072969 + 3 ^ 40 * 6530244 * 2
def baseEnd_6530244 : Nat := 3353153963139253624017961

theorem tailTrace_6530244 : CollatzResearch.WordTrace tailWord_6530244 prefixEnd_6530244 3353153963139253624017961 := by
  unfold tailWord_6530244
  simp only [CollatzResearch.WordTrace]
  refine ⟨119088782877024369864290893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158785043836032493152387857 119088782877024369864290893)
  ·
    refine ⟨44658293578884138699109085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119088782877024369864290893 44658293578884138699109085)
    ·
      refine ⟨16746860092081552012165907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44658293578884138699109085 16746860092081552012165907)
      ·
        refine ⟨25120290138122328018248861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16746860092081552012165907 25120290138122328018248861)
        ·
          refine ⟨9420108801795873006843323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25120290138122328018248861 9420108801795873006843323)
          ·
            refine ⟨14130163202693809510264985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9420108801795873006843323 14130163202693809510264985)
            ·
              refine ⟨10597622402020357132698739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14130163202693809510264985 10597622402020357132698739)
              ·
                refine ⟨15896433603030535699048109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10597622402020357132698739 15896433603030535699048109)
                ·
                  refine ⟨5961162601136450887143041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15896433603030535699048109 5961162601136450887143041)
                  ·
                    refine ⟨4470871950852338165357281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5961162601136450887143041 4470871950852338165357281)
                    ·
                      refine ⟨3353153963139253624017961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4470871950852338165357281 3353153963139253624017961)
                      ·
                        rfl

theorem cell23_6530244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_6530244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530244 prefixEnd_6530244 := by exact prefixLift 6530244
  have htrace : WordTrace (prefixWord ++ tailWord_6530244) baseStart_6530244 baseEnd_6530244 := by
    simpa [prefixWord, tailWord_6530244, baseEnd_6530244] using wordTrace_append hprefix tailTrace_6530244
  have hstable : (prefixWord ++ tailWord_6530244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530244).length < 2 ^ (prefixWord ++ tailWord_6530244).sum := by decide
  have hdescent : baseEnd_6530244 < baseStart_6530244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530276 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 1, 8]
def baseStart_6530276 : Nat := 118140960795 + 6530276 * 2 ^ 59
def prefixEnd_6530276 : Nat := 4983230072969 + 3 ^ 40 * 6530276 * 2
def baseEnd_6530276 : Nat := 1117723464840065832939271

theorem tailTrace_6530276 : CollatzResearch.WordTrace tailWord_6530276 prefixEnd_6530276 1117723464840065832939271 := by
  unfold tailWord_6530276
  simp only [CollatzResearch.WordTrace]
  refine ⟨119089366444966404596873341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158785821926621872795831121 119089366444966404596873341)
  ·
    refine ⟨44658512416862401723827503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119089366444966404596873341 44658512416862401723827503)
    ·
      refine ⟨66987768625293602585741255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44658512416862401723827503 66987768625293602585741255)
      ·
        refine ⟨100481652937940403878611883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66987768625293602585741255 100481652937940403878611883)
        ·
          refine ⟨150722479406910605817917825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100481652937940403878611883 150722479406910605817917825)
          ·
            refine ⟨113041859555182954363438369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150722479406910605817917825 113041859555182954363438369)
            ·
              refine ⟨84781394666387215772578777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113041859555182954363438369 84781394666387215772578777)
              ·
                refine ⟨63586045999790411829434083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84781394666387215772578777 63586045999790411829434083)
                ·
                  refine ⟨95379068999685617744151125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63586045999790411829434083 95379068999685617744151125)
                  ·
                    refine ⟨1117723464840065832939271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95379068999685617744151125 1117723464840065832939271)
                    ·
                      rfl

theorem cell23_6530276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_6530276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530276 prefixEnd_6530276 := by exact prefixLift 6530276
  have htrace : WordTrace (prefixWord ++ tailWord_6530276) baseStart_6530276 baseEnd_6530276 := by
    simpa [prefixWord, tailWord_6530276, baseEnd_6530276] using wordTrace_append hprefix tailTrace_6530276
  have hstable : (prefixWord ++ tailWord_6530276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530276).length < 2 ^ (prefixWord ++ tailWord_6530276).sum := by decide
  have hdescent : baseEnd_6530276 < baseStart_6530276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530340 : List Nat := [2, 3, 1, 3, 1, 1, 2, 5, 5]
def baseStart_6530340 : Nat := 118140960795 + 6530340 * 2 ^ 59
def prefixEnd_6530340 : Nat := 4983230072969 + 3 ^ 40 * 6530340 * 2
def baseEnd_6530340 : Nat := 372578139698009472046391

theorem tailTrace_6530340 : CollatzResearch.WordTrace tailWord_6530340 prefixEnd_6530340 372578139698009472046391 := by
  unfold tailWord_6530340
  simp only [CollatzResearch.WordTrace]
  refine ⟨119090533580850474062038237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158787378107800632082717649 119090533580850474062038237)
  ·
    refine ⟨44658950092818927773264339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119090533580850474062038237 44658950092818927773264339)
    ·
      refine ⟨66988425139228391659896509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44658950092818927773264339 66988425139228391659896509)
      ·
        refine ⟨25120659427210646872461191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66988425139228391659896509 25120659427210646872461191)
        ·
          refine ⟨37680989140815970308691787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25120659427210646872461191 37680989140815970308691787)
          ·
            refine ⟨56521483711223955463037681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37680989140815970308691787 56521483711223955463037681)
            ·
              refine ⟨42391112783417966597278261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56521483711223955463037681 42391112783417966597278261)
              ·
                refine ⟨3974166823445434368494837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42391112783417966597278261 3974166823445434368494837)
                ·
                  refine ⟨372578139698009472046391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3974166823445434368494837 372578139698009472046391)
                  ·
                    rfl

theorem cell23_6530340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_6530340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530340 prefixEnd_6530340 := by exact prefixLift 6530340
  have htrace : WordTrace (prefixWord ++ tailWord_6530340) baseStart_6530340 baseEnd_6530340 := by
    simpa [prefixWord, tailWord_6530340, baseEnd_6530340] using wordTrace_append hprefix tailTrace_6530340
  have hstable : (prefixWord ++ tailWord_6530340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530340).length < 2 ^ (prefixWord ++ tailWord_6530340).sum := by decide
  have hdescent : baseEnd_6530340 < baseStart_6530340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530357 : List Nat := [1, 3, 3, 1, 2, 2, 4, 2, 5]
def baseStart_6530357 : Nat := 118140960795 + 6530357 * 2 ^ 59
def prefixEnd_6530357 : Nat := 4983230072969 + 3 ^ 40 * 6530357 * 2
def baseEnd_6530357 : Nat := 372579109605912409100549

theorem tailTrace_6530357 : CollatzResearch.WordTrace tailWord_6530357 prefixEnd_6530357 372579109605912409100549 := by
  unfold tailWord_6530357
  simp only [CollatzResearch.WordTrace]
  refine ⟨238181687202639360027445325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158787791468426240018296883 238181687202639360027445325)
  ·
    refine ⟨89318132700989760010291997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238181687202639360027445325 89318132700989760010291997)
    ·
      refine ⟨33494299762871160003859499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89318132700989760010291997 33494299762871160003859499)
      ·
        refine ⟨50241449644306740005789249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33494299762871160003859499 50241449644306740005789249)
        ·
          refine ⟨37681087233230055004341937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50241449644306740005789249 37681087233230055004341937)
          ·
            refine ⟨28260815424922541253256453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37681087233230055004341937 28260815424922541253256453)
            ·
              refine ⟨5298902892172976484985585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28260815424922541253256453 5298902892172976484985585)
              ·
                refine ⟨3974177169129732363739189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5298902892172976484985585 3974177169129732363739189)
                ·
                  refine ⟨372579109605912409100549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3974177169129732363739189 372579109605912409100549)
                  ·
                    rfl

theorem cell23_6530357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 5].length) (baseStart_6530357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530357 prefixEnd_6530357 := by exact prefixLift 6530357
  have htrace : WordTrace (prefixWord ++ tailWord_6530357) baseStart_6530357 baseEnd_6530357 := by
    simpa [prefixWord, tailWord_6530357, baseEnd_6530357] using wordTrace_append hprefix tailTrace_6530357
  have hstable : (prefixWord ++ tailWord_6530357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530357).length < 2 ^ (prefixWord ++ tailWord_6530357).sum := by decide
  have hdescent : baseEnd_6530357 < baseStart_6530357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530373 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 4, 1, 4]
def baseStart_6530373 : Nat := 118140960795 + 6530373 * 2 ^ 59
def prefixEnd_6530373 : Nat := 4983230072969 + 3 ^ 40 * 6530373 * 2
def baseEnd_6530373 : Nat := 3353220202143683619304867

theorem tailTrace_6530373 : CollatzResearch.WordTrace tailWord_6530373 prefixEnd_6530373 3353220202143683619304867 := by
  unfold tailWord_6530373
  simp only [CollatzResearch.WordTrace]
  refine ⟨238182270770581394760027773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158788180513720929840018515 238182270770581394760027773)
  ·
    refine ⟨89318351538968023035010415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238182270770581394760027773 89318351538968023035010415)
    ·
      refine ⟨133977527308452034552515623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89318351538968023035010415 133977527308452034552515623)
      ·
        refine ⟨200966290962678051828773435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133977527308452034552515623 200966290962678051828773435)
        ·
          refine ⟨301449436444017077743160153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200966290962678051828773435 301449436444017077743160153)
          ·
            refine ⟨226087077333012808307370115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301449436444017077743160153 226087077333012808307370115)
            ·
              refine ⟨339130615999519212461055173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226087077333012808307370115 339130615999519212461055173)
              ·
                refine ⟨63586990499909852336447845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 339130615999519212461055173 63586990499909852336447845)
                ·
                  refine ⟨11922560718733097313083971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63586990499909852336447845 11922560718733097313083971)
                  ·
                    refine ⟨17883841078099645969625957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11922560718733097313083971 17883841078099645969625957)
                    ·
                      refine ⟨3353220202143683619304867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17883841078099645969625957 3353220202143683619304867)
                      ·
                        rfl

theorem cell23_6530373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_6530373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530373 prefixEnd_6530373 := by exact prefixLift 6530373
  have htrace : WordTrace (prefixWord ++ tailWord_6530373) baseStart_6530373 baseEnd_6530373 := by
    simpa [prefixWord, tailWord_6530373, baseEnd_6530373] using wordTrace_append hprefix tailTrace_6530373
  have hstable : (prefixWord ++ tailWord_6530373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530373).length < 2 ^ (prefixWord ++ tailWord_6530373).sum := by decide
  have hdescent : baseEnd_6530373 < baseStart_6530373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530374 : List Nat := [6, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_6530374 : Nat := 118140960795 + 6530374 * 2 ^ 59
def prefixEnd_6530374 : Nat := 4983230072969 + 3 ^ 40 * 6530374 * 2
def baseEnd_6530374 : Nat := 372580079513815346154707

theorem tailTrace_6530374 : CollatzResearch.WordTrace tailWord_6530374 prefixEnd_6530374 372580079513815346154707 := by
  unfold tailWord_6530374
  simp only [CollatzResearch.WordTrace]
  refine ⟨7443197101361805372837943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158788204829051847953876117 7443197101361805372837943)
  ·
    refine ⟨11164795652042708059256915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7443197101361805372837943 11164795652042708059256915)
    ·
      refine ⟨16747193478064062088885373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11164795652042708059256915 16747193478064062088885373)
      ·
        refine ⟨6280197554274023283332015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16747193478064062088885373 6280197554274023283332015)
        ·
          refine ⟨9420296331411034924998023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6280197554274023283332015 9420296331411034924998023)
          ·
            refine ⟨14130444497116552387497035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9420296331411034924998023 14130444497116552387497035)
            ·
              refine ⟨21195666745674828581245553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14130444497116552387497035 21195666745674828581245553)
              ·
                refine ⟨15896750059256121435934165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21195666745674828581245553 15896750059256121435934165)
                ·
                  refine ⟨372580079513815346154707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15896750059256121435934165 372580079513815346154707)
                  ·
                    rfl

theorem cell23_6530374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_6530374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530374 prefixEnd_6530374 := by exact prefixLift 6530374
  have htrace : WordTrace (prefixWord ++ tailWord_6530374) baseStart_6530374 baseEnd_6530374 := by
    simpa [prefixWord, tailWord_6530374, baseEnd_6530374] using wordTrace_append hprefix tailTrace_6530374
  have hstable : (prefixWord ++ tailWord_6530374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530374).length < 2 ^ (prefixWord ++ tailWord_6530374).sum := by decide
  have hdescent : baseEnd_6530374 < baseStart_6530374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530403 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 6]
def baseStart_6530403 : Nat := 118140960795 + 6530403 * 2 ^ 59
def prefixEnd_6530403 : Nat := 4983230072969 + 3 ^ 40 * 6530403 * 2
def baseEnd_6530403 : Nat := 3353235606563318501929729

theorem tailTrace_6530403 : CollatzResearch.WordTrace tailWord_6530403 prefixEnd_6530403 3353235606563318501929729 := by
  unfold tailWord_6530403
  simp only [CollatzResearch.WordTrace]
  refine ⟨238183364960472709883619863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158788909973648473255746575 238183364960472709883619863)
  ·
    refine ⟨357275047440709064825429795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238183364960472709883619863 357275047440709064825429795)
    ·
      refine ⟨535912571161063597238144693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357275047440709064825429795 535912571161063597238144693)
      ·
        refine ⟨50241803546349712241076065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 535912571161063597238144693 50241803546349712241076065)
        ·
          refine ⟨37681352659762284180807049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50241803546349712241076065 37681352659762284180807049)
          ·
            refine ⟨28261014494821713135605287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37681352659762284180807049 28261014494821713135605287)
            ·
              refine ⟨42391521742232569703407931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28261014494821713135605287 42391521742232569703407931)
              ·
                refine ⟨63587282613348854555111897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42391521742232569703407931 63587282613348854555111897)
                ·
                  refine ⟨47690461960011640916333923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63587282613348854555111897 47690461960011640916333923)
                  ·
                    refine ⟨71535692940017461374500885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47690461960011640916333923 71535692940017461374500885)
                    ·
                      refine ⟨3353235606563318501929729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71535692940017461374500885 3353235606563318501929729)
                      ·
                        rfl

theorem cell23_6530403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_6530403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530403 prefixEnd_6530403 := by exact prefixLift 6530403
  have htrace : WordTrace (prefixWord ++ tailWord_6530403) baseStart_6530403 baseEnd_6530403 := by
    simpa [prefixWord, tailWord_6530403, baseEnd_6530403] using wordTrace_append hprefix tailTrace_6530403
  have hstable : (prefixWord ++ tailWord_6530403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530403).length < 2 ^ (prefixWord ++ tailWord_6530403).sum := by decide
  have hdescent : baseEnd_6530403 < baseStart_6530403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530417 : List Nat := [1, 2, 2, 2, 1, 2, 4, 4, 1, 4]
def baseStart_6530417 : Nat := 118140960795 + 6530417 * 2 ^ 59
def prefixEnd_6530417 : Nat := 4983230072969 + 3 ^ 40 * 6530417 * 2
def baseEnd_6530417 : Nat := 1117747598430827149051555

theorem tailTrace_6530417 : CollatzResearch.WordTrace tailWord_6530417 prefixEnd_6530417 1117747598430827149051555 := by
  unfold tailWord_6530417
  simp only [CollatzResearch.WordTrace]
  refine ⟨238183875582421990274629505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158789250388281326849753003 238183875582421990274629505)
  ·
    refine ⟨178637906686816492705972129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238183875582421990274629505 178637906686816492705972129)
    ·
      refine ⟨133978430015112369529479097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178637906686816492705972129 133978430015112369529479097)
      ·
        refine ⟨100483822511334277147109323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133978430015112369529479097 100483822511334277147109323)
        ·
          refine ⟨150725733767001415720663985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100483822511334277147109323 150725733767001415720663985)
          ·
            refine ⟨113044300325251061790497989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150725733767001415720663985 113044300325251061790497989)
            ·
              refine ⟨21195806310984574085718373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113044300325251061790497989 21195806310984574085718373)
              ·
                refine ⟨3974213683309607641072195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21195806310984574085718373 3974213683309607641072195)
                ·
                  refine ⟨5961320524964411461608293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974213683309607641072195 5961320524964411461608293)
                  ·
                    refine ⟨1117747598430827149051555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5961320524964411461608293 1117747598430827149051555)
                    ·
                      rfl

theorem cell23_6530417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 1, 4].length) (baseStart_6530417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530417 prefixEnd_6530417 := by exact prefixLift 6530417
  have htrace : WordTrace (prefixWord ++ tailWord_6530417) baseStart_6530417 baseEnd_6530417 := by
    simpa [prefixWord, tailWord_6530417, baseEnd_6530417] using wordTrace_append hprefix tailTrace_6530417
  have hstable : (prefixWord ++ tailWord_6530417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530417).length < 2 ^ (prefixWord ++ tailWord_6530417).sum := by decide
  have hdescent : baseEnd_6530417 < baseStart_6530417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530434 : List Nat := [3, 4, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_6530434 : Nat := 118140960795 + 6530434 * 2 ^ 59
def prefixEnd_6530434 : Nat := 4983230072969 + 3 ^ 40 * 6530434 * 2
def baseEnd_6530434 : Nat := 1117750508154535960214029

theorem tailTrace_6530434 : CollatzResearch.WordTrace tailWord_6530434 prefixEnd_6530434 1117750508154535960214029 := by
  unfold tailWord_6530434
  simp only [CollatzResearch.WordTrace]
  refine ⟨59546123905840100544499589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158789663748906934785332237 59546123905840100544499589)
  ·
    refine ⟨11164898232345018852093673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59546123905840100544499589 11164898232345018852093673)
    ·
      refine ⟨8373673674258764139070255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11164898232345018852093673 8373673674258764139070255)
      ·
        refine ⟨12560510511388146208605383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8373673674258764139070255 12560510511388146208605383)
        ·
          refine ⟨18840765767082219312908075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12560510511388146208605383 18840765767082219312908075)
          ·
            refine ⟨28261148650623328969362113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18840765767082219312908075 28261148650623328969362113)
            ·
              refine ⟨21195861487967496727021585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28261148650623328969362113 21195861487967496727021585)
              ·
                refine ⟨15896896115975622545266189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21195861487967496727021585 15896896115975622545266189)
                ·
                  refine ⟨5961336043490858454474821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15896896115975622545266189 5961336043490858454474821)
                  ·
                    refine ⟨1117750508154535960214029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5961336043490858454474821 1117750508154535960214029)
                    ·
                      rfl

theorem cell23_6530434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_6530434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530434 prefixEnd_6530434 := by exact prefixLift 6530434
  have htrace : WordTrace (prefixWord ++ tailWord_6530434) baseStart_6530434 baseEnd_6530434 := by
    simpa [prefixWord, tailWord_6530434, baseEnd_6530434] using wordTrace_append hprefix tailTrace_6530434
  have hstable : (prefixWord ++ tailWord_6530434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530434).length < 2 ^ (prefixWord ++ tailWord_6530434).sum := by decide
  have hdescent : baseEnd_6530434 < baseStart_6530434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530467 : List Nat := [1, 1, 1, 4, 1, 3, 3, 2, 2, 3, 2]
def baseStart_6530467 : Nat := 118140960795 + 6530467 * 2 ^ 59
def prefixEnd_6530467 : Nat := 4983230072969 + 3 ^ 40 * 6530467 * 2
def baseEnd_6530467 : Nat := 3353268469325206251529435

theorem tailTrace_6530467 : CollatzResearch.WordTrace tailWord_6530467 prefixEnd_6530467 3353268469325206251529435 := by
  unfold tailWord_6530467
  simp only [CollatzResearch.WordTrace]
  refine ⟨238185699232240848813949655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158790466154827232542633103 238185699232240848813949655)
  ·
    refine ⟨357278548848361273220924483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238185699232240848813949655 357278548848361273220924483)
    ·
      refine ⟨535917823272541909831386725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357278548848361273220924483 535917823272541909831386725)
      ·
        refine ⟨100484591863601608093385011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 535917823272541909831386725 100484591863601608093385011)
        ·
          refine ⟨150726887795402412140077517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100484591863601608093385011 150726887795402412140077517)
          ·
            refine ⟨56522582923275904552529069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150726887795402412140077517 56522582923275904552529069)
            ·
              refine ⟨21195968596228464207198401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56522582923275904552529069 21195968596228464207198401)
              ·
                refine ⟨15896976447171348155398801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21195968596228464207198401 15896976447171348155398801)
                ·
                  refine ⟨11922732335378511116549101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15896976447171348155398801 11922732335378511116549101)
                  ·
                    refine ⟨4471024625766941668705913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11922732335378511116549101 4471024625766941668705913)
                    ·
                      refine ⟨3353268469325206251529435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4471024625766941668705913 3353268469325206251529435)
                      ·
                        rfl

theorem cell23_6530467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_6530467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530467 prefixEnd_6530467 := by exact prefixLift 6530467
  have htrace : WordTrace (prefixWord ++ tailWord_6530467) baseStart_6530467 baseEnd_6530467 := by
    simpa [prefixWord, tailWord_6530467, baseEnd_6530467] using wordTrace_append hprefix tailTrace_6530467
  have hstable : (prefixWord ++ tailWord_6530467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530467).length < 2 ^ (prefixWord ++ tailWord_6530467).sum := by decide
  have hdescent : baseEnd_6530467 < baseStart_6530467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530480 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 2, 6, 2]
def baseStart_6530480 : Nat := 118140960795 + 6530480 * 2 ^ 59
def prefixEnd_6530480 : Nat := 4983230072969 + 3 ^ 40 * 6530480 * 2
def baseEnd_6530480 : Nat := 3353275144573714700666875

theorem tailTrace_6530480 : CollatzResearch.WordTrace tailWord_6530480 prefixEnd_6530480 3353275144573714700666875 := by
  unfold tailWord_6530480
  simp only [CollatzResearch.WordTrace]
  refine ⟨119093086690596876017086447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158790782254129168022781929 119093086690596876017086447)
  ·
    refine ⟨178639630035895314025629671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119093086690596876017086447 178639630035895314025629671)
    ·
      refine ⟨267959445053842971038444507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178639630035895314025629671 267959445053842971038444507)
      ·
        refine ⟨401939167580764456557666761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267959445053842971038444507 401939167580764456557666761)
        ·
          refine ⟨301454375685573342418250071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401939167580764456557666761 301454375685573342418250071)
          ·
            refine ⟨452181563528360013627375107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301454375685573342418250071 452181563528360013627375107)
            ·
              refine ⟨678272345292540020441062661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452181563528360013627375107 678272345292540020441062661)
              ·
                refine ⟨127176064742351253832699249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 678272345292540020441062661 127176064742351253832699249)
                ·
                  refine ⟨95382048556763440374524437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127176064742351253832699249 95382048556763440374524437)
                  ·
                    refine ⟨4471033526098286267555833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95382048556763440374524437 4471033526098286267555833)
                    ·
                      refine ⟨3353275144573714700666875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4471033526098286267555833 3353275144573714700666875)
                      ·
                        rfl

theorem cell23_6530480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 6, 2].length) (baseStart_6530480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530480 prefixEnd_6530480 := by exact prefixLift 6530480
  have htrace : WordTrace (prefixWord ++ tailWord_6530480) baseStart_6530480 baseEnd_6530480 := by
    simpa [prefixWord, tailWord_6530480, baseEnd_6530480] using wordTrace_append hprefix tailTrace_6530480
  have hstable : (prefixWord ++ tailWord_6530480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530480).length < 2 ^ (prefixWord ++ tailWord_6530480).sum := by decide
  have hdescent : baseEnd_6530480 < baseStart_6530480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530503 : List Nat := [1, 1, 4, 1, 1, 3, 1, 11]
def baseStart_6530503 : Nat := 118140960795 + 6530503 * 2 ^ 59
def prefixEnd_6530503 : Nat := 4983230072969 + 3 ^ 40 * 6530503 * 2
def baseEnd_6530503 : Nat := 124195813134398818914047

theorem tailTrace_6530503 : CollatzResearch.WordTrace tailWord_6530503 prefixEnd_6530503 124195813134398818914047 := by
  unfold tailWord_6530503
  simp only [CollatzResearch.WordTrace]
  refine ⟨238187012260110426962260163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158791341506740284641506775 238187012260110426962260163)
  ·
    refine ⟨357280518390165640443390245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238187012260110426962260163 357280518390165640443390245)
    ·
      refine ⟨66990097198156057583135671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 357280518390165640443390245 66990097198156057583135671)
      ·
        refine ⟨100485145797234086374703507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66990097198156057583135671 100485145797234086374703507)
        ·
          refine ⟨150727718695851129562055261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100485145797234086374703507 150727718695851129562055261)
          ·
            refine ⟨56522894510944173585770723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150727718695851129562055261 56522894510944173585770723)
            ·
              refine ⟨84784341766416260378656085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56522894510944173585770723 84784341766416260378656085)
              ·
                refine ⟨124195813134398818914047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 84784341766416260378656085 124195813134398818914047)
                ·
                  rfl

theorem cell23_6530503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 11].length) (baseStart_6530503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530503 prefixEnd_6530503 := by exact prefixLift 6530503
  have htrace : WordTrace (prefixWord ++ tailWord_6530503) baseStart_6530503 baseEnd_6530503 := by
    simpa [prefixWord, tailWord_6530503, baseEnd_6530503] using wordTrace_append hprefix tailTrace_6530503
  have hstable : (prefixWord ++ tailWord_6530503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530503).length < 2 ^ (prefixWord ++ tailWord_6530503).sum := by decide
  have hdescent : baseEnd_6530503 < baseStart_6530503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530510 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_6530510 : Nat := 118140960795 + 6530510 * 2 ^ 59
def prefixEnd_6530510 : Nat := 4983230072969 + 3 ^ 40 * 6530510 * 2
def baseEnd_6530510 : Nat := 3353290548993349583291737

theorem tailTrace_6530510 : CollatzResearch.WordTrace tailWord_6530510 prefixEnd_6530510 3353290548993349583291737 := by
  unfold tailWord_6530510
  simp only [CollatzResearch.WordTrace]
  refine ⟨29773408446385633394720623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158791511714056711438509989 29773408446385633394720623)
  ·
    refine ⟨44660112669578450092080935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29773408446385633394720623 44660112669578450092080935)
    ·
      refine ⟨66990169004367675138121403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44660112669578450092080935 66990169004367675138121403)
      ·
        refine ⟨100485253506551512707182105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66990169004367675138121403 100485253506551512707182105)
        ·
          refine ⟨75363940129913634530386579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100485253506551512707182105 75363940129913634530386579)
          ·
            refine ⟨113045910194870451795579869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75363940129913634530386579 113045910194870451795579869)
            ·
              refine ⟨42392216323076419423342451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113045910194870451795579869 42392216323076419423342451)
              ·
                refine ⟨63588324484614629135013677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42392216323076419423342451 63588324484614629135013677)
                ·
                  refine ⟨23845621681730485925630129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63588324484614629135013677 23845621681730485925630129)
                  ·
                    refine ⟨17884216261297864444222597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23845621681730485925630129 17884216261297864444222597)
                    ·
                      refine ⟨3353290548993349583291737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17884216261297864444222597 3353290548993349583291737)
                      ·
                        rfl

theorem cell23_6530510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_6530510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530510 prefixEnd_6530510 := by exact prefixLift 6530510
  have htrace : WordTrace (prefixWord ++ tailWord_6530510) baseStart_6530510 baseEnd_6530510 := by
    simpa [prefixWord, tailWord_6530510, baseEnd_6530510] using wordTrace_append hprefix tailTrace_6530510
  have hstable : (prefixWord ++ tailWord_6530510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530510).length < 2 ^ (prefixWord ++ tailWord_6530510).sum := by decide
  have hdescent : baseEnd_6530510 < baseStart_6530510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530581 : List Nat := [1, 3, 2, 1, 3, 4, 1, 2, 2, 1, 3]
def baseStart_6530581 : Nat := 118140960795 + 6530581 * 2 ^ 59
def prefixEnd_6530581 : Nat := 4983230072969 + 3 ^ 40 * 6530581 * 2
def baseEnd_6530581 : Nat := 3353327006119818805503911

theorem tailTrace_6530581 : CollatzResearch.WordTrace tailWord_6530581 prefixEnd_6530581 3353327006119818805503911 := by
  unfold tailWord_6530581
  simp only [CollatzResearch.WordTrace]
  refine ⟨238189857153827846283599597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158793238102551897522399731 238189857153827846283599597)
  ·
    refine ⟨89321196432685442356349849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238189857153827846283599597 89321196432685442356349849)
    ·
      refine ⟨66990897324514081767262387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89321196432685442356349849 66990897324514081767262387)
      ·
        refine ⟨100486345986771122650893581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66990897324514081767262387 100486345986771122650893581)
        ·
          refine ⟨37682379745039170994085093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100486345986771122650893581 37682379745039170994085093)
          ·
            refine ⟨7065446202194844561390955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37682379745039170994085093 7065446202194844561390955)
            ·
              refine ⟨10598169303292266842086433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7065446202194844561390955 10598169303292266842086433)
              ·
                refine ⟨7948626977469200131564825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10598169303292266842086433 7948626977469200131564825)
                ·
                  refine ⟨5961470233101900098673619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7948626977469200131564825 5961470233101900098673619)
                  ·
                    refine ⟨8942205349652850148010429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5961470233101900098673619 8942205349652850148010429)
                    ·
                      refine ⟨3353327006119818805503911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8942205349652850148010429 3353327006119818805503911)
                      ·
                        rfl

theorem cell23_6530581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_6530581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530581 prefixEnd_6530581 := by exact prefixLift 6530581
  have htrace : WordTrace (prefixWord ++ tailWord_6530581) baseStart_6530581 baseEnd_6530581 := by
    simpa [prefixWord, tailWord_6530581, baseEnd_6530581] using wordTrace_append hprefix tailTrace_6530581
  have hstable : (prefixWord ++ tailWord_6530581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530581).length < 2 ^ (prefixWord ++ tailWord_6530581).sum := by decide
  have hdescent : baseEnd_6530581 < baseStart_6530581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530674 : List Nat := [3, 2, 1, 2, 3, 2, 2, 1, 2, 5]
def baseStart_6530674 : Nat := 118140960795 + 6530674 * 2 ^ 59
def prefixEnd_6530674 : Nat := 4983230072969 + 3 ^ 40 * 6530674 * 2
def baseEnd_6530674 : Nat := 1117791586606895647213661

theorem tailTrace_6530674 : CollatzResearch.WordTrace tailWord_6530674 prefixEnd_6530674 1117791586606895647213661 := by
  unfold tailWord_6530674
  simp only [CollatzResearch.WordTrace]
  refine ⟨59548312285622730791683769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158795499428327282111156717 59548312285622730791683769)
  ·
    refine ⟨44661234214217048093762827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59548312285622730791683769 44661234214217048093762827)
    ·
      refine ⟨66991851321325572140644241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44661234214217048093762827 66991851321325572140644241)
      ·
        refine ⟨50243888490994179105483181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66991851321325572140644241 50243888490994179105483181)
        ·
          refine ⟨18841458184122817164556193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50243888490994179105483181 18841458184122817164556193)
          ·
            refine ⟨14131093638092112873417145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18841458184122817164556193 14131093638092112873417145)
            ·
              refine ⟨10598320228569084655062859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14131093638092112873417145 10598320228569084655062859)
              ·
                refine ⟨15897480342853626982594289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10598320228569084655062859 15897480342853626982594289)
                ·
                  refine ⟨11923110257140220236945717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15897480342853626982594289 11923110257140220236945717)
                  ·
                    refine ⟨1117791586606895647213661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11923110257140220236945717 1117791586606895647213661)
                    ·
                      rfl

theorem cell23_6530674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_6530674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530674 prefixEnd_6530674 := by exact prefixLift 6530674
  have htrace : WordTrace (prefixWord ++ tailWord_6530674) baseStart_6530674 baseEnd_6530674 := by
    simpa [prefixWord, tailWord_6530674, baseEnd_6530674] using wordTrace_append hprefix tailTrace_6530674
  have hstable : (prefixWord ++ tailWord_6530674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530674).length < 2 ^ (prefixWord ++ tailWord_6530674).sum := by decide
  have hdescent : baseEnd_6530674 < baseStart_6530674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530680 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 4, 3, 5]
def baseStart_6530680 : Nat := 118140960795 + 6530680 * 2 ^ 59
def prefixEnd_6530680 : Nat := 4983230072969 + 3 ^ 40 * 6530680 * 2
def baseEnd_6530680 : Nat := 3353377840704613918165955

theorem tailTrace_6530680 : CollatzResearch.WordTrace tailWord_6530680 prefixEnd_6530680 3353377840704613918165955 := by
  unfold tailWord_6530680
  simp only [CollatzResearch.WordTrace]
  refine ⟨119096733990234593095726747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158795645320312790794302329 119096733990234593095726747)
  ·
    refine ⟨178645100985351889643590121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119096733990234593095726747 178645100985351889643590121)
    ·
      refine ⟨133983825739013917232692591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178645100985351889643590121 133983825739013917232692591)
      ·
        refine ⟨200975738608520875849038887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133983825739013917232692591 200975738608520875849038887)
        ·
          refine ⟨301463607912781313773558331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200975738608520875849038887 301463607912781313773558331)
          ·
            refine ⟨452195411869171970660337497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301463607912781313773558331 452195411869171970660337497)
            ·
              refine ⟨339146558901878977995253123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452195411869171970660337497 339146558901878977995253123)
              ·
                refine ⟨508719838352818466992879685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339146558901878977995253123 508719838352818466992879685)
                ·
                  refine ⟨95384969691153462561164941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 508719838352818466992879685 95384969691153462561164941)
                  ·
                    refine ⟨35769363634182548460436853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95384969691153462561164941 35769363634182548460436853)
                    ·
                      refine ⟨3353377840704613918165955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35769363634182548460436853 3353377840704613918165955)
                      ·
                        rfl

theorem cell23_6530680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_6530680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530680 prefixEnd_6530680 := by exact prefixLift 6530680
  have htrace : WordTrace (prefixWord ++ tailWord_6530680) baseStart_6530680 baseEnd_6530680 := by
    simpa [prefixWord, tailWord_6530680, baseEnd_6530680] using wordTrace_append hprefix tailTrace_6530680
  have hstable : (prefixWord ++ tailWord_6530680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530680).length < 2 ^ (prefixWord ++ tailWord_6530680).sum := by decide
  have hdescent : baseEnd_6530680 < baseStart_6530680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530728 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_6530728 : Nat := 118140960795 + 6530728 * 2 ^ 59
def prefixEnd_6530728 : Nat := 4983230072969 + 3 ^ 40 * 6530728 * 2
def baseEnd_6530728 : Nat := 3353402487776029730365735

theorem tailTrace_6530728 : CollatzResearch.WordTrace tailWord_6530728 prefixEnd_6530728 3353402487776029730365735 := by
  unfold tailWord_6530728
  simp only [CollatzResearch.WordTrace]
  refine ⟨119097609342147645194600419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158796812456196860259467225 119097609342147645194600419)
  ·
    refine ⟨178646414013221467791900629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119097609342147645194600419 178646414013221467791900629)
    ·
      refine ⟨4187025328434878151372671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 178646414013221467791900629 4187025328434878151372671)
      ·
        refine ⟨6280537992652317227059007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4187025328434878151372671 6280537992652317227059007)
        ·
          refine ⟨9420806988978475840588511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6280537992652317227059007 9420806988978475840588511)
          ·
            refine ⟨14131210483467713760882767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9420806988978475840588511 14131210483467713760882767)
            ·
              refine ⟨21196815725201570641324151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14131210483467713760882767 21196815725201570641324151)
              ·
                refine ⟨31795223587802355961986227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21196815725201570641324151 31795223587802355961986227)
                ·
                  refine ⟨47692835381703533942979341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31795223587802355961986227 47692835381703533942979341)
                  ·
                    refine ⟨17884813268138825228617253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47692835381703533942979341 17884813268138825228617253)
                    ·
                      refine ⟨3353402487776029730365735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17884813268138825228617253 3353402487776029730365735)
                      ·
                        rfl

theorem cell23_6530728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_6530728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530728 prefixEnd_6530728 := by exact prefixLift 6530728
  have htrace : WordTrace (prefixWord ++ tailWord_6530728) baseStart_6530728 baseEnd_6530728 := by
    simpa [prefixWord, tailWord_6530728, baseEnd_6530728] using wordTrace_append hprefix tailTrace_6530728
  have hstable : (prefixWord ++ tailWord_6530728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530728).length < 2 ^ (prefixWord ++ tailWord_6530728).sum := by decide
  have hdescent : baseEnd_6530728 < baseStart_6530728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530767 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 4]
def baseStart_6530767 : Nat := 118140960795 + 6530767 * 2 ^ 59
def prefixEnd_6530767 : Nat := 4983230072969 + 3 ^ 40 * 6530767 * 2
def baseEnd_6530767 : Nat := 3353422513521555077778055

theorem tailTrace_6530767 : CollatzResearch.WordTrace tailWord_6530767 prefixEnd_6530767 3353422513521555077778055 := by
  unfold tailWord_6530767
  simp only [CollatzResearch.WordTrace]
  refine ⟨238196641131154000049870555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158797760754102666699913703 238196641131154000049870555)
  ·
    refine ⟨357294961696731000074805833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238196641131154000049870555 357294961696731000074805833)
    ·
      refine ⟨267971221272548250056104375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357294961696731000074805833 267971221272548250056104375)
      ·
        refine ⟨401956831908822375084156563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267971221272548250056104375 401956831908822375084156563)
        ·
          refine ⟨602935247863233562626234845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401956831908822375084156563 602935247863233562626234845)
          ·
            refine ⟨226100717948712585984838067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 602935247863233562626234845 226100717948712585984838067)
            ·
              refine ⟨339151076923068878977257101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226100717948712585984838067 339151076923068878977257101)
              ·
                refine ⟨127181653846150829616471413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339151076923068878977257101 127181653846150829616471413)
                ·
                  refine ⟨11923280048076640276544195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127181653846150829616471413 11923280048076640276544195)
                  ·
                    refine ⟨17884920072114960414816293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11923280048076640276544195 17884920072114960414816293)
                    ·
                      refine ⟨3353422513521555077778055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17884920072114960414816293 3353422513521555077778055)
                      ·
                        rfl

theorem cell23_6530767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 4].length) (baseStart_6530767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530767 prefixEnd_6530767 := by exact prefixLift 6530767
  have htrace : WordTrace (prefixWord ++ tailWord_6530767) baseStart_6530767 baseEnd_6530767 := by
    simpa [prefixWord, tailWord_6530767, baseEnd_6530767] using wordTrace_append hprefix tailTrace_6530767
  have hstable : (prefixWord ++ tailWord_6530767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530767).length < 2 ^ (prefixWord ++ tailWord_6530767).sum := by decide
  have hdescent : baseEnd_6530767 < baseStart_6530767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530784 : List Nat := [2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 4]
def baseStart_6530784 : Nat := 118140960795 + 6530784 * 2 ^ 59
def prefixEnd_6530784 : Nat := 4983230072969 + 3 ^ 40 * 6530784 * 2
def baseEnd_6530784 : Nat := 3353431242692681511265477

theorem tailTrace_6530784 : CollatzResearch.WordTrace tailWord_6530784 prefixEnd_6530784 3353431242692681511265477 := by
  unfold tailWord_6530784
  simp only [CollatzResearch.WordTrace]
  refine ⟨119098630586046205976619703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158798174114728274635492937 119098630586046205976619703)
  ·
    refine ⟨178647945879069308964929555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119098630586046205976619703 178647945879069308964929555)
    ·
      refine ⟨267971918818603963447394333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178647945879069308964929555 267971918818603963447394333)
      ·
        refine ⟨100489469556976486292772875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267971918818603963447394333 100489469556976486292772875)
        ·
          refine ⟨150734204335464729439159313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100489469556976486292772875 150734204335464729439159313)
          ·
            refine ⟨113050653251598547079369485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150734204335464729439159313 113050653251598547079369485)
            ·
              refine ⟨42393994969349455154763557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113050653251598547079369485 42393994969349455154763557)
              ·
                refine ⟨7948874056753022841518167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42393994969349455154763557 7948874056753022841518167)
                ·
                  refine ⟨11923311085129534262277251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7948874056753022841518167 11923311085129534262277251)
                  ·
                    refine ⟨17884966627694301393415877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11923311085129534262277251 17884966627694301393415877)
                    ·
                      refine ⟨3353431242692681511265477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17884966627694301393415877 3353431242692681511265477)
                      ·
                        rfl

theorem cell23_6530784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_6530784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530784 prefixEnd_6530784 := by exact prefixLift 6530784
  have htrace : WordTrace (prefixWord ++ tailWord_6530784) baseStart_6530784 baseEnd_6530784 := by
    simpa [prefixWord, tailWord_6530784, baseEnd_6530784] using wordTrace_append hprefix tailTrace_6530784
  have hstable : (prefixWord ++ tailWord_6530784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530784).length < 2 ^ (prefixWord ++ tailWord_6530784).sum := by decide
  have hdescent : baseEnd_6530784 < baseStart_6530784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530794 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 4, 4]
def baseStart_6530794 : Nat := 118140960795 + 6530794 * 2 ^ 59
def prefixEnd_6530794 : Nat := 4983230072969 + 3 ^ 40 * 6530794 * 2
def baseEnd_6530794 : Nat := 1117812125833075490713477

theorem tailTrace_6530794 : CollatzResearch.WordTrace tailWord_6530794 prefixEnd_6530794 1117812125833075490713477 := by
  unfold tailWord_6530794
  simp only [CollatzResearch.WordTrace]
  refine ⟨59549406475514045915275859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158798417268037455774068957 59549406475514045915275859)
  ·
    refine ⟨89324109713271068872913789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59549406475514045915275859 89324109713271068872913789)
    ·
      refine ⟨33496541142476650827342671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89324109713271068872913789 33496541142476650827342671)
      ·
        refine ⟨50244811713714976241014007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33496541142476650827342671 50244811713714976241014007)
        ·
          refine ⟨75367217570572464361521011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50244811713714976241014007 75367217570572464361521011)
          ·
            refine ⟨113050826355858696542281517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75367217570572464361521011 113050826355858696542281517)
            ·
              refine ⟨42394059883447011203355569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113050826355858696542281517 42394059883447011203355569)
              ·
                refine ⟨31795544912585258402516677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42394059883447011203355569 31795544912585258402516677)
                ·
                  refine ⟨5961664671109735950471877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31795544912585258402516677 5961664671109735950471877)
                  ·
                    refine ⟨1117812125833075490713477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5961664671109735950471877 1117812125833075490713477)
                    ·
                      rfl

theorem cell23_6530794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_6530794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530794 prefixEnd_6530794 := by exact prefixLift 6530794
  have htrace : WordTrace (prefixWord ++ tailWord_6530794) baseStart_6530794 baseEnd_6530794 := by
    simpa [prefixWord, tailWord_6530794, baseEnd_6530794] using wordTrace_append hprefix tailTrace_6530794
  have hstable : (prefixWord ++ tailWord_6530794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530794).length < 2 ^ (prefixWord ++ tailWord_6530794).sum := by decide
  have hdescent : baseEnd_6530794 < baseStart_6530794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530857 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 3, 5, 4]
def baseStart_6530857 : Nat := 118140960795 + 6530857 * 2 ^ 59
def prefixEnd_6530857 : Nat := 4983230072969 + 3 ^ 40 * 6530857 * 2
def baseEnd_6530857 : Nat := 3353468726780459725652641

theorem tailTrace_6530857 : CollatzResearch.WordTrace tailWord_6530857 prefixEnd_6530857 3353468726780459725652641 := by
  unfold tailWord_6530857
  simp only [CollatzResearch.WordTrace]
  refine ⟨238199923700827945420646825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158799949133885296947097883 238199923700827945420646825)
  ·
    refine ⟨178649942775620959065485119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238199923700827945420646825 178649942775620959065485119)
    ·
      refine ⟨267974914163431438598227679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178649942775620959065485119 267974914163431438598227679)
      ·
        refine ⟨401962371245147157897341519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267974914163431438598227679 401962371245147157897341519)
        ·
          refine ⟨602943556867720736846012279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401962371245147157897341519 602943556867720736846012279)
          ·
            refine ⟨904415335301581105269018419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602943556867720736846012279 904415335301581105269018419)
            ·
              refine ⟨1356623002952371657903527629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904415335301581105269018419 1356623002952371657903527629)
              ·
                refine ⟨508733626107139371713822861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1356623002952371657903527629 508733626107139371713822861)
                ·
                  refine ⟨190775109790177264392683573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 508733626107139371713822861 190775109790177264392683573)
                  ·
                    refine ⟨17885166542829118536814085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 190775109790177264392683573 17885166542829118536814085)
                    ·
                      refine ⟨3353468726780459725652641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17885166542829118536814085 3353468726780459725652641)
                      ·
                        rfl

theorem cell23_6530857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_6530857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530857 prefixEnd_6530857 := by exact prefixLift 6530857
  have htrace : WordTrace (prefixWord ++ tailWord_6530857) baseStart_6530857 baseEnd_6530857 := by
    simpa [prefixWord, tailWord_6530857, baseEnd_6530857] using wordTrace_append hprefix tailTrace_6530857
  have hstable : (prefixWord ++ tailWord_6530857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530857).length < 2 ^ (prefixWord ++ tailWord_6530857).sum := by decide
  have hdescent : baseEnd_6530857 < baseStart_6530857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530869 : List Nat := [1, 3, 3, 1, 4, 2, 2, 2, 1, 2, 2]
def baseStart_6530869 : Nat := 118140960795 + 6530869 * 2 ^ 59
def prefixEnd_6530869 : Nat := 4983230072969 + 3 ^ 40 * 6530869 * 2
def baseEnd_6530869 : Nat := 3353474888548313678702587

theorem tailTrace_6530869 : CollatzResearch.WordTrace tailWord_6530869 prefixEnd_6530869 3353474888548313678702587 := by
  unfold tailWord_6530869
  simp only [CollatzResearch.WordTrace]
  refine ⟨238200361376784471470083661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158800240917856314313389107 238200361376784471470083661)
  ·
    refine ⟨89325135516294176801281373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238200361376784471470083661 89325135516294176801281373)
    ·
      refine ⟨33496925818610316300480515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89325135516294176801281373 33496925818610316300480515)
      ·
        refine ⟨50245388727915474450720773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33496925818610316300480515 50245388727915474450720773)
        ·
          refine ⟨9421010386484151459510145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50245388727915474450720773 9421010386484151459510145)
          ·
            refine ⟨7065757789863113594632609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9421010386484151459510145 7065757789863113594632609)
            ·
              refine ⟨5299318342397335195974457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7065757789863113594632609 5299318342397335195974457)
              ·
                refine ⟨3974488756798001396980843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5299318342397335195974457 3974488756798001396980843)
                ·
                  refine ⟨5961733135197002095471265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974488756798001396980843 5961733135197002095471265)
                  ·
                    refine ⟨4471299851397751571603449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5961733135197002095471265 4471299851397751571603449)
                    ·
                      refine ⟨3353474888548313678702587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4471299851397751571603449 3353474888548313678702587)
                      ·
                        rfl

theorem cell23_6530869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_6530869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530869 prefixEnd_6530869 := by exact prefixLift 6530869
  have htrace : WordTrace (prefixWord ++ tailWord_6530869) baseStart_6530869 baseEnd_6530869 := by
    simpa [prefixWord, tailWord_6530869, baseEnd_6530869] using wordTrace_append hprefix tailTrace_6530869
  have hstable : (prefixWord ++ tailWord_6530869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530869).length < 2 ^ (prefixWord ++ tailWord_6530869).sum := by decide
  have hdescent : baseEnd_6530869 < baseStart_6530869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530874 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4]
def baseStart_6530874 : Nat := 118140960795 + 6530874 * 2 ^ 59
def prefixEnd_6530874 : Nat := 4983230072969 + 3 ^ 40 * 6530874 * 2
def baseEnd_6530874 : Nat := 3353477455951586159140063

theorem tailTrace_6530874 : CollatzResearch.WordTrace tailWord_6530874 prefixEnd_6530874 3353477455951586159140063 := by
  unfold tailWord_6530874
  simp only [CollatzResearch.WordTrace]
  refine ⟨59550135935441589331003919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158800362494510904882677117 59550135935441589331003919)
  ·
    refine ⟨89325203903162383996505879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59550135935441589331003919 89325203903162383996505879)
    ·
      refine ⟨133987805854743575994758819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89325203903162383996505879 133987805854743575994758819)
      ·
        refine ⟨200981708782115363992138229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133987805854743575994758819 200981708782115363992138229)
        ·
          refine ⟨18842035198323315374262959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200981708782115363992138229 18842035198323315374262959)
          ·
            refine ⟨28263052797484973061394439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18842035198323315374262959 28263052797484973061394439)
            ·
              refine ⟨42394579196227459592091659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28263052797484973061394439 42394579196227459592091659)
              ·
                refine ⟨63591868794341189388137489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42394579196227459592091659 63591868794341189388137489)
                ·
                  refine ⟨47693901595755892041103117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63591868794341189388137489 47693901595755892041103117)
                  ·
                    refine ⟨17885213098408459515413669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47693901595755892041103117 17885213098408459515413669)
                    ·
                      refine ⟨3353477455951586159140063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17885213098408459515413669 3353477455951586159140063)
                      ·
                        rfl

theorem cell23_6530874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_6530874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530874 prefixEnd_6530874 := by exact prefixLift 6530874
  have htrace : WordTrace (prefixWord ++ tailWord_6530874) baseStart_6530874 baseEnd_6530874 := by
    simpa [prefixWord, tailWord_6530874, baseEnd_6530874] using wordTrace_append hprefix tailTrace_6530874
  have hstable : (prefixWord ++ tailWord_6530874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530874).length < 2 ^ (prefixWord ++ tailWord_6530874).sum := by decide
  have hdescent : baseEnd_6530874 < baseStart_6530874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530878 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 3, 3, 2]
def baseStart_6530878 : Nat := 118140960795 + 6530878 * 2 ^ 59
def prefixEnd_6530878 : Nat := 4983230072969 + 3 ^ 40 * 6530878 * 2
def baseEnd_6530878 : Nat := 3353479509874204143490045

theorem tailTrace_6530878 : CollatzResearch.WordTrace tailWord_6530878 prefixEnd_6530878 3353479509874204143490045 := by
  unfold tailWord_6530878
  simp only [CollatzResearch.WordTrace]
  refine ⟨29775086204218983250895161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158800459755834577338107525 29775086204218983250895161)
  ·
    refine ⟨22331314653164237438171371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29775086204218983250895161 22331314653164237438171371)
    ·
      refine ⟨33496971979746356157257057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22331314653164237438171371 33496971979746356157257057)
      ·
        refine ⟨25122728984809767117942793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33496971979746356157257057 25122728984809767117942793)
        ·
          refine ⟨18842046738607325338457095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25122728984809767117942793 18842046738607325338457095)
          ·
            refine ⟨28263070107910988007685643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18842046738607325338457095 28263070107910988007685643)
            ·
              refine ⟨42394605161866482011528465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28263070107910988007685643 42394605161866482011528465)
              ·
                refine ⟨31795953871399861508646349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42394605161866482011528465 31795953871399861508646349)
                ·
                  refine ⟨11923482701774948065742381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31795953871399861508646349 11923482701774948065742381)
                  ·
                    refine ⟨4471306013165605524653393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11923482701774948065742381 4471306013165605524653393)
                    ·
                      refine ⟨3353479509874204143490045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4471306013165605524653393 3353479509874204143490045)
                      ·
                        rfl

theorem cell23_6530878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_6530878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530878 prefixEnd_6530878 := by exact prefixLift 6530878
  have htrace : WordTrace (prefixWord ++ tailWord_6530878) baseStart_6530878 baseEnd_6530878 := by
    simpa [prefixWord, tailWord_6530878, baseEnd_6530878] using wordTrace_append hprefix tailTrace_6530878
  have hstable : (prefixWord ++ tailWord_6530878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530878).length < 2 ^ (prefixWord ++ tailWord_6530878).sum := by decide
  have hdescent : baseEnd_6530878 < baseStart_6530878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530925 : List Nat := [1, 5, 1, 1, 1, 1, 5, 2, 2, 2, 2]
def baseStart_6530925 : Nat := 118140960795 + 6530925 * 2 ^ 59
def prefixEnd_6530925 : Nat := 4983230072969 + 3 ^ 40 * 6530925 * 2
def baseEnd_6530925 : Nat := 3353503643464965459602329

theorem tailTrace_6530925 : CollatzResearch.WordTrace tailWord_6530925 prefixEnd_6530925 3353503643464965459602329 := by
  unfold tailWord_6530925
  simp only [CollatzResearch.WordTrace]
  refine ⟨238202403864581593034122229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158801602576387728689414819 238202403864581593034122229)
  ·
    refine ⟨22331475362304524346948959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 238202403864581593034122229 22331475362304524346948959)
    ·
      refine ⟨33497213043456786520423439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22331475362304524346948959 33497213043456786520423439)
      ·
        refine ⟨50245819565185179780635159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33497213043456786520423439 50245819565185179780635159)
        ·
          refine ⟨75368729347777769670952739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50245819565185179780635159 75368729347777769670952739)
          ·
            refine ⟨113053094021666654506429109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75368729347777769670952739 113053094021666654506429109)
            ·
              refine ⟨10598727564531248859977729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113053094021666654506429109 10598727564531248859977729)
              ·
                refine ⟨7949045673398436644983297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10598727564531248859977729 7949045673398436644983297)
                ·
                  refine ⟨5961784255048827483737473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7949045673398436644983297 5961784255048827483737473)
                  ·
                    refine ⟨4471338191286620612803105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5961784255048827483737473 4471338191286620612803105)
                    ·
                      refine ⟨3353503643464965459602329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4471338191286620612803105 3353503643464965459602329)
                      ·
                        rfl

theorem cell23_6530925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_6530925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530925 prefixEnd_6530925 := by exact prefixLift 6530925
  have htrace : WordTrace (prefixWord ++ tailWord_6530925) baseStart_6530925 baseEnd_6530925 := by
    simpa [prefixWord, tailWord_6530925, baseEnd_6530925] using wordTrace_append hprefix tailTrace_6530925
  have hstable : (prefixWord ++ tailWord_6530925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530925).length < 2 ^ (prefixWord ++ tailWord_6530925).sum := by decide
  have hdescent : baseEnd_6530925 < baseStart_6530925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530942 : List Nat := [4, 2, 3, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_6530942 : Nat := 118140960795 + 6530942 * 2 ^ 59
def prefixEnd_6530942 : Nat := 4983230072969 + 3 ^ 40 * 6530942 * 2
def baseEnd_6530942 : Nat := 3353512372636091893089751

theorem tailTrace_6530942 : CollatzResearch.WordTrace tailWord_6530942 prefixEnd_6530942 3353512372636091893089751 := by
  unfold tailWord_6530942
  simp only [CollatzResearch.WordTrace]
  refine ⟨29775377988190000617186385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158802015937013336624994053 29775377988190000617186385)
  ·
    refine ⟨22331533491142500462889789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29775377988190000617186385 22331533491142500462889789)
    ·
      refine ⟨8374325059178437673583671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22331533491142500462889789 8374325059178437673583671)
      ·
        refine ⟨12561487588767656510375507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8374325059178437673583671 12561487588767656510375507)
        ·
          refine ⟨18842231383151484765563261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12561487588767656510375507 18842231383151484765563261)
          ·
            refine ⟨7065836768681806787086223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18842231383151484765563261 7065836768681806787086223)
            ·
              refine ⟨10598755153022710180629335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7065836768681806787086223 10598755153022710180629335)
              ·
                refine ⟨15898132729534065270944003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10598755153022710180629335 15898132729534065270944003)
                ·
                  refine ⟨23847199094301097906416005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15898132729534065270944003 23847199094301097906416005)
                  ·
                    refine ⟨4471349830181455857453001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23847199094301097906416005 4471349830181455857453001)
                    ·
                      refine ⟨3353512372636091893089751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4471349830181455857453001 3353512372636091893089751)
                      ·
                        rfl

theorem cell23_6530942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_6530942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530942 prefixEnd_6530942 := by exact prefixLift 6530942
  have htrace : WordTrace (prefixWord ++ tailWord_6530942) baseStart_6530942 baseEnd_6530942 := by
    simpa [prefixWord, tailWord_6530942, baseEnd_6530942] using wordTrace_append hprefix tailTrace_6530942
  have hstable : (prefixWord ++ tailWord_6530942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530942).length < 2 ^ (prefixWord ++ tailWord_6530942).sum := by decide
  have hdescent : baseEnd_6530942 < baseStart_6530942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530978 : List Nat := [3, 3, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_6530978 : Nat := 118140960795 + 6530978 * 2 ^ 59
def prefixEnd_6530978 : Nat := 4983230072969 + 3 ^ 40 * 6530978 * 2
def baseEnd_6530978 : Nat := 1117843619313217917413195

theorem tailTrace_6530978 : CollatzResearch.WordTrace tailWord_6530978 prefixEnd_6530978 1117843619313217917413195 := by
  unfold tailWord_6530978
  simp only [CollatzResearch.WordTrace]
  refine ⟨59551084233347395771450397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158802891288926388723867725 59551084233347395771450397)
  ·
    refine ⟨22331656587505273414293899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59551084233347395771450397 22331656587505273414293899)
    ·
      refine ⟨33497484881257910121440849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22331656587505273414293899 33497484881257910121440849)
      ·
        refine ⟨25123113660943432591080637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33497484881257910121440849 25123113660943432591080637)
        ·
          refine ⟨9421167622853787221655239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25123113660943432591080637 9421167622853787221655239)
          ·
            refine ⟨14131751434280680832482859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9421167622853787221655239 14131751434280680832482859)
            ·
              refine ⟨21197627151421021248724289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14131751434280680832482859 21197627151421021248724289)
              ·
                refine ⟨15898220363565765936543217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21197627151421021248724289 15898220363565765936543217)
                ·
                  refine ⟨11923665272674324452407413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15898220363565765936543217 11923665272674324452407413)
                  ·
                    refine ⟨1117843619313217917413195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11923665272674324452407413 1117843619313217917413195)
                    ·
                      rfl

theorem cell23_6530978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_6530978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530978 prefixEnd_6530978 := by exact prefixLift 6530978
  have htrace : WordTrace (prefixWord ++ tailWord_6530978) baseStart_6530978 baseEnd_6530978 := by
    simpa [prefixWord, tailWord_6530978, baseEnd_6530978] using wordTrace_append hprefix tailTrace_6530978
  have hstable : (prefixWord ++ tailWord_6530978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530978).length < 2 ^ (prefixWord ++ tailWord_6530978).sum := by decide
  have hdescent : baseEnd_6530978 < baseStart_6530978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530981 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 4, 4, 2]
def baseStart_6530981 : Nat := 118140960795 + 6530981 * 2 ^ 59
def prefixEnd_6530981 : Nat := 4983230072969 + 3 ^ 40 * 6530981 * 2
def baseEnd_6530981 : Nat := 3353532398381617240502071

theorem tailTrace_6530981 : CollatzResearch.WordTrace tailWord_6530981 prefixEnd_6530981 3353532398381617240502071 := by
  unfold tailWord_6530981
  simp only [CollatzResearch.WordTrace]
  refine ⟨238204446352378714598160797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158802964234919143065440531 238204446352378714598160797)
  ·
    refine ⟨89326667382142017974310299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 238204446352378714598160797 89326667382142017974310299)
    ·
      refine ⟨133990001073213026961465449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89326667382142017974310299 133990001073213026961465449)
      ·
        refine ⟨100492500804909770221099087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133990001073213026961465449 100492500804909770221099087)
        ·
          refine ⟨150738751207364655331648631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100492500804909770221099087 150738751207364655331648631)
          ·
            refine ⟨226108126811046982997472947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150738751207364655331648631 226108126811046982997472947)
            ·
              refine ⟨339162190216570474496209421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226108126811046982997472947 339162190216570474496209421)
              ·
                refine ⟨127185821331213927936078533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 339162190216570474496209421 127185821331213927936078533)
                ·
                  refine ⟨23847341499602611488014725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127185821331213927936078533 23847341499602611488014725)
                  ·
                    refine ⟨4471376531175489654002761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23847341499602611488014725 4471376531175489654002761)
                    ·
                      refine ⟨3353532398381617240502071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4471376531175489654002761 3353532398381617240502071)
                      ·
                        rfl

theorem cell23_6530981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_6530981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530981 prefixEnd_6530981 := by exact prefixLift 6530981
  have htrace : WordTrace (prefixWord ++ tailWord_6530981) baseStart_6530981 baseEnd_6530981 := by
    simpa [prefixWord, tailWord_6530981, baseEnd_6530981] using wordTrace_append hprefix tailTrace_6530981
  have hstable : (prefixWord ++ tailWord_6530981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530981).length < 2 ^ (prefixWord ++ tailWord_6530981).sum := by decide
  have hdescent : baseEnd_6530981 < baseStart_6530981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6530994 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_6530994 : Nat := 118140960795 + 6530994 * 2 ^ 59
def prefixEnd_6530994 : Nat := 4983230072969 + 3 ^ 40 * 6530994 * 2
def baseEnd_6530994 : Nat := 3353539073630125689639511

theorem tailTrace_6530994 : CollatzResearch.WordTrace tailWord_6530994 prefixEnd_6530994 3353539073630125689639511 := by
  unfold tailWord_6530994
  simp only [CollatzResearch.WordTrace]
  refine ⟨59551230125332904454596009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158803280334221078545589357 59551230125332904454596009)
  ·
    refine ⟨44663422593999678340947007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59551230125332904454596009 44663422593999678340947007)
    ·
      refine ⟨66995133890999517511420511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44663422593999678340947007 66995133890999517511420511)
      ·
        refine ⟨100492700836499276267130767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66995133890999517511420511 100492700836499276267130767)
        ·
          refine ⟨150739051254748914400696151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100492700836499276267130767 150739051254748914400696151)
          ·
            refine ⟨226108576882123371601044227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150739051254748914400696151 226108576882123371601044227)
            ·
              refine ⟨339162865323185057401566341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226108576882123371601044227 339162865323185057401566341)
              ·
                refine ⟨63593037248097198262793689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 339162865323185057401566341 63593037248097198262793689)
                ·
                  refine ⟨47694777936072898697095267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63593037248097198262793689 47694777936072898697095267)
                  ·
                    refine ⟨71542166904109348045642901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47694777936072898697095267 71542166904109348045642901)
                    ·
                      refine ⟨3353539073630125689639511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71542166904109348045642901 3353539073630125689639511)
                      ·
                        rfl

theorem cell23_6530994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_6530994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6530994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6530994 prefixEnd_6530994 := by exact prefixLift 6530994
  have htrace : WordTrace (prefixWord ++ tailWord_6530994) baseStart_6530994 baseEnd_6530994 := by
    simpa [prefixWord, tailWord_6530994, baseEnd_6530994] using wordTrace_append hprefix tailTrace_6530994
  have hstable : (prefixWord ++ tailWord_6530994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6530994).length < 2 ^ (prefixWord ++ tailWord_6530994).sum := by decide
  have hdescent : baseEnd_6530994 < baseStart_6530994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6530994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531001 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 4, 2, 3]
def baseStart_6531001 : Nat := 118140960795 + 6531001 * 2 ^ 59
def prefixEnd_6531001 : Nat := 4983230072969 + 3 ^ 40 * 6531001 * 2
def baseEnd_6531001 : Nat := 3353542667994707162251979

theorem tailTrace_6531001 : CollatzResearch.WordTrace tailWord_6531001 prefixEnd_6531001 3353542667994707162251979 := by
  unfold tailWord_6531001
  simp only [CollatzResearch.WordTrace]
  refine ⟨238205175812306258013888857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158803450541537505342592571 238205175812306258013888857)
  ·
    refine ⟨178653881859229693510416643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238205175812306258013888857 178653881859229693510416643)
    ·
      refine ⟨267980822788844540265624965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178653881859229693510416643 267980822788844540265624965)
      ·
        refine ⟨50246404272908351299804681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267980822788844540265624965 50246404272908351299804681)
        ·
          refine ⟨37684803204681263474853511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50246404272908351299804681 37684803204681263474853511)
          ·
            refine ⟨56527204807021895212280267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37684803204681263474853511 56527204807021895212280267)
            ·
              refine ⟨84790807210532842818420401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56527204807021895212280267 84790807210532842818420401)
              ·
                refine ⟨63593105407899632113815301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84790807210532842818420401 63593105407899632113815301)
                ·
                  refine ⟨11923707263981181021340369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63593105407899632113815301 11923707263981181021340369)
                  ·
                    refine ⟨8942780447985885766005277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11923707263981181021340369 8942780447985885766005277)
                    ·
                      refine ⟨3353542667994707162251979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8942780447985885766005277 3353542667994707162251979)
                      ·
                        rfl

theorem cell23_6531001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_6531001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531001 prefixEnd_6531001 := by exact prefixLift 6531001
  have htrace : WordTrace (prefixWord ++ tailWord_6531001) baseStart_6531001 baseEnd_6531001 := by
    simpa [prefixWord, tailWord_6531001, baseEnd_6531001] using wordTrace_append hprefix tailTrace_6531001
  have hstable : (prefixWord ++ tailWord_6531001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531001).length < 2 ^ (prefixWord ++ tailWord_6531001).sum := by decide
  have hdescent : baseEnd_6531001 < baseStart_6531001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531048 : List Nat := [2, 1, 4, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_6531048 : Nat := 118140960795 + 6531048 * 2 ^ 59
def prefixEnd_6531048 : Nat := 4983230072969 + 3 ^ 40 * 6531048 * 2
def baseEnd_6531048 : Nat := 3353566801585468478364263

theorem tailTrace_6531048 : CollatzResearch.WordTrace tailWord_6531048 prefixEnd_6531048 3353566801585468478364263 := by
  unfold tailWord_6531048
  simp only [CollatzResearch.WordTrace]
  refine ⟨119103445021567992520424899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158804593362090656693899865 119103445021567992520424899)
  ·
    refine ⟨178655167532351988780637349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119103445021567992520424899 178655167532351988780637349)
    ·
      refine ⟨33497843912315997896369503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178655167532351988780637349 33497843912315997896369503)
      ·
        refine ⟨50246765868473996844554255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33497843912315997896369503 50246765868473996844554255)
        ·
          refine ⟨75370148802710995266831383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50246765868473996844554255 75370148802710995266831383)
          ·
            refine ⟨113055223204066492900247075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75370148802710995266831383 113055223204066492900247075)
            ·
              refine ⟨169582834806099739350370613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113055223204066492900247075 169582834806099739350370613)
              ·
                refine ⟨15898390763071850564097245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169582834806099739350370613 15898390763071850564097245)
                ·
                  refine ⟨5961896536151943961536467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15898390763071850564097245 5961896536151943961536467)
                  ·
                    refine ⟨8942844804227915942304701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5961896536151943961536467 8942844804227915942304701)
                    ·
                      refine ⟨3353566801585468478364263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8942844804227915942304701 3353566801585468478364263)
                      ·
                        rfl

theorem cell23_6531048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_6531048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531048 prefixEnd_6531048 := by exact prefixLift 6531048
  have htrace : WordTrace (prefixWord ++ tailWord_6531048) baseStart_6531048 baseEnd_6531048 := by
    simpa [prefixWord, tailWord_6531048, baseEnd_6531048] using wordTrace_append hprefix tailTrace_6531048
  have hstable : (prefixWord ++ tailWord_6531048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531048).length < 2 ^ (prefixWord ++ tailWord_6531048).sum := by decide
  have hdescent : baseEnd_6531048 < baseStart_6531048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531098 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 4, 4]
def baseStart_6531098 : Nat := 118140960795 + 6531098 * 2 ^ 59
def prefixEnd_6531098 : Nat := 4983230072969 + 3 ^ 40 * 6531098 * 2
def baseEnd_6531098 : Nat := 1117864158539397760913011

theorem tailTrace_6531098 : CollatzResearch.WordTrace tailWord_6531098 prefixEnd_6531098 1117864158539397760913011 := by
  unfold tailWord_6531098
  simp only [CollatzResearch.WordTrace]
  refine ⟨59552178423238710895042487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158805809128636562386779965 59552178423238710895042487)
  ·
    refine ⟨89328267634858066342563731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59552178423238710895042487 89328267634858066342563731)
    ·
      refine ⟨133992401452287099513845597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89328267634858066342563731 133992401452287099513845597)
      ·
        refine ⟨50247150544607662317692099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133992401452287099513845597 50247150544607662317692099)
        ·
          refine ⟨75370725816911493476538149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50247150544607662317692099 75370725816911493476538149)
          ·
            refine ⟨14132011090670905026850903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75370725816911493476538149 14132011090670905026850903)
            ·
              refine ⟨21198016636006357540276355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14132011090670905026850903 21198016636006357540276355)
              ·
                refine ⟨31797024954009536310414533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21198016636006357540276355 31797024954009536310414533)
                ·
                  refine ⟨5961942178876788058202725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31797024954009536310414533 5961942178876788058202725)
                  ·
                    refine ⟨1117864158539397760913011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5961942178876788058202725 1117864158539397760913011)
                    ·
                      rfl

theorem cell23_6531098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_6531098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531098 prefixEnd_6531098 := by exact prefixLift 6531098
  have htrace : WordTrace (prefixWord ++ tailWord_6531098) baseStart_6531098 baseEnd_6531098 := by
    simpa [prefixWord, tailWord_6531098, baseEnd_6531098] using wordTrace_append hprefix tailTrace_6531098
  have hstable : (prefixWord ++ tailWord_6531098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531098).length < 2 ^ (prefixWord ++ tailWord_6531098).sum := by decide
  have hdescent : baseEnd_6531098 < baseStart_6531098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531118 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_6531118 : Nat := 118140960795 + 6531118 * 2 ^ 59
def prefixEnd_6531118 : Nat := 4983230072969 + 3 ^ 40 * 6531118 * 2
def baseEnd_6531118 : Nat := 3353602745231283204488941

theorem tailTrace_6531118 : CollatzResearch.WordTrace tailWord_6531118 prefixEnd_6531118 3353602745231283204488941 := by
  unfold tailWord_6531118
  simp only [CollatzResearch.WordTrace]
  refine ⟨29776180394110298374487251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158806295435254924663932005 29776180394110298374487251)
  ·
    refine ⟨44664270591165447561730877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29776180394110298374487251 44664270591165447561730877)
    ·
      refine ⟨16749101471687042835649079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44664270591165447561730877 16749101471687042835649079)
      ·
        refine ⟨25123652207530564253473619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16749101471687042835649079 25123652207530564253473619)
        ·
          refine ⟨37685478311295846380210429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25123652207530564253473619 37685478311295846380210429)
          ·
            refine ⟨14132054366735942392578911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37685478311295846380210429 14132054366735942392578911)
            ·
              refine ⟨21198081550103913588868367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14132054366735942392578911 21198081550103913588868367)
              ·
                refine ⟨31797122325155870383302551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21198081550103913588868367 31797122325155870383302551)
                ·
                  refine ⟨47695683487733805574953827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31797122325155870383302551 47695683487733805574953827)
                  ·
                    refine ⟨71543525231600708362430741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47695683487733805574953827 71543525231600708362430741)
                    ·
                      refine ⟨3353602745231283204488941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71543525231600708362430741 3353602745231283204488941)
                      ·
                        rfl

theorem cell23_6531118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_6531118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531118 prefixEnd_6531118 := by exact prefixLift 6531118
  have htrace : WordTrace (prefixWord ++ tailWord_6531118) baseStart_6531118 baseEnd_6531118 := by
    simpa [prefixWord, tailWord_6531118, baseEnd_6531118] using wordTrace_append hprefix tailTrace_6531118
  have hstable : (prefixWord ++ tailWord_6531118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531118).length < 2 ^ (prefixWord ++ tailWord_6531118).sum := by decide
  have hdescent : baseEnd_6531118 < baseStart_6531118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531142 : List Nat := [6, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_6531142 : Nat := 118140960795 + 6531142 * 2 ^ 59
def prefixEnd_6531142 : Nat := 4983230072969 + 3 ^ 40 * 6531142 * 2
def baseEnd_6531142 : Nat := 3353615068766991110588831

theorem tailTrace_6531142 : CollatzResearch.WordTrace tailWord_6531142 prefixEnd_6531142 3353615068766991110588831 := by
  unfold tailWord_6531142
  simp only [CollatzResearch.WordTrace]
  refine ⟨7444072453274857471711615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158806879003196959396514453 7444072453274857471711615)
  ·
    refine ⟨11166108679912286207567423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7444072453274857471711615 11166108679912286207567423)
    ·
      refine ⟨16749163019868429311351135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11166108679912286207567423 16749163019868429311351135)
      ·
        refine ⟨25123744529802643967026703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16749163019868429311351135 25123744529802643967026703)
        ·
          refine ⟨37685616794703965950540055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25123744529802643967026703 37685616794703965950540055)
          ·
            refine ⟨56528425192055948925810083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37685616794703965950540055 56528425192055948925810083)
            ·
              refine ⟨84792637788083923388715125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56528425192055948925810083 84792637788083923388715125)
              ·
                refine ⟨7949309792632867817692043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84792637788083923388715125 7949309792632867817692043)
                ·
                  refine ⟨11923964688949301726538065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7949309792632867817692043 11923964688949301726538065)
                  ·
                    refine ⟨8942973516711976294903549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11923964688949301726538065 8942973516711976294903549)
                    ·
                      refine ⟨3353615068766991110588831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8942973516711976294903549 3353615068766991110588831)
                      ·
                        rfl

theorem cell23_6531142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_6531142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531142 prefixEnd_6531142 := by exact prefixLift 6531142
  have htrace : WordTrace (prefixWord ++ tailWord_6531142) baseStart_6531142 baseEnd_6531142 := by
    simpa [prefixWord, tailWord_6531142, baseEnd_6531142] using wordTrace_append hprefix tailTrace_6531142
  have hstable : (prefixWord ++ tailWord_6531142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531142).length < 2 ^ (prefixWord ++ tailWord_6531142).sum := by decide
  have hdescent : baseEnd_6531142 < baseStart_6531142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531161 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 2, 3, 4]
def baseStart_6531161 : Nat := 118140960795 + 6531161 * 2 ^ 59
def prefixEnd_6531161 : Nat := 4983230072969 + 3 ^ 40 * 6531161 * 2
def baseEnd_6531161 : Nat := 3353624824899426536251243

theorem tailTrace_6531161 : CollatzResearch.WordTrace tailWord_6531161 prefixEnd_6531161 3353624824899426536251243 := by
  unfold tailWord_6531161
  simp only [CollatzResearch.WordTrace]
  refine ⟨238211011491726605339713337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158807340994484403559808891 238211011491726605339713337)
  ·
    refine ⟨178658258618794954004785003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 238211011491726605339713337 178658258618794954004785003)
    ·
      refine ⟨267987387928192431007177505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178658258618794954004785003 267987387928192431007177505)
      ·
        refine ⟨200990540946144323255383129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267987387928192431007177505 200990540946144323255383129)
        ·
          refine ⟨150742905709608242441537347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200990540946144323255383129 150742905709608242441537347)
          ·
            refine ⟨226114358564412363662306021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150742905709608242441537347 226114358564412363662306021)
            ·
              refine ⟨42396442230827318186682379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226114358564412363662306021 42396442230827318186682379)
              ·
                refine ⟨63594663346240977280023569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42396442230827318186682379 63594663346240977280023569)
                ·
                  refine ⟨47695997509680732960017677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63594663346240977280023569 47695997509680732960017677)
                  ·
                    refine ⟨17885999066130274860006629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47695997509680732960017677 17885999066130274860006629)
                    ·
                      refine ⟨3353624824899426536251243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17885999066130274860006629 3353624824899426536251243)
                      ·
                        rfl

theorem cell23_6531161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_6531161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531161 prefixEnd_6531161 := by exact prefixLift 6531161
  have htrace : WordTrace (prefixWord ++ tailWord_6531161) baseStart_6531161 baseEnd_6531161 := by
    simpa [prefixWord, tailWord_6531161, baseEnd_6531161] using wordTrace_append hprefix tailTrace_6531161
  have hstable : (prefixWord ++ tailWord_6531161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531161).length < 2 ^ (prefixWord ++ tailWord_6531161).sum := by decide
  have hdescent : baseEnd_6531161 < baseStart_6531161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531171 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 2, 6]
def baseStart_6531171 : Nat := 118140960795 + 6531171 * 2 ^ 59
def prefixEnd_6531171 : Nat := 4983230072969 + 3 ^ 40 * 6531171 * 2
def baseEnd_6531171 : Nat := 1117876653235323832375399

theorem tailTrace_6531171 : CollatzResearch.WordTrace tailWord_6531171 prefixEnd_6531171 1117876653235323832375399 := by
  unfold tailWord_6531171
  simp only [CollatzResearch.WordTrace]
  refine ⟨238211376221690377047577367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158807584147793584698384911 238211376221690377047577367)
  ·
    refine ⟨357317064332535565571366051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238211376221690377047577367 357317064332535565571366051)
    ·
      refine ⟨535975596498803348357049077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357317064332535565571366051 535975596498803348357049077)
      ·
        refine ⟨50247712171762813908473351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 535975596498803348357049077 50247712171762813908473351)
        ·
          refine ⟨75371568257644220862710027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50247712171762813908473351 75371568257644220862710027)
          ·
            refine ⟨113057352386466331294065041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75371568257644220862710027 113057352386466331294065041)
            ·
              refine ⟨84793014289849748470548781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113057352386466331294065041 84793014289849748470548781)
              ·
                refine ⟨31797380358693655676455793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84793014289849748470548781 31797380358693655676455793)
                ·
                  refine ⟨23848035269020241757341845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31797380358693655676455793 23848035269020241757341845)
                  ·
                    refine ⟨1117876653235323832375399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23848035269020241757341845 1117876653235323832375399)
                    ·
                      rfl

theorem cell23_6531171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 6].length) (baseStart_6531171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531171 prefixEnd_6531171 := by exact prefixLift 6531171
  have htrace : WordTrace (prefixWord ++ tailWord_6531171) baseStart_6531171 baseEnd_6531171 := by
    simpa [prefixWord, tailWord_6531171, baseEnd_6531171] using wordTrace_append hprefix tailTrace_6531171
  have hstable : (prefixWord ++ tailWord_6531171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531171).length < 2 ^ (prefixWord ++ tailWord_6531171).sum := by decide
  have hdescent : baseEnd_6531171 < baseStart_6531171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6531172 : List Nat := [2, 3, 1, 1, 2, 1, 6, 1, 2, 1, 3]
def baseStart_6531172 : Nat := 118140960795 + 6531172 * 2 ^ 59
def prefixEnd_6531172 : Nat := 4983230072969 + 3 ^ 40 * 6531172 * 2
def baseEnd_6531172 : Nat := 3353630473186625993213693

theorem tailTrace_6531172 : CollatzResearch.WordTrace tailWord_6531172 prefixEnd_6531172 3353630473186625993213693 := by
  unfold tailWord_6531172
  simp only [CollatzResearch.WordTrace]
  refine ⟨119105706347343377109181885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158807608463124502812242513 119105706347343377109181885)
  ·
    refine ⟨44664639880253766415943207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119105706347343377109181885 44664639880253766415943207)
    ·
      refine ⟨66996959820380649623914811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44664639880253766415943207 66996959820380649623914811)
      ·
        refine ⟨100495439730570974435872217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66996959820380649623914811 100495439730570974435872217)
        ·
          refine ⟨75371579797928230826904163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100495439730570974435872217 75371579797928230826904163)
          ·
            refine ⟨113057369696892346240356245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75371579797928230826904163 113057369696892346240356245)
            ·
              refine ⟨5299564204541828730016699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113057369696892346240356245 5299564204541828730016699)
              ·
                refine ⟨7949346306812743095025049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5299564204541828730016699 7949346306812743095025049)
                ·
                  refine ⟨5962009730109557321268787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7949346306812743095025049 5962009730109557321268787)
                  ·
                    refine ⟨8943014595164335981903181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5962009730109557321268787 8943014595164335981903181)
                    ·
                      refine ⟨3353630473186625993213693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8943014595164335981903181 3353630473186625993213693)
                      ·
                        rfl

theorem cell23_6531172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_6531172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6531172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6531172 prefixEnd_6531172 := by exact prefixLift 6531172
  have htrace : WordTrace (prefixWord ++ tailWord_6531172) baseStart_6531172 baseEnd_6531172 := by
    simpa [prefixWord, tailWord_6531172, baseEnd_6531172] using wordTrace_append hprefix tailTrace_6531172
  have hstable : (prefixWord ++ tailWord_6531172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6531172).length < 2 ^ (prefixWord ++ tailWord_6531172).sum := by decide
  have hdescent : baseEnd_6531172 < baseStart_6531172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6531172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
