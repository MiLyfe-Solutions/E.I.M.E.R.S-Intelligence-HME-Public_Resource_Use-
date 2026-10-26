import V185TrunkScan21Chunk075

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_920746 : List Nat := [3, 1, 5, 1, 1, 3, 2, 2, 3]
def baseStart_920746 : Nat := 118140960795 + 920746 * 2 ^ 59
def prefixEnd_920746 : Nat := 4983230072969 + 3 ^ 40 * 920746 * 2
def baseEnd_920746 : Nat := 210126781646559915884699

theorem tailTrace_920746 : CollatzResearch.WordTrace tailWord_920746 prefixEnd_920746 210126781646559915884699 := by
  unfold tailWord_920746
  simp only [CollatzResearch.WordTrace]
  refine ⟨8395591380575491935631523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22388243681534645161684061 8395591380575491935631523)
  ·
    refine ⟨12593387070863237903447285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8395591380575491935631523 12593387070863237903447285)
    ·
      refine ⟨1180630037893428553448183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12593387070863237903447285 1180630037893428553448183)
      ·
        refine ⟨1770945056840142830172275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180630037893428553448183 1770945056840142830172275)
        ·
          refine ⟨2656417585260214245258413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770945056840142830172275 2656417585260214245258413)
          ·
            refine ⟨996156594472580341971905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2656417585260214245258413 996156594472580341971905)
            ·
              refine ⟨747117445854435256478929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 996156594472580341971905 747117445854435256478929)
              ·
                refine ⟨560338084390826442359197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 747117445854435256478929 560338084390826442359197)
                ·
                  refine ⟨210126781646559915884699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560338084390826442359197 210126781646559915884699)
                  ·
                    rfl

theorem cell21_920746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_920746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920746 prefixEnd_920746 := by exact prefixLift 920746
  have htrace : WordTrace (prefixWord ++ tailWord_920746) baseStart_920746 baseEnd_920746 := by
    simpa [prefixWord, tailWord_920746, baseEnd_920746] using wordTrace_append hprefix tailTrace_920746
  have hstable : (prefixWord ++ tailWord_920746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920746).length < 2 ^ (prefixWord ++ tailWord_920746).sum := by decide
  have hdescent : baseEnd_920746 < baseStart_920746 := by decide
  rcases family_descends (prefixWord ++ tailWord_920746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920844 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 6]
def baseStart_920844 : Nat := 118140960795 + 920844 * 2 ^ 59
def prefixEnd_920844 : Nat := 4983230072969 + 3 ^ 40 * 920844 * 2
def baseEnd_920844 : Nat := 210149146581733523251165

theorem tailTrace_920844 : CollatzResearch.WordTrace tailWord_920844 prefixEnd_920844 210149146581733523251165 := by
  unfold tailWord_920844
  simp only [CollatzResearch.WordTrace]
  refine ⟨16792969937973465239796793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22390626583964620319729057 16792969937973465239796793)
  ·
    refine ⟨12594727453480098929847595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16792969937973465239796793 12594727453480098929847595)
    ·
      refine ⟨18892091180220148394771393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12594727453480098929847595 18892091180220148394771393)
      ·
        refine ⟨14169068385165111296078545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18892091180220148394771393 14169068385165111296078545)
        ·
          refine ⟨10626801288873833472058909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14169068385165111296078545 10626801288873833472058909)
          ·
            refine ⟨3985050483327687552022091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10626801288873833472058909 3985050483327687552022091)
            ·
              refine ⟨5977575724991531328033137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3985050483327687552022091 5977575724991531328033137)
              ·
                refine ⟨4483181793743648496024853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5977575724991531328033137 4483181793743648496024853)
                ·
                  refine ⟨210149146581733523251165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4483181793743648496024853 210149146581733523251165)
                  ·
                    rfl

theorem cell21_920844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_920844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920844 prefixEnd_920844 := by exact prefixLift 920844
  have htrace : WordTrace (prefixWord ++ tailWord_920844) baseStart_920844 baseEnd_920844 := by
    simpa [prefixWord, tailWord_920844, baseEnd_920844] using wordTrace_append hprefix tailTrace_920844
  have hstable : (prefixWord ++ tailWord_920844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920844).length < 2 ^ (prefixWord ++ tailWord_920844).sum := by decide
  have hdescent : baseEnd_920844 < baseStart_920844 := by decide
  rcases family_descends (prefixWord ++ tailWord_920844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920850 : List Nat := [3, 2, 4, 2, 2, 1, 7]
def baseStart_920850 : Nat := 118140960795 + 920850 * 2 ^ 59
def prefixEnd_920850 : Nat := 4983230072969 + 3 ^ 40 * 920850 * 2
def baseEnd_920850 : Nat := 23350057318164316239017

theorem tailTrace_920850 : CollatzResearch.WordTrace tailWord_920850 prefixEnd_920850 23350057318164316239017 := by
  unfold tailWord_920850
  simp only [CollatzResearch.WordTrace]
  refine ⟨8396539678481298376078001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22390772475950129002874669 8396539678481298376078001)
  ·
    refine ⟨6297404758860973782058501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8396539678481298376078001 6297404758860973782058501)
    ·
      refine ⟨1180763392286432584135969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6297404758860973782058501 1180763392286432584135969)
      ·
        refine ⟨885572544214824438101977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1180763392286432584135969 885572544214824438101977)
        ·
          refine ⟨664179408161118328576483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 885572544214824438101977 664179408161118328576483)
          ·
            refine ⟨996269112241677492864725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664179408161118328576483 996269112241677492864725)
            ·
              refine ⟨23350057318164316239017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 996269112241677492864725 23350057318164316239017)
              ·
                rfl

theorem cell21_920850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 7].length) (baseStart_920850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920850 prefixEnd_920850 := by exact prefixLift 920850
  have htrace : WordTrace (prefixWord ++ tailWord_920850) baseStart_920850 baseEnd_920850 := by
    simpa [prefixWord, tailWord_920850, baseEnd_920850] using wordTrace_append hprefix tailTrace_920850
  have hstable : (prefixWord ++ tailWord_920850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920850).length < 2 ^ (prefixWord ++ tailWord_920850).sum := by decide
  have hdescent : baseEnd_920850 < baseStart_920850 := by decide
  rcases family_descends (prefixWord ++ tailWord_920850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920861 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 6]
def baseStart_920861 : Nat := 118140960795 + 920861 * 2 ^ 59
def prefixEnd_920861 : Nat := 4983230072969 + 3 ^ 40 * 920861 * 2
def baseEnd_920861 : Nat := 210153026213345271467797

theorem tailTrace_920861 : CollatzResearch.WordTrace tailWord_920861 prefixEnd_920861 210153026213345271467797 := by
  unfold tailWord_920861
  simp only [CollatzResearch.WordTrace]
  refine ⟨33586559916885342382962437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22391039944590228255308291 33586559916885342382962437)
  ·
    refine ⟨6297479984416001696805457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33586559916885342382962437 6297479984416001696805457)
    ·
      refine ⟨4723109988312001272604093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6297479984416001696805457 4723109988312001272604093)
      ·
        refine ⟨1771166245617000477226535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4723109988312001272604093 1771166245617000477226535)
        ·
          refine ⟨2656749368425500715839803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1771166245617000477226535 2656749368425500715839803)
          ·
            refine ⟨3985124052638251073759705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2656749368425500715839803 3985124052638251073759705)
            ·
              refine ⟨2988843039478688305319779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3985124052638251073759705 2988843039478688305319779)
              ·
                refine ⟨4483264559218032457979669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2988843039478688305319779 4483264559218032457979669)
                ·
                  refine ⟨210153026213345271467797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4483264559218032457979669 210153026213345271467797)
                  ·
                    rfl

theorem cell21_920861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_920861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920861 prefixEnd_920861 := by exact prefixLift 920861
  have htrace : WordTrace (prefixWord ++ tailWord_920861) baseStart_920861 baseEnd_920861 := by
    simpa [prefixWord, tailWord_920861, baseEnd_920861] using wordTrace_append hprefix tailTrace_920861
  have hstable : (prefixWord ++ tailWord_920861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920861).length < 2 ^ (prefixWord ++ tailWord_920861).sum := by decide
  have hdescent : baseEnd_920861 < baseStart_920861 := by decide
  rcases family_descends (prefixWord ++ tailWord_920861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920864 : List Nat := [2, 1, 1, 5, 4, 1, 1, 1, 5]
def baseStart_920864 : Nat := 118140960795 + 920864 * 2 ^ 59
def prefixEnd_920864 : Nat := 4983230072969 + 3 ^ 40 * 920864 * 2
def baseEnd_920864 : Nat := 210153710854217932917791

theorem tailTrace_920864 : CollatzResearch.WordTrace tailWord_920864 prefixEnd_920864 210153710854217932917791 := by
  unfold tailWord_920864
  simp only [CollatzResearch.WordTrace]
  refine ⟨16793334667937236947660823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22391112890582982596881097 16793334667937236947660823)
  ·
    refine ⟨25190002001905855421491235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16793334667937236947660823 25190002001905855421491235)
    ·
      refine ⟨37785003002858783132236853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25190002001905855421491235 37785003002858783132236853)
      ·
        refine ⟨3542344031518010918647205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37785003002858783132236853 3542344031518010918647205)
        ·
          refine ⟨664189505909627047246351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3542344031518010918647205 664189505909627047246351)
          ·
            refine ⟨996284258864440570869527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664189505909627047246351 996284258864440570869527)
            ·
              refine ⟨1494426388296660856304291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996284258864440570869527 1494426388296660856304291)
              ·
                refine ⟨2241639582444991284456437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1494426388296660856304291 2241639582444991284456437)
                ·
                  refine ⟨210153710854217932917791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2241639582444991284456437 210153710854217932917791)
                  ·
                    rfl

theorem cell21_920864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 5].length) (baseStart_920864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920864 prefixEnd_920864 := by exact prefixLift 920864
  have htrace : WordTrace (prefixWord ++ tailWord_920864) baseStart_920864 baseEnd_920864 := by
    simpa [prefixWord, tailWord_920864, baseEnd_920864] using wordTrace_append hprefix tailTrace_920864
  have hstable : (prefixWord ++ tailWord_920864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920864).length < 2 ^ (prefixWord ++ tailWord_920864).sum := by decide
  have hdescent : baseEnd_920864 < baseStart_920864 := by decide
  rcases family_descends (prefixWord ++ tailWord_920864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920909 : List Nat := [1, 6, 1, 3, 2, 8]
def baseStart_920909 : Nat := 118140960795 + 920909 * 2 ^ 59
def prefixEnd_920909 : Nat := 4983230072969 + 3 ^ 40 * 920909 * 2
def baseEnd_920909 : Nat := 7783851128418809432137

theorem tailTrace_920909 : CollatzResearch.WordTrace tailWord_920909 prefixEnd_920909 7783851128418809432137 := by
  unfold tailWord_920909
  simp only [CollatzResearch.WordTrace]
  refine ⟨33588310620711446580709781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22392207080474297720473187 33588310620711446580709781)
  ·
    refine ⟨1574452060345849058470771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33588310620711446580709781 1574452060345849058470771)
    ·
      refine ⟨2361678090518773587706157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1574452060345849058470771 2361678090518773587706157)
      ·
        refine ⟨885629283944540095389809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2361678090518773587706157 885629283944540095389809)
        ·
          refine ⟨664221962958405071542357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 885629283944540095389809 664221962958405071542357)
          ·
            refine ⟨7783851128418809432137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 664221962958405071542357 7783851128418809432137)
            ·
              rfl

theorem cell21_920909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 8].length) (baseStart_920909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920909 prefixEnd_920909 := by exact prefixLift 920909
  have htrace : WordTrace (prefixWord ++ tailWord_920909) baseStart_920909 baseEnd_920909 := by
    simpa [prefixWord, tailWord_920909, baseEnd_920909] using wordTrace_append hprefix tailTrace_920909
  have hstable : (prefixWord ++ tailWord_920909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920909).length < 2 ^ (prefixWord ++ tailWord_920909).sum := by decide
  have hdescent : baseEnd_920909 < baseStart_920909 := by decide
  rcases family_descends (prefixWord ++ tailWord_920909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920951 : List Nat := [1, 1, 3, 1, 1, 2, 7, 5]
def baseStart_920951 : Nat := 118140960795 + 920951 * 2 ^ 59
def prefixEnd_920951 : Nat := 4983230072969 + 3 ^ 40 * 920951 * 2
def baseEnd_920951 : Nat := 70057855146508371655871

theorem tailTrace_920951 : CollatzResearch.WordTrace tailWord_920951 prefixEnd_920951 70057855146508371655871 := by
  unfold tailWord_920951
  simp only [CollatzResearch.WordTrace]
  refine ⟨33589842486559287753738707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22393228324372858502492471 33589842486559287753738707)
  ·
    refine ⟨50384763729838931630608061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33589842486559287753738707 50384763729838931630608061)
    ·
      refine ⟨18894286398689599361478023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50384763729838931630608061 18894286398689599361478023)
      ·
        refine ⟨28341429598034399042217035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18894286398689599361478023 28341429598034399042217035)
        ·
          refine ⟨42512144397051598563325553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28341429598034399042217035 42512144397051598563325553)
          ·
            refine ⟨31884108297788698922494165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42512144397051598563325553 31884108297788698922494165)
            ·
              refine ⟨747283788229422630995957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 31884108297788698922494165 747283788229422630995957)
              ·
                refine ⟨70057855146508371655871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 747283788229422630995957 70057855146508371655871)
                ·
                  rfl

theorem cell21_920951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 5].length) (baseStart_920951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_920951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_920951 prefixEnd_920951 := by exact prefixLift 920951
  have htrace : WordTrace (prefixWord ++ tailWord_920951) baseStart_920951 baseEnd_920951 := by
    simpa [prefixWord, tailWord_920951, baseEnd_920951] using wordTrace_append hprefix tailTrace_920951
  have hstable : (prefixWord ++ tailWord_920951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920951).length < 2 ^ (prefixWord ++ tailWord_920951).sum := by decide
  have hdescent : baseEnd_920951 < baseStart_920951 := by decide
  rcases family_descends (prefixWord ++ tailWord_920951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921044 : List Nat := [2, 4, 1, 2, 3, 1, 2, 6]
def baseStart_921044 : Nat := 118140960795 + 921044 * 2 ^ 59
def prefixEnd_921044 : Nat := 4983230072969 + 3 ^ 40 * 921044 * 2
def baseEnd_921044 : Nat := 70064929768859206639141

theorem tailTrace_921044 : CollatzResearch.WordTrace tailWord_921044 prefixEnd_921044 70064929768859206639141 := by
  unfold tailWord_921044
  simp only [CollatzResearch.WordTrace]
  refine ⟨16796617237611182318437093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22395489650148243091249457 16796617237611182318437093)
  ·
    refine ⟨3149365732052096684706955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16796617237611182318437093 3149365732052096684706955)
    ·
      refine ⟨4724048598078145027060433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3149365732052096684706955 4724048598078145027060433)
      ·
        refine ⟨3543036448558608770295325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4724048598078145027060433 3543036448558608770295325)
        ·
          refine ⟨1328638668209478288860747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3543036448558608770295325 1328638668209478288860747)
          ·
            refine ⟨1992958002314217433291121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328638668209478288860747 1992958002314217433291121)
            ·
              refine ⟨1494718501735663074968341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1992958002314217433291121 1494718501735663074968341)
              ·
                refine ⟨70064929768859206639141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1494718501735663074968341 70064929768859206639141)
                ·
                  rfl

theorem cell21_921044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 6].length) (baseStart_921044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921044 prefixEnd_921044 := by exact prefixLift 921044
  have htrace : WordTrace (prefixWord ++ tailWord_921044) baseStart_921044 baseEnd_921044 := by
    simpa [prefixWord, tailWord_921044, baseEnd_921044] using wordTrace_append hprefix tailTrace_921044
  have hstable : (prefixWord ++ tailWord_921044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921044).length < 2 ^ (prefixWord ++ tailWord_921044).sum := by decide
  have hdescent : baseEnd_921044 < baseStart_921044 := by decide
  rcases family_descends (prefixWord ++ tailWord_921044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921092 : List Nat := [2, 3, 2, 3, 2, 1, 1, 4, 3]
def baseStart_921092 : Nat := 118140960795 + 921092 * 2 ^ 59
def prefixEnd_921092 : Nat := 4983230072969 + 3 ^ 40 * 921092 * 2
def baseEnd_921092 : Nat := 210205743560540203117325

theorem tailTrace_921092 : CollatzResearch.WordTrace tailWord_921092 prefixEnd_921092 210205743560540203117325 := by
  unfold tailWord_921092
  simp only [CollatzResearch.WordTrace]
  refine ⟨16797492589524234417310765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22396656786032312556414353 16797492589524234417310765)
  ·
    refine ⟨6299059721071587906491537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16797492589524234417310765 6299059721071587906491537)
    ·
      refine ⟨4724294790803690929868653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6299059721071587906491537 4724294790803690929868653)
      ·
        refine ⟨1771610546551384098700745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4724294790803690929868653 1771610546551384098700745)
        ·
          refine ⟨1328707909913538074025559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1771610546551384098700745 1328707909913538074025559)
          ·
            refine ⟨1993061864870307111038339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328707909913538074025559 1993061864870307111038339)
            ·
              refine ⟨2989592797305460666557509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1993061864870307111038339 2989592797305460666557509)
              ·
                refine ⟨560548649494773874979533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2989592797305460666557509 560548649494773874979533)
                ·
                  refine ⟨210205743560540203117325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560548649494773874979533 210205743560540203117325)
                  ·
                    rfl

theorem cell21_921092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_921092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921092 prefixEnd_921092 := by exact prefixLift 921092
  have htrace : WordTrace (prefixWord ++ tailWord_921092) baseStart_921092 baseEnd_921092 := by
    simpa [prefixWord, tailWord_921092, baseEnd_921092] using wordTrace_append hprefix tailTrace_921092
  have hstable : (prefixWord ++ tailWord_921092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921092).length < 2 ^ (prefixWord ++ tailWord_921092).sum := by decide
  have hdescent : baseEnd_921092 < baseStart_921092 := by decide
  rcases family_descends (prefixWord ++ tailWord_921092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921120 : List Nat := [2, 1, 1, 6, 1, 2, 3, 5]
def baseStart_921120 : Nat := 118140960795 + 921120 * 2 ^ 59
def prefixEnd_921120 : Nat := 4983230072969 + 3 ^ 40 * 921120 * 2
def baseEnd_921120 : Nat := 70070711180672792216867

theorem tailTrace_921120 : CollatzResearch.WordTrace tailWord_921120 prefixEnd_921120 70070711180672792216867 := by
  unfold tailWord_921120
  simp only [CollatzResearch.WordTrace]
  refine ⟨16798003211473514808320407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22397337615298019744427209 16798003211473514808320407)
  ·
    refine ⟨25197004817210272212480611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16798003211473514808320407 25197004817210272212480611)
    ·
      refine ⟨37795507225815408318720917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25197004817210272212480611 37795507225815408318720917)
      ·
        refine ⟨1771664401210097264940043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37795507225815408318720917 1771664401210097264940043)
        ·
          refine ⟨2657496601815145897410065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1771664401210097264940043 2657496601815145897410065)
          ·
            refine ⟨1993122451361359423057549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2657496601815145897410065 1993122451361359423057549)
            ·
              refine ⟨747420919260509783646581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1993122451361359423057549 747420919260509783646581)
              ·
                refine ⟨70070711180672792216867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 747420919260509783646581 70070711180672792216867)
                ·
                  rfl

theorem cell21_921120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 5].length) (baseStart_921120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921120 prefixEnd_921120 := by exact prefixLift 921120
  have htrace : WordTrace (prefixWord ++ tailWord_921120) baseStart_921120 baseEnd_921120 := by
    simpa [prefixWord, tailWord_921120, baseEnd_921120] using wordTrace_append hprefix tailTrace_921120
  have hstable : (prefixWord ++ tailWord_921120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921120).length < 2 ^ (prefixWord ++ tailWord_921120).sum := by decide
  have hdescent : baseEnd_921120 < baseStart_921120 := by decide
  rcases family_descends (prefixWord ++ tailWord_921120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921162 : List Nat := [3, 1, 2, 1, 1, 3, 2, 8]
def baseStart_921162 : Nat := 118140960795 + 921162 * 2 ^ 59
def prefixEnd_921162 : Nat := 4983230072969 + 3 ^ 40 * 921162 * 2
def baseEnd_921162 : Nat := 70073906171411878983505

theorem tailTrace_921162 : CollatzResearch.WordTrace tailWord_921162 prefixEnd_921162 70073906171411878983505 := by
  unfold tailWord_921162
  simp only [CollatzResearch.WordTrace]
  refine ⟨8399384572198717697417435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22398358859196580526446493 8399384572198717697417435)
  ·
    refine ⟨12599076858298076546126153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8399384572198717697417435 12599076858298076546126153)
    ·
      refine ⟨9449307643723557409594615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12599076858298076546126153 9449307643723557409594615)
      ·
        refine ⟨14173961465585336114391923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9449307643723557409594615 14173961465585336114391923)
        ·
          refine ⟨21260942198378004171587885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14173961465585336114391923 21260942198378004171587885)
          ·
            refine ⟨7972853324391751564345457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21260942198378004171587885 7972853324391751564345457)
            ·
              refine ⟨5979639993293813673259093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7972853324391751564345457 5979639993293813673259093)
              ·
                refine ⟨70073906171411878983505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5979639993293813673259093 70073906171411878983505)
                ·
                  rfl

theorem cell21_921162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_921162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921162 prefixEnd_921162 := by exact prefixLift 921162
  have htrace : WordTrace (prefixWord ++ tailWord_921162) baseStart_921162 baseEnd_921162 := by
    simpa [prefixWord, tailWord_921162, baseEnd_921162] using wordTrace_append hprefix tailTrace_921162
  have hstable : (prefixWord ++ tailWord_921162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921162).length < 2 ^ (prefixWord ++ tailWord_921162).sum := by decide
  have hdescent : baseEnd_921162 < baseStart_921162 := by decide
  rcases family_descends (prefixWord ++ tailWord_921162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921334 : List Nat := [5, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_921334 : Nat := 118140960795 + 921334 * 2 ^ 59
def prefixEnd_921334 : Nat := 4983230072969 + 3 ^ 40 * 921334 * 2
def baseEnd_921334 : Nat := 210260971257601560083497

theorem tailTrace_921334 : CollatzResearch.WordTrace tailWord_921334 prefixEnd_921334 210260971257601560083497 := by
  unfold tailWord_921334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2100238227760734010308191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22402541096114496109954037 2100238227760734010308191)
  ·
    refine ⟨3150357341641101015462287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2100238227760734010308191 3150357341641101015462287)
    ·
      refine ⟨4725536012461651523193431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3150357341641101015462287 4725536012461651523193431)
      ·
        refine ⟨7088304018692477284790147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4725536012461651523193431 7088304018692477284790147)
        ·
          refine ⟨10632456028038715927185221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7088304018692477284790147 10632456028038715927185221)
          ·
            refine ⟨1993585505257259236347229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10632456028038715927185221 1993585505257259236347229)
            ·
              refine ⟨747594564471472213630211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1993585505257259236347229 747594564471472213630211)
              ·
                refine ⟨1121391846707208320445317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747594564471472213630211 1121391846707208320445317)
                ·
                  refine ⟨210260971257601560083497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1121391846707208320445317 210260971257601560083497)
                  ·
                    rfl

theorem cell21_921334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_921334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921334 prefixEnd_921334 := by exact prefixLift 921334
  have htrace : WordTrace (prefixWord ++ tailWord_921334) baseStart_921334 baseEnd_921334 := by
    simpa [prefixWord, tailWord_921334, baseEnd_921334] using wordTrace_append hprefix tailTrace_921334
  have hstable : (prefixWord ++ tailWord_921334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921334).length < 2 ^ (prefixWord ++ tailWord_921334).sum := by decide
  have hdescent : baseEnd_921334 < baseStart_921334 := by decide
  rcases family_descends (prefixWord ++ tailWord_921334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921345 : List Nat := [1, 2, 4, 1, 1, 1, 4, 2, 5]
def baseStart_921345 : Nat := 118140960795 + 921345 * 2 ^ 59
def prefixEnd_921345 : Nat := 4983230072969 + 3 ^ 40 * 921345 * 2
def baseEnd_921345 : Nat := 210263481607467985400141

theorem tailTrace_921345 : CollatzResearch.WordTrace tailWord_921345 prefixEnd_921345 210263481607467985400141 := by
  unfold tailWord_921345
  simp only [CollatzResearch.WordTrace]
  refine ⟨33604212847131893043581489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22402808564754595362387659 33604212847131893043581489)
  ·
    refine ⟨25203159635348919782686117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33604212847131893043581489 25203159635348919782686117)
    ·
      refine ⟨4725592431627922459253647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25203159635348919782686117 4725592431627922459253647)
      ·
        refine ⟨7088388647441883688880471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4725592431627922459253647 7088388647441883688880471)
        ·
          refine ⟨10632582971162825533320707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7088388647441883688880471 10632582971162825533320707)
          ·
            refine ⟨15948874456744238299981061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10632582971162825533320707 15948874456744238299981061)
            ·
              refine ⟨2990413960639544681246449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15948874456744238299981061 2990413960639544681246449)
              ·
                refine ⟨2242810470479658510934837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2990413960639544681246449 2242810470479658510934837)
                ·
                  refine ⟨210263481607467985400141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2242810470479658510934837 210263481607467985400141)
                  ·
                    rfl

theorem cell21_921345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_921345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921345 prefixEnd_921345 := by exact prefixLift 921345
  have htrace : WordTrace (prefixWord ++ tailWord_921345) baseStart_921345 baseEnd_921345 := by
    simpa [prefixWord, tailWord_921345, baseEnd_921345] using wordTrace_append hprefix tailTrace_921345
  have hstable : (prefixWord ++ tailWord_921345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921345).length < 2 ^ (prefixWord ++ tailWord_921345).sum := by decide
  have hdescent : baseEnd_921345 < baseStart_921345 := by decide
  rcases family_descends (prefixWord ++ tailWord_921345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921348 : List Nat := [2, 3, 2, 2, 1, 4, 2, 5]
def baseStart_921348 : Nat := 118140960795 + 921348 * 2 ^ 59
def prefixEnd_921348 : Nat := 4983230072969 + 3 ^ 40 * 921348 * 2
def baseEnd_921348 : Nat := 70088055416113548950045

theorem tailTrace_921348 : CollatzResearch.WordTrace tailWord_921348 prefixEnd_921348 70088055416113548950045 := by
  unfold tailWord_921348
  simp only [CollatzResearch.WordTrace]
  refine ⟨16802161133060512277970349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22402881510747349703960465 16802161133060512277970349)
  ·
    refine ⟨6300810424897692104238881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16802161133060512277970349 6300810424897692104238881)
    ·
      refine ⟨4725607818673269078179161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6300810424897692104238881 4725607818673269078179161)
      ·
        refine ⟨3544205864004951808634371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4725607818673269078179161 3544205864004951808634371)
        ·
          refine ⟨5316308796007427712951557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3544205864004951808634371 5316308796007427712951557)
          ·
            refine ⟨996807899251392696178417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5316308796007427712951557 996807899251392696178417)
            ·
              refine ⟨747605924438544522133813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 996807899251392696178417 747605924438544522133813)
              ·
                refine ⟨70088055416113548950045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 747605924438544522133813 70088055416113548950045)
                ·
                  rfl

theorem cell21_921348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 5].length) (baseStart_921348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921348 prefixEnd_921348 := by exact prefixLift 921348
  have htrace : WordTrace (prefixWord ++ tailWord_921348) baseStart_921348 baseEnd_921348 := by
    simpa [prefixWord, tailWord_921348, baseEnd_921348] using wordTrace_append hprefix tailTrace_921348
  have hstable : (prefixWord ++ tailWord_921348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921348).length < 2 ^ (prefixWord ++ tailWord_921348).sum := by decide
  have hdescent : baseEnd_921348 < baseStart_921348 := by decide
  rcases family_descends (prefixWord ++ tailWord_921348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921376 : List Nat := [2, 1, 1, 5, 1, 1, 2, 4, 4]
def baseStart_921376 : Nat := 118140960795 + 921376 * 2 ^ 59
def prefixEnd_921376 : Nat := 4983230072969 + 3 ^ 40 * 921376 * 2
def baseEnd_921376 : Nat := 210270556229818820383411

theorem tailTrace_921376 : CollatzResearch.WordTrace tailWord_921376 prefixEnd_921376 210270556229818820383411 := by
  unfold tailWord_921376
  simp only [CollatzResearch.WordTrace]
  refine ⟨16802671755009792668979991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22403562340013056891973321 16802671755009792668979991)
  ·
    refine ⟨25204007632514689003469987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16802671755009792668979991 25204007632514689003469987)
    ·
      refine ⟨37806011448772033505204981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25204007632514689003469987 37806011448772033505204981)
      ·
        refine ⟨3544313573322378141112967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37806011448772033505204981 3544313573322378141112967)
        ·
          refine ⟨5316470359983567211669451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3544313573322378141112967 5316470359983567211669451)
          ·
            refine ⟨7974705539975350817504177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5316470359983567211669451 7974705539975350817504177)
            ·
              refine ⟨5981029154981513113128133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7974705539975350817504177 5981029154981513113128133)
              ·
                refine ⟨1121442966559033708711525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5981029154981513113128133 1121442966559033708711525)
                ·
                  refine ⟨210270556229818820383411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1121442966559033708711525 210270556229818820383411)
                  ·
                    rfl

theorem cell21_921376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_921376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921376 prefixEnd_921376 := by exact prefixLift 921376
  have htrace : WordTrace (prefixWord ++ tailWord_921376) baseStart_921376 baseEnd_921376 := by
    simpa [prefixWord, tailWord_921376, baseEnd_921376] using wordTrace_append hprefix tailTrace_921376
  have hstable : (prefixWord ++ tailWord_921376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921376).length < 2 ^ (prefixWord ++ tailWord_921376).sum := by decide
  have hdescent : baseEnd_921376 < baseStart_921376 := by decide
  rcases family_descends (prefixWord ++ tailWord_921376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921393 : List Nat := [1, 2, 2, 3, 2, 2, 4, 1, 4]
def baseStart_921393 : Nat := 118140960795 + 921393 * 2 ^ 59
def prefixEnd_921393 : Nat := 4983230072969 + 3 ^ 40 * 921393 * 2
def baseEnd_921393 : Nat := 210274435861430568600043

theorem tailTrace_921393 : CollatzResearch.WordTrace tailWord_921393 prefixEnd_921393 210274435861430568600043 := by
  unfold tailWord_921393
  simp only [CollatzResearch.WordTrace]
  refine ⟨33605963550957997241328833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22403975700638664827552555 33605963550957997241328833)
  ·
    refine ⟨25204472663218497930996625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33605963550957997241328833 25204472663218497930996625)
    ·
      refine ⟨18903354497413873448247469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25204472663218497930996625 18903354497413873448247469)
      ·
        refine ⟨7088757936530202543092801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18903354497413873448247469 7088757936530202543092801)
        ·
          refine ⟨5316568452397651907319601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7088757936530202543092801 5316568452397651907319601)
          ·
            refine ⟨3987426339298238930489701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5316568452397651907319601 3987426339298238930489701)
            ·
              refine ⟨747642438618419799466819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3987426339298238930489701 747642438618419799466819)
              ·
                refine ⟨1121463657927629699200229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747642438618419799466819 1121463657927629699200229)
                ·
                  refine ⟨210274435861430568600043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1121463657927629699200229 210274435861430568600043)
                  ·
                    rfl

theorem cell21_921393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 4].length) (baseStart_921393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921393 prefixEnd_921393 := by exact prefixLift 921393
  have htrace : WordTrace (prefixWord ++ tailWord_921393) baseStart_921393 baseEnd_921393 := by
    simpa [prefixWord, tailWord_921393, baseEnd_921393] using wordTrace_append hprefix tailTrace_921393
  have hstable : (prefixWord ++ tailWord_921393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921393).length < 2 ^ (prefixWord ++ tailWord_921393).sum := by decide
  have hdescent : baseEnd_921393 < baseStart_921393 := by decide
  rcases family_descends (prefixWord ++ tailWord_921393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921452 : List Nat := [2, 2, 1, 1, 4, 2, 2, 3, 4]
def baseStart_921452 : Nat := 118140960795 + 921452 * 2 ^ 59
def prefixEnd_921452 : Nat := 4983230072969 + 3 ^ 40 * 921452 * 2
def baseEnd_921452 : Nat := 210287900465259577116589

theorem tailTrace_921452 : CollatzResearch.WordTrace tailWord_921452 prefixEnd_921452 210287900465259577116589 := by
  unfold tailWord_921452
  simp only [CollatzResearch.WordTrace]
  refine ⟨16804057728872125158863305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22405410305162833545151073 16804057728872125158863305)
  ·
    refine ⟨12603043296654093869147479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16804057728872125158863305 12603043296654093869147479)
    ·
      refine ⟨18904564944981140803721219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12603043296654093869147479 18904564944981140803721219)
      ·
        refine ⟨28356847417471711205581829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18904564944981140803721219 28356847417471711205581829)
        ·
          refine ⟨5316908890775945851046593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28356847417471711205581829 5316908890775945851046593)
          ·
            refine ⟨3987681668081959388284945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5316908890775945851046593 3987681668081959388284945)
            ·
              refine ⟨2990761251061469541213709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3987681668081959388284945 2990761251061469541213709)
              ·
                refine ⟨1121535469148051077955141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2990761251061469541213709 1121535469148051077955141)
                ·
                  refine ⟨210287900465259577116589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1121535469148051077955141 210287900465259577116589)
                  ·
                    rfl

theorem cell21_921452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_921452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921452 prefixEnd_921452 := by exact prefixLift 921452
  have htrace : WordTrace (prefixWord ++ tailWord_921452) baseStart_921452 baseEnd_921452 := by
    simpa [prefixWord, tailWord_921452, baseEnd_921452] using wordTrace_append hprefix tailTrace_921452
  have hstable : (prefixWord ++ tailWord_921452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921452).length < 2 ^ (prefixWord ++ tailWord_921452).sum := by decide
  have hdescent : baseEnd_921452 < baseStart_921452 := by decide
  rcases family_descends (prefixWord ++ tailWord_921452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921562 : List Nat := [3, 1, 1, 2, 5, 2, 2, 1, 4]
def baseStart_921562 : Nat := 118140960795 + 921562 * 2 ^ 59
def prefixEnd_921562 : Nat := 4983230072969 + 3 ^ 40 * 921562 * 2
def baseEnd_921562 : Nat := 210313003963923830283031

theorem tailTrace_921562 : CollatzResearch.WordTrace tailWord_921562 prefixEnd_921562 210313003963923830283031 := by
  unfold tailWord_921562
  simp only [CollatzResearch.WordTrace]
  refine ⟨8403031871836434776057735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22408084991563826069487293 8403031871836434776057735)
  ·
    refine ⟨12604547807754652164086603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8403031871836434776057735 12604547807754652164086603)
    ·
      refine ⟨18906821711631978246129905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12604547807754652164086603 18906821711631978246129905)
      ·
        refine ⟨14180116283723983684597429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18906821711631978246129905 14180116283723983684597429)
        ·
          refine ⟨1329385901599123470431009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14180116283723983684597429 1329385901599123470431009)
          ·
            refine ⟨997039426199342602823257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1329385901599123470431009 997039426199342602823257)
            ·
              refine ⟨747779569649506952117443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 997039426199342602823257 747779569649506952117443)
              ·
                refine ⟨1121669354474260428176165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747779569649506952117443 1121669354474260428176165)
                ·
                  refine ⟨210313003963923830283031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1121669354474260428176165 210313003963923830283031)
                  ·
                    rfl

theorem cell21_921562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_921562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921562 prefixEnd_921562 := by exact prefixLift 921562
  have htrace : WordTrace (prefixWord ++ tailWord_921562) baseStart_921562 baseEnd_921562 := by
    simpa [prefixWord, tailWord_921562, baseEnd_921562] using wordTrace_append hprefix tailTrace_921562
  have hstable : (prefixWord ++ tailWord_921562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921562).length < 2 ^ (prefixWord ++ tailWord_921562).sum := by decide
  have hdescent : baseEnd_921562 < baseStart_921562 := by decide
  rcases family_descends (prefixWord ++ tailWord_921562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921607 : List Nat := [1, 1, 4, 3, 1, 2, 4, 2, 3]
def baseStart_921607 : Nat := 118140960795 + 921607 * 2 ^ 59
def prefixEnd_921607 : Nat := 4983230072969 + 3 ^ 40 * 921607 * 2
def baseEnd_921607 : Nat := 210323273577013752032939

theorem tailTrace_921607 : CollatzResearch.WordTrace tailWord_921607 prefixEnd_921607 210323273577013752032939 := by
  unfold tailWord_921607
  simp only [CollatzResearch.WordTrace]
  refine ⟨33613768772182711789619075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22409179181455141193079383 33613768772182711789619075)
  ·
    refine ⟨50420653158274067684428613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33613768772182711789619075 50420653158274067684428613)
    ·
      refine ⟨9453872467176387690830365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50420653158274067684428613 9453872467176387690830365)
      ·
        refine ⟨3545202175191145384061387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9453872467176387690830365 3545202175191145384061387)
        ·
          refine ⟨5317803262786718076092081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3545202175191145384061387 5317803262786718076092081)
          ·
            refine ⟨3988352447090038557069061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5317803262786718076092081 3988352447090038557069061)
            ·
              refine ⟨747816083829382229450449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3988352447090038557069061 747816083829382229450449)
              ·
                refine ⟨560862062872036672087837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 747816083829382229450449 560862062872036672087837)
                ·
                  refine ⟨210323273577013752032939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 560862062872036672087837 210323273577013752032939)
                  ·
                    rfl

theorem cell21_921607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 3].length) (baseStart_921607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921607 prefixEnd_921607 := by exact prefixLift 921607
  have htrace : WordTrace (prefixWord ++ tailWord_921607) baseStart_921607 baseEnd_921607 := by
    simpa [prefixWord, tailWord_921607, baseEnd_921607] using wordTrace_append hprefix tailTrace_921607
  have hstable : (prefixWord ++ tailWord_921607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921607).length < 2 ^ (prefixWord ++ tailWord_921607).sum := by decide
  have hdescent : baseEnd_921607 < baseStart_921607 := by decide
  rcases family_descends (prefixWord ++ tailWord_921607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921725 : List Nat := [1, 4, 1, 1, 3, 2, 3, 1, 5]
def baseStart_921725 : Nat := 118140960795 + 921725 * 2 ^ 59
def prefixEnd_921725 : Nat := 4983230072969 + 3 ^ 40 * 921725 * 2
def baseEnd_921725 : Nat := 210350202784671769066031

theorem tailTrace_921725 : CollatzResearch.WordTrace tailWord_921725 prefixEnd_921725 210350202784671769066031 := by
  unfold tailWord_921725
  simp only [CollatzResearch.WordTrace]
  refine ⟨33618072585755217942414629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22412048390503478628276419 33618072585755217942414629)
  ·
    refine ⟨6303388609829103364202743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33618072585755217942414629 6303388609829103364202743)
    ·
      refine ⟨9455082914743655046304115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6303388609829103364202743 9455082914743655046304115)
      ·
        refine ⟨14182624372115482569456173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9455082914743655046304115 14182624372115482569456173)
        ·
          refine ⟨5318484139543305963546065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14182624372115482569456173 5318484139543305963546065)
          ·
            refine ⟨3988863104657479472659549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5318484139543305963546065 3988863104657479472659549)
            ·
              refine ⟨1495823664246554802247331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3988863104657479472659549 1495823664246554802247331)
              ·
                refine ⟨2243735496369832203370997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495823664246554802247331 2243735496369832203370997)
                ·
                  refine ⟨210350202784671769066031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2243735496369832203370997 210350202784671769066031)
                  ·
                    rfl

theorem cell21_921725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_921725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921725 prefixEnd_921725 := by exact prefixLift 921725
  have htrace : WordTrace (prefixWord ++ tailWord_921725) baseStart_921725 baseEnd_921725 := by
    simpa [prefixWord, tailWord_921725, baseEnd_921725] using wordTrace_append hprefix tailTrace_921725
  have hstable : (prefixWord ++ tailWord_921725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921725).length < 2 ^ (prefixWord ++ tailWord_921725).sum := by decide
  have hdescent : baseEnd_921725 < baseStart_921725 := by decide
  rcases family_descends (prefixWord ++ tailWord_921725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921770 : List Nat := [3, 1, 5, 1, 11]
def baseStart_921770 : Nat := 118140960795 + 921770 * 2 ^ 59
def prefixEnd_921770 : Nat := 4983230072969 + 3 ^ 40 * 921770 * 2
def baseEnd_921770 : Nat := 2597042869108169022419

theorem tailTrace_921770 : CollatzResearch.WordTrace tailWord_921770 prefixEnd_921770 2597042869108169022419 := by
  unfold tailWord_921770
  simp only [CollatzResearch.WordTrace]
  refine ⟨8404928467648047656950691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22413142580394793751868509 8404928467648047656950691)
  ·
    refine ⟨12607392701472071485426037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8404928467648047656950691 12607392701472071485426037)
    ·
      refine ⟨1181943065763006701758691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12607392701472071485426037 1181943065763006701758691)
      ·
        refine ⟨1772914598644510052638037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1181943065763006701758691 1772914598644510052638037)
        ·
          refine ⟨2597042869108169022419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1772914598644510052638037 2597042869108169022419)
          ·
            rfl

theorem cell21_921770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 11].length) (baseStart_921770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921770 prefixEnd_921770 := by exact prefixLift 921770
  have htrace : WordTrace (prefixWord ++ tailWord_921770) baseStart_921770 baseEnd_921770 := by
    simpa [prefixWord, tailWord_921770, baseEnd_921770] using wordTrace_append hprefix tailTrace_921770
  have hstable : (prefixWord ++ tailWord_921770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921770).length < 2 ^ (prefixWord ++ tailWord_921770).sum := by decide
  have hdescent : baseEnd_921770 < baseStart_921770 := by decide
  rcases family_descends (prefixWord ++ tailWord_921770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921773 : List Nat := [1, 5, 2, 1, 2, 2, 2, 2, 4]
def baseStart_921773 : Nat := 118140960795 + 921773 * 2 ^ 59
def prefixEnd_921773 : Nat := 4983230072969 + 3 ^ 40 * 921773 * 2
def baseEnd_921773 : Nat := 210361157038634352265933

theorem tailTrace_921773 : CollatzResearch.WordTrace tailWord_921773 prefixEnd_921773 210361157038634352265933 := by
  unfold tailWord_921773
  simp only [CollatzResearch.WordTrace]
  refine ⟨33619823289581322140161973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22413215526387548093441315 33619823289581322140161973)
  ·
    refine ⟨3151858433398248950640185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33619823289581322140161973 3151858433398248950640185)
    ·
      refine ⟨2363893825048686712980139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3151858433398248950640185 2363893825048686712980139)
      ·
        refine ⟨3545840737573030069470209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2363893825048686712980139 3545840737573030069470209)
        ·
          refine ⟨2659380553179772552102657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3545840737573030069470209 2659380553179772552102657)
          ·
            refine ⟨1994535414884829414076993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2659380553179772552102657 1994535414884829414076993)
            ·
              refine ⟨1495901561163622060557745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1994535414884829414076993 1495901561163622060557745)
              ·
                refine ⟨1121926170872716545418309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1495901561163622060557745 1121926170872716545418309)
                ·
                  refine ⟨210361157038634352265933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1121926170872716545418309 210361157038634352265933)
                  ·
                    rfl

theorem cell21_921773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_921773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921773 prefixEnd_921773 := by exact prefixLift 921773
  have htrace : WordTrace (prefixWord ++ tailWord_921773) baseStart_921773 baseEnd_921773 := by
    simpa [prefixWord, tailWord_921773, baseEnd_921773] using wordTrace_append hprefix tailTrace_921773
  have hstable : (prefixWord ++ tailWord_921773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921773).length < 2 ^ (prefixWord ++ tailWord_921773).sum := by decide
  have hdescent : baseEnd_921773 < baseStart_921773 := by decide
  rcases family_descends (prefixWord ++ tailWord_921773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921784 : List Nat := [2, 1, 2, 1, 2, 1, 4, 3, 5]
def baseStart_921784 : Nat := 118140960795 + 921784 * 2 ^ 59
def prefixEnd_921784 : Nat := 4983230072969 + 3 ^ 40 * 921784 * 2
def baseEnd_921784 : Nat := 210363667388500777582577

theorem tailTrace_921784 : CollatzResearch.WordTrace tailWord_921784 prefixEnd_921784 210363667388500777582577 := by
  unfold tailWord_921784
  simp only [CollatzResearch.WordTrace]
  refine ⟨16810112246270735509406203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22413482995027647345874937 16810112246270735509406203)
  ·
    refine ⟨25215168369406103264109305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16810112246270735509406203 25215168369406103264109305)
    ·
      refine ⟨18911376277054577448081979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25215168369406103264109305 18911376277054577448081979)
      ·
        refine ⟨28367064415581866172122969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18911376277054577448081979 28367064415581866172122969)
        ·
          refine ⟨21275298311686399629092227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28367064415581866172122969 21275298311686399629092227)
          ·
            refine ⟨31912947467529599443638341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21275298311686399629092227 31912947467529599443638341)
            ·
              refine ⟨5983677650161799895682189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31912947467529599443638341 5983677650161799895682189)
              ·
                refine ⟨2243879118810674960880821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5983677650161799895682189 2243879118810674960880821)
                ·
                  refine ⟨210363667388500777582577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2243879118810674960880821 210363667388500777582577)
                  ·
                    rfl

theorem cell21_921784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_921784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921784 prefixEnd_921784 := by exact prefixLift 921784
  have htrace : WordTrace (prefixWord ++ tailWord_921784) baseStart_921784 baseEnd_921784 := by
    simpa [prefixWord, tailWord_921784, baseEnd_921784] using wordTrace_append hprefix tailTrace_921784
  have hstable : (prefixWord ++ tailWord_921784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921784).length < 2 ^ (prefixWord ++ tailWord_921784).sum := by decide
  have hdescent : baseEnd_921784 < baseStart_921784 := by decide
  rcases family_descends (prefixWord ++ tailWord_921784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921804 : List Nat := [2, 2, 1, 6, 1, 1, 3, 5]
def baseStart_921804 : Nat := 118140960795 + 921804 * 2 ^ 59
def prefixEnd_921804 : Nat := 4983230072969 + 3 ^ 40 * 921804 * 2
def baseEnd_921804 : Nat := 70122743886995062416401

theorem tailTrace_921804 : CollatzResearch.WordTrace tailWord_921804 prefixEnd_921804 70122743886995062416401 := by
  unfold tailWord_921804
  simp only [CollatzResearch.WordTrace]
  refine ⟨16810476976234507217270233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22413969301646009623026977 16810476976234507217270233)
  ·
    refine ⟨12607857732175880412952675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16810476976234507217270233 12607857732175880412952675)
    ·
      refine ⟨18911786598263820619429013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12607857732175880412952675 18911786598263820619429013)
      ·
        refine ⟨886489996793616591535735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18911786598263820619429013 886489996793616591535735)
        ·
          refine ⟨1329734995190424887303603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886489996793616591535735 1329734995190424887303603)
          ·
            refine ⟨1994602492785637330955405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329734995190424887303603 1994602492785637330955405)
            ·
              refine ⟨747975934794613999108277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1994602492785637330955405 747975934794613999108277)
              ·
                refine ⟨70122743886995062416401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 747975934794613999108277 70122743886995062416401)
                ·
                  rfl

theorem cell21_921804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 5].length) (baseStart_921804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921804 prefixEnd_921804 := by exact prefixLift 921804
  have htrace : WordTrace (prefixWord ++ tailWord_921804) baseStart_921804 baseEnd_921804 := by
    simpa [prefixWord, tailWord_921804, baseEnd_921804] using wordTrace_append hprefix tailTrace_921804
  have hstable : (prefixWord ++ tailWord_921804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921804).length < 2 ^ (prefixWord ++ tailWord_921804).sum := by decide
  have hdescent : baseEnd_921804 < baseStart_921804 := by decide
  rcases family_descends (prefixWord ++ tailWord_921804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921832 : List Nat := [2, 1, 4, 1, 2, 2, 3, 2, 4]
def baseStart_921832 : Nat := 118140960795 + 921832 * 2 ^ 59
def prefixEnd_921832 : Nat := 4983230072969 + 3 ^ 40 * 921832 * 2
def baseEnd_921832 : Nat := 210374621642463360782479

theorem tailTrace_921832 : CollatzResearch.WordTrace tailWord_921832 prefixEnd_921832 210374621642463360782479 := by
  unfold tailWord_921832
  simp only [CollatzResearch.WordTrace]
  refine ⟨16810987598183787608279875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22414650130911716811039833 16810987598183787608279875)
  ·
    refine ⟨25216481397275681412419813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16810987598183787608279875 25216481397275681412419813)
    ·
      refine ⟨4728090261989190264828715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25216481397275681412419813 4728090261989190264828715)
      ·
        refine ⟨7092135392983785397243073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4728090261989190264828715 7092135392983785397243073)
        ·
          refine ⟨5319101544737839047932305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7092135392983785397243073 5319101544737839047932305)
          ·
            refine ⟨3989326158553379285949229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5319101544737839047932305 3989326158553379285949229)
            ·
              refine ⟨1495997309457517232230961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3989326158553379285949229 1495997309457517232230961)
              ·
                refine ⟨1121997982093137924173221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1495997309457517232230961 1121997982093137924173221)
                ·
                  refine ⟨210374621642463360782479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1121997982093137924173221 210374621642463360782479)
                  ·
                    rfl

theorem cell21_921832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_921832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921832 prefixEnd_921832 := by exact prefixLift 921832
  have htrace : WordTrace (prefixWord ++ tailWord_921832) baseStart_921832 baseEnd_921832 := by
    simpa [prefixWord, tailWord_921832, baseEnd_921832] using wordTrace_append hprefix tailTrace_921832
  have hstable : (prefixWord ++ tailWord_921832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921832).length < 2 ^ (prefixWord ++ tailWord_921832).sum := by decide
  have hdescent : baseEnd_921832 < baseStart_921832 := by decide
  rcases family_descends (prefixWord ++ tailWord_921832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921863 : List Nat := [1, 1, 4, 5, 1, 1, 1, 7]
def baseStart_921863 : Nat := 118140960795 + 921863 * 2 ^ 59
def prefixEnd_921863 : Nat := 4983230072969 + 3 ^ 40 * 921863 * 2
def baseEnd_921863 : Nat := 70127232088271398588583

theorem tailTrace_921863 : CollatzResearch.WordTrace tailWord_921863 prefixEnd_921863 70127232088271398588583 := by
  unfold tailWord_921863
  simp only [CollatzResearch.WordTrace]
  refine ⟨33623105859255267510938243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22415403906170178340625495 33623105859255267510938243)
  ·
    refine ⟨50434658788882901266407365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33623105859255267510938243 50434658788882901266407365)
    ·
      refine ⟨9456498522915543987451381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50434658788882901266407365 9456498522915543987451381)
      ·
        refine ⟨886546736523332248823567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9456498522915543987451381 886546736523332248823567)
        ·
          refine ⟨1329820104784998373235351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886546736523332248823567 1329820104784998373235351)
          ·
            refine ⟨1994730157177497559853027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329820104784998373235351 1994730157177497559853027)
            ·
              refine ⟨2992095235766246339779541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1994730157177497559853027 2992095235766246339779541)
              ·
                refine ⟨70127232088271398588583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2992095235766246339779541 70127232088271398588583)
                ·
                  rfl

theorem cell21_921863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 7].length) (baseStart_921863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921863 prefixEnd_921863 := by exact prefixLift 921863
  have htrace : WordTrace (prefixWord ++ tailWord_921863) baseStart_921863 baseEnd_921863 := by
    simpa [prefixWord, tailWord_921863, baseEnd_921863] using wordTrace_append hprefix tailTrace_921863
  have hstable : (prefixWord ++ tailWord_921863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921863).length < 2 ^ (prefixWord ++ tailWord_921863).sum := by decide
  have hdescent : baseEnd_921863 < baseStart_921863 := by decide
  rcases family_descends (prefixWord ++ tailWord_921863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921891 : List Nat := [1, 1, 1, 4, 2, 2, 2, 4, 4]
def baseStart_921891 : Nat := 118140960795 + 921891 * 2 ^ 59
def prefixEnd_921891 : Nat := 4983230072969 + 3 ^ 40 * 921891 * 2
def baseEnd_921891 : Nat := 210388086246292369299025

theorem tailTrace_921891 : CollatzResearch.WordTrace tailWord_921891 prefixEnd_921891 210388086246292369299025 := by
  unfold tailWord_921891
  simp only [CollatzResearch.WordTrace]
  refine ⟨33624127103153828292957527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22416084735435885528638351 33624127103153828292957527)
  ·
    refine ⟨50436190654730742439436291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33624127103153828292957527 50436190654730742439436291)
    ·
      refine ⟨75654285982096113659154437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50436190654730742439436291 75654285982096113659154437)
      ·
        refine ⟨14185178621643021311091457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75654285982096113659154437 14185178621643021311091457)
        ·
          refine ⟨10638883966232265983318593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14185178621643021311091457 10638883966232265983318593)
          ·
            refine ⟨7979162974674199487488945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10638883966232265983318593 7979162974674199487488945)
            ·
              refine ⟨5984372231005649615616709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7979162974674199487488945 5984372231005649615616709)
              ·
                refine ⟨1122069793313559302928133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5984372231005649615616709 1122069793313559302928133)
                ·
                  refine ⟨210388086246292369299025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1122069793313559302928133 210388086246292369299025)
                  ·
                    rfl

theorem cell21_921891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 4].length) (baseStart_921891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921891 prefixEnd_921891 := by exact prefixLift 921891
  have htrace : WordTrace (prefixWord ++ tailWord_921891) baseStart_921891 baseEnd_921891 := by
    simpa [prefixWord, tailWord_921891, baseEnd_921891] using wordTrace_append hprefix tailTrace_921891
  have hstable : (prefixWord ++ tailWord_921891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921891).length < 2 ^ (prefixWord ++ tailWord_921891).sum := by decide
  have hdescent : baseEnd_921891 < baseStart_921891 := by decide
  rcases family_descends (prefixWord ++ tailWord_921891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921998 : List Nat := [4, 1, 1, 4, 1, 2, 8]
def baseStart_921998 : Nat := 118140960795 + 921998 * 2 ^ 59
def prefixEnd_921998 : Nat := 4983230072969 + 3 ^ 40 * 921998 * 2
def baseEnd_921998 : Nat := 23379167233787106779497

theorem tailTrace_921998 : CollatzResearch.WordTrace tailWord_921998 prefixEnd_921998 23379167233787106779497 := by
  unfold tailWord_921998
  simp only [CollatzResearch.WordTrace]
  refine ⟨4203503714220773195887831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22418686475844123711401765 4203503714220773195887831)
  ·
    refine ⟨6305255571331159793831747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4203503714220773195887831 6305255571331159793831747)
    ·
      refine ⟨9457883356996739690747621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6305255571331159793831747 9457883356996739690747621)
      ·
        refine ⟨1773353129436888692015179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9457883356996739690747621 1773353129436888692015179)
        ·
          refine ⟨2660029694155333038022769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1773353129436888692015179 2660029694155333038022769)
          ·
            refine ⟨1995022270616499778517077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2660029694155333038022769 1995022270616499778517077)
            ·
              refine ⟨23379167233787106779497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1995022270616499778517077 23379167233787106779497)
              ·
                rfl

theorem cell21_921998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 8].length) (baseStart_921998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_921998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_921998 prefixEnd_921998 := by exact prefixLift 921998
  have htrace : WordTrace (prefixWord ++ tailWord_921998) baseStart_921998 baseEnd_921998 := by
    simpa [prefixWord, tailWord_921998, baseEnd_921998] using wordTrace_append hprefix tailTrace_921998
  have hstable : (prefixWord ++ tailWord_921998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921998).length < 2 ^ (prefixWord ++ tailWord_921998).sum := by decide
  have hdescent : baseEnd_921998 < baseStart_921998 := by decide
  rcases family_descends (prefixWord ++ tailWord_921998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922046 : List Nat := [4, 2, 1, 1, 1, 1, 5, 3, 3]
def baseStart_922046 : Nat := 118140960795 + 922046 * 2 ^ 59
def prefixEnd_922046 : Nat := 4983230072969 + 3 ^ 40 * 922046 * 2
def baseEnd_922046 : Nat := 210423459358046544215375

theorem tailTrace_922046 : CollatzResearch.WordTrace tailWord_922046 prefixEnd_922046 210423459358046544215375 := by
  unfold tailWord_922046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4203722552199036220606249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22419853611728193176566661 4203722552199036220606249)
  ·
    refine ⟨3152791914149277165454687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4203722552199036220606249 3152791914149277165454687)
    ·
      refine ⟨4729187871223915748182031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3152791914149277165454687 4729187871223915748182031)
      ·
        refine ⟨7093781806835873622273047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4729187871223915748182031 7093781806835873622273047)
        ·
          refine ⟨10640672710253810433409571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7093781806835873622273047 10640672710253810433409571)
          ·
            refine ⟨15961009065380715650114357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10640672710253810433409571 15961009065380715650114357)
            ·
              refine ⟨1496344599879442092198221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15961009065380715650114357 1496344599879442092198221)
              ·
                refine ⟨561129224954790784574333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1496344599879442092198221 561129224954790784574333)
                ·
                  refine ⟨210423459358046544215375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561129224954790784574333 210423459358046544215375)
                  ·
                    rfl

theorem cell21_922046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_922046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_922046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_922046 prefixEnd_922046 := by exact prefixLift 922046
  have htrace : WordTrace (prefixWord ++ tailWord_922046) baseStart_922046 baseEnd_922046 := by
    simpa [prefixWord, tailWord_922046, baseEnd_922046] using wordTrace_append hprefix tailTrace_922046
  have hstable : (prefixWord ++ tailWord_922046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922046).length < 2 ^ (prefixWord ++ tailWord_922046).sum := by decide
  have hdescent : baseEnd_922046 < baseStart_922046 := by decide
  rcases family_descends (prefixWord ++ tailWord_922046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922049 : List Nat := [1, 2, 7, 1, 2, 1, 7]
def baseStart_922049 : Nat := 118140960795 + 922049 * 2 ^ 59
def prefixEnd_922049 : Nat := 4983230072969 + 3 ^ 40 * 922049 * 2
def baseEnd_922049 : Nat := 23380460444324356185041

theorem tailTrace_922049 : CollatzResearch.WordTrace tailWord_922049 prefixEnd_922049 23380460444324356185041 := by
  unfold tailWord_922049
  simp only [CollatzResearch.WordTrace]
  refine ⟨33629889836581421277209201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22419926557720947518139467 33629889836581421277209201)
  ·
    refine ⟨25222417377436065957906901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33629889836581421277209201 25222417377436065957906901)
    ·
      refine ⟨591150407283657795888443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 25222417377436065957906901 591150407283657795888443)
      ·
        refine ⟨886725610925486693832665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591150407283657795888443 886725610925486693832665)
        ·
          refine ⟨665044208194115020374499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 886725610925486693832665 665044208194115020374499)
          ·
            refine ⟨997566312291172530561749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665044208194115020374499 997566312291172530561749)
            ·
              refine ⟨23380460444324356185041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 997566312291172530561749 23380460444324356185041)
              ·
                rfl

theorem cell21_922049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 7].length) (baseStart_922049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_922049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_922049 prefixEnd_922049 := by exact prefixLift 922049
  have htrace : WordTrace (prefixWord ++ tailWord_922049) baseStart_922049 baseEnd_922049 := by
    simpa [prefixWord, tailWord_922049, baseEnd_922049] using wordTrace_append hprefix tailTrace_922049
  have hstable : (prefixWord ++ tailWord_922049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922049).length < 2 ^ (prefixWord ++ tailWord_922049).sum := by decide
  have hdescent : baseEnd_922049 < baseStart_922049 := by decide
  rcases family_descends (prefixWord ++ tailWord_922049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922181 : List Nat := [1, 3, 1, 1, 1, 5, 2, 4, 3]
def baseStart_922181 : Nat := 118140960795 + 922181 * 2 ^ 59
def prefixEnd_922181 : Nat := 4983230072969 + 3 ^ 40 * 922181 * 2
def baseEnd_922181 : Nat := 210454268197316309465099

theorem tailTrace_922181 : CollatzResearch.WordTrace tailWord_922181 prefixEnd_922181 210454268197316309465099 := by
  unfold tailWord_922181
  simp only [CollatzResearch.WordTrace]
  refine ⟨33634704272103207821014397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22423136181402138547342931 33634704272103207821014397)
  ·
    refine ⟨12613014102038702932880399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33634704272103207821014397 12613014102038702932880399)
    ·
      refine ⟨18919521153058054399320599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12613014102038702932880399 18919521153058054399320599)
      ·
        refine ⟨28379281729587081598980899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18919521153058054399320599 28379281729587081598980899)
        ·
          refine ⟨42568922594380622398471349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28379281729587081598980899 42568922594380622398471349)
          ·
            refine ⟨3990836493223183349856689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42568922594380622398471349 3990836493223183349856689)
            ·
              refine ⟨2993127369917387512392517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3990836493223183349856689 2993127369917387512392517)
              ·
                refine ⟨561211381859510158573597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2993127369917387512392517 561211381859510158573597)
                ·
                  refine ⟨210454268197316309465099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561211381859510158573597 210454268197316309465099)
                  ·
                    rfl

theorem cell21_922181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_922181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_922181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_922181 prefixEnd_922181 := by exact prefixLift 922181
  have htrace : WordTrace (prefixWord ++ tailWord_922181) baseStart_922181 baseEnd_922181 := by
    simpa [prefixWord, tailWord_922181, baseEnd_922181] using wordTrace_append hprefix tailTrace_922181
  have hstable : (prefixWord ++ tailWord_922181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922181).length < 2 ^ (prefixWord ++ tailWord_922181).sum := by decide
  have hdescent : baseEnd_922181 < baseStart_922181 := by decide
  rcases family_descends (prefixWord ++ tailWord_922181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922209 : List Nat := [1, 2, 3, 1, 1, 5, 1, 7]
def baseStart_922209 : Nat := 118140960795 + 922209 * 2 ^ 59
def prefixEnd_922209 : Nat := 4983230072969 + 3 ^ 40 * 922209 * 2
def baseEnd_922209 : Nat := 70153552726264827666125

theorem tailTrace_922209 : CollatzResearch.WordTrace tailWord_922209 prefixEnd_922209 70153552726264827666125 := by
  unfold tailWord_922209
  simp only [CollatzResearch.WordTrace]
  refine ⟨33635725516001768603033681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22423817010667845735355787 33635725516001768603033681)
  ·
    refine ⟨25226794137001326452275261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33635725516001768603033681 25226794137001326452275261)
    ·
      refine ⟨9460047801375497419603223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25226794137001326452275261 9460047801375497419603223)
      ·
        refine ⟨14190071702063246129404835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9460047801375497419603223 14190071702063246129404835)
        ·
          refine ⟨21285107553094869194107253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14190071702063246129404835 21285107553094869194107253)
          ·
            refine ⟨1995478833102643986947555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21285107553094869194107253 1995478833102643986947555)
            ·
              refine ⟨2993218249653965980421333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1995478833102643986947555 2993218249653965980421333)
              ·
                refine ⟨70153552726264827666125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2993218249653965980421333 70153552726264827666125)
                ·
                  rfl

theorem cell21_922209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 7].length) (baseStart_922209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_922209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_922209 prefixEnd_922209 := by exact prefixLift 922209
  have htrace : WordTrace (prefixWord ++ tailWord_922209) baseStart_922209 baseEnd_922209 := by
    simpa [prefixWord, tailWord_922209, baseEnd_922209] using wordTrace_append hprefix tailTrace_922209
  have hstable : (prefixWord ++ tailWord_922209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922209).length < 2 ^ (prefixWord ++ tailWord_922209).sum := by decide
  have hdescent : baseEnd_922209 < baseStart_922209 := by decide
  rcases family_descends (prefixWord ++ tailWord_922209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922223 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 7]
def baseStart_922223 : Nat := 118140960795 + 922223 * 2 ^ 59
def prefixEnd_922223 : Nat := 4983230072969 + 3 ^ 40 * 922223 * 2
def baseEnd_922223 : Nat := 210463853169533569765013

theorem tailTrace_922223 : CollatzResearch.WordTrace tailWord_922223 prefixEnd_922223 210463853169533569765013 := by
  unfold tailWord_922223
  simp only [CollatzResearch.WordTrace]
  refine ⟨33636236137951048994043323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22424157425300699329362215 33636236137951048994043323)
  ·
    refine ⟨50454354206926573491064985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33636236137951048994043323 50454354206926573491064985)
    ·
      refine ⟨37840765655194930118298739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50454354206926573491064985 37840765655194930118298739)
      ·
        refine ⟨56761148482792395177448109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37840765655194930118298739 56761148482792395177448109)
        ·
          refine ⟨21285430681047148191543041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56761148482792395177448109 21285430681047148191543041)
          ·
            refine ⟨15964073010785361143657281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21285430681047148191543041 15964073010785361143657281)
            ·
              refine ⟨11973054758089020857742961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15964073010785361143657281 11973054758089020857742961)
              ·
                refine ⟨8979791068566765643307221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11973054758089020857742961 8979791068566765643307221)
                ·
                  refine ⟨210463853169533569765013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8979791068566765643307221 210463853169533569765013)
                  ·
                    rfl

theorem cell21_922223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 7].length) (baseStart_922223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_922223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_922223 prefixEnd_922223 := by exact prefixLift 922223
  have htrace : WordTrace (prefixWord ++ tailWord_922223) baseStart_922223 baseEnd_922223 := by
    simpa [prefixWord, tailWord_922223, baseEnd_922223] using wordTrace_append hprefix tailTrace_922223
  have hstable : (prefixWord ++ tailWord_922223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922223).length < 2 ^ (prefixWord ++ tailWord_922223).sum := by decide
  have hdescent : baseEnd_922223 < baseStart_922223 := by decide
  rcases family_descends (prefixWord ++ tailWord_922223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922226 : List Nat := [3, 2, 1, 2, 4, 2, 7]
def baseStart_922226 : Nat := 118140960795 + 922226 * 2 ^ 59
def prefixEnd_922226 : Nat := 4983230072969 + 3 ^ 40 * 922226 * 2
def baseEnd_922226 : Nat := 23384948645600692357223

theorem tailTrace_922226 : CollatzResearch.WordTrace tailWord_922226 prefixEnd_922226 23384948645600692357223 := by
  unfold tailWord_922226
  simp only [CollatzResearch.WordTrace]
  refine ⟨8409086389235045126600633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22424230371293453670935021 8409086389235045126600633)
  ·
    refine ⟨6306814791926283844950475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8409086389235045126600633 6306814791926283844950475)
    ·
      refine ⟨9460222187889425767425713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6306814791926283844950475 9460222187889425767425713)
      ·
        refine ⟨7095166640917069325569285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9460222187889425767425713 7095166640917069325569285)
        ·
          refine ⟨1330343745171950498544241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7095166640917069325569285 1330343745171950498544241)
          ·
            refine ⟨997757808878962873908181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1330343745171950498544241 997757808878962873908181)
            ·
              refine ⟨23384948645600692357223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 997757808878962873908181 23384948645600692357223)
              ·
                rfl

theorem cell21_922226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 7].length) (baseStart_922226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_922226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_922226 prefixEnd_922226 := by exact prefixLift 922226
  have htrace : WordTrace (prefixWord ++ tailWord_922226) baseStart_922226 baseEnd_922226 := by
    simpa [prefixWord, tailWord_922226, baseEnd_922226] using wordTrace_append hprefix tailTrace_922226
  have hstable : (prefixWord ++ tailWord_922226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922226).length < 2 ^ (prefixWord ++ tailWord_922226).sum := by decide
  have hdescent : baseEnd_922226 < baseStart_922226 := by decide
  rcases family_descends (prefixWord ++ tailWord_922226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922240 : List Nat := [2, 1, 1, 2, 1, 5, 3, 1, 5]
def baseStart_922240 : Nat := 118140960795 + 922240 * 2 ^ 59
def prefixEnd_922240 : Nat := 4983230072969 + 3 ^ 40 * 922240 * 2
def baseEnd_922240 : Nat := 210467732801145317981645

theorem tailTrace_922240 : CollatzResearch.WordTrace tailWord_922240 prefixEnd_922240 210467732801145317981645 := by
  unfold tailWord_922240
  simp only [CollatzResearch.WordTrace]
  refine ⟨16818428089444730448706087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22424570785926307264941449 16818428089444730448706087)
  ·
    refine ⟨25227642134167095673059131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16818428089444730448706087 25227642134167095673059131)
    ·
      refine ⟨37841463201250643509588697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25227642134167095673059131 37841463201250643509588697)
      ·
        refine ⟨28381097400937982632191523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37841463201250643509588697 28381097400937982632191523)
        ·
          refine ⟨42571646101406973948287285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28381097400937982632191523 42571646101406973948287285)
          ·
            refine ⟨3991091822006903807651933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42571646101406973948287285 3991091822006903807651933)
            ·
              refine ⟨1496659433252588927869475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3991091822006903807651933 1496659433252588927869475)
              ·
                refine ⟨2244989149878883391804213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1496659433252588927869475 2244989149878883391804213)
                ·
                  refine ⟨210467732801145317981645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2244989149878883391804213 210467732801145317981645)
                  ·
                    rfl

theorem cell21_922240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_922240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_922240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_922240 prefixEnd_922240 := by exact prefixLift 922240
  have htrace : WordTrace (prefixWord ++ tailWord_922240) baseStart_922240 baseEnd_922240 := by
    simpa [prefixWord, tailWord_922240, baseEnd_922240] using wordTrace_append hprefix tailTrace_922240
  have hstable : (prefixWord ++ tailWord_922240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922240).length < 2 ^ (prefixWord ++ tailWord_922240).sum := by decide
  have hdescent : baseEnd_922240 < baseStart_922240 := by decide
  rcases family_descends (prefixWord ++ tailWord_922240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922285 : List Nat := [1, 5, 2, 1, 1, 11]
def baseStart_922285 : Nat := 118140960795 + 922285 * 2 ^ 59
def prefixEnd_922285 : Nat := 4983230072969 + 3 ^ 40 * 922285 * 2
def baseEnd_922285 : Nat := 7795481570897601471539

theorem tailTrace_922285 : CollatzResearch.WordTrace tailWord_922285 prefixEnd_922285 7795481570897601471539 := by
  unfold tailWord_922285
  simp only [CollatzResearch.WordTrace]
  refine ⟨33638497463726433582800309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22425664975817622388533539 33638497463726433582800309)
  ·
    refine ⟨3153609137224353148387529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33638497463726433582800309 3153609137224353148387529)
    ·
      refine ⟨2365206852918264861290647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3153609137224353148387529 2365206852918264861290647)
      ·
        refine ⟨3547810279377397291935971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2365206852918264861290647 3547810279377397291935971)
        ·
          refine ⟨5321715419066095937903957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3547810279377397291935971 5321715419066095937903957)
          ·
            refine ⟨7795481570897601471539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5321715419066095937903957 7795481570897601471539)
            ·
              rfl

theorem cell21_922285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 11].length) (baseStart_922285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_922285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_922285 prefixEnd_922285 := by exact prefixLift 922285
  have htrace : WordTrace (prefixWord ++ tailWord_922285) baseStart_922285 baseEnd_922285 := by
    simpa [prefixWord, tailWord_922285, baseEnd_922285] using wordTrace_append hprefix tailTrace_922285
  have hstable : (prefixWord ++ tailWord_922285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922285).length < 2 ^ (prefixWord ++ tailWord_922285).sum := by decide
  have hdescent : baseEnd_922285 < baseStart_922285 := by decide
  rcases family_descends (prefixWord ++ tailWord_922285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922316 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 7]
def baseStart_922316 : Nat := 118140960795 + 922316 * 2 ^ 59
def prefixEnd_922316 : Nat := 4983230072969 + 3 ^ 40 * 922316 * 2
def baseEnd_922316 : Nat := 210485077036586074714823

theorem tailTrace_922316 : CollatzResearch.WordTrace tailWord_922316 prefixEnd_922316 210485077036586074714823 := by
  unfold tailWord_922316
  simp only [CollatzResearch.WordTrace]
  refine ⟨16819814063307062938589401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22426418751076083918119201 16819814063307062938589401)
  ·
    refine ⟨12614860547480297203942051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16819814063307062938589401 12614860547480297203942051)
    ·
      refine ⟨18922290821220445805913077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12614860547480297203942051 18922290821220445805913077)
      ·
        refine ⟨1773964764489416794304351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18922290821220445805913077 1773964764489416794304351)
        ·
          refine ⟨2660947146734125191456527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1773964764489416794304351 2660947146734125191456527)
          ·
            refine ⟨3991420720101187787184791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2660947146734125191456527 3991420720101187787184791)
            ·
              refine ⟨5987131080151781680777187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3991420720101187787184791 5987131080151781680777187)
              ·
                refine ⟨8980696620227672521165781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5987131080151781680777187 8980696620227672521165781)
                ·
                  refine ⟨210485077036586074714823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8980696620227672521165781 210485077036586074714823)
                  ·
                    rfl

theorem cell21_922316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_922316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_922316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_922316 prefixEnd_922316 := by exact prefixLift 922316
  have htrace : WordTrace (prefixWord ++ tailWord_922316) baseStart_922316 baseEnd_922316 := by
    simpa [prefixWord, tailWord_922316, baseEnd_922316] using wordTrace_append hprefix tailTrace_922316
  have hstable : (prefixWord ++ tailWord_922316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922316).length < 2 ^ (prefixWord ++ tailWord_922316).sum := by decide
  have hdescent : baseEnd_922316 < baseStart_922316 := by decide
  rcases family_descends (prefixWord ++ tailWord_922316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922330 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 6]
def baseStart_922330 : Nat := 118140960795 + 922330 * 2 ^ 59
def prefixEnd_922330 : Nat := 4983230072969 + 3 ^ 40 * 922330 * 2
def baseEnd_922330 : Nat := 210488272027325161481461

theorem tailTrace_922330 : CollatzResearch.WordTrace tailWord_922330 prefixEnd_922330 210488272027325161481461 := by
  unfold tailWord_922330
  simp only [CollatzResearch.WordTrace]
  refine ⟨8410034687140851567047111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22426759165708937512125629 8410034687140851567047111)
  ·
    refine ⟨12615052030711277350570667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8410034687140851567047111 12615052030711277350570667)
    ·
      refine ⟨18922578046066916025856001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12615052030711277350570667 18922578046066916025856001)
      ·
        refine ⟨14191933534550187019392001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18922578046066916025856001 14191933534550187019392001)
        ·
          refine ⟨10643950150912640264544001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14191933534550187019392001 10643950150912640264544001)
          ·
            refine ⟨7982962613184480198408001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10643950150912640264544001 7982962613184480198408001)
            ·
              refine ⟨5987221959888360148806001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7982962613184480198408001 5987221959888360148806001)
              ·
                refine ⟨4490416469916270111604501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5987221959888360148806001 4490416469916270111604501)
                ·
                  refine ⟨210488272027325161481461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4490416469916270111604501 210488272027325161481461)
                  ·
                    rfl

theorem cell21_922330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_922330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_922330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_922330 prefixEnd_922330 := by exact prefixLift 922330
  have htrace : WordTrace (prefixWord ++ tailWord_922330) baseStart_922330 baseEnd_922330 := by
    simpa [prefixWord, tailWord_922330, baseEnd_922330] using wordTrace_append hprefix tailTrace_922330
  have hstable : (prefixWord ++ tailWord_922330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922330).length < 2 ^ (prefixWord ++ tailWord_922330).sum := by decide
  have hdescent : baseEnd_922330 < baseStart_922330 := by decide
  rcases family_descends (prefixWord ++ tailWord_922330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922364 : List Nat := [2, 2, 2, 1, 3, 3, 3, 1, 4]
def baseStart_922364 : Nat := 118140960795 + 922364 * 2 ^ 59
def prefixEnd_922364 : Nat := 4983230072969 + 3 ^ 40 * 922364 * 2
def baseEnd_922364 : Nat := 210496031290548657914725

theorem tailTrace_922364 : CollatzResearch.WordTrace tailWord_922364 prefixEnd_922364 210496031290548657914725 := by
  unfold tailWord_922364
  simp only [CollatzResearch.WordTrace]
  refine ⟨16820689415220115037463073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22427585886960153383284097 16820689415220115037463073)
  ·
    refine ⟨12615517061415086278097305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16820689415220115037463073 12615517061415086278097305)
    ·
      refine ⟨9461637796061314708572979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12615517061415086278097305 9461637796061314708572979)
      ·
        refine ⟨14192456694091972062859469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9461637796061314708572979 14192456694091972062859469)
        ·
          refine ⟨5322171260284489523572301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14192456694091972062859469 5322171260284489523572301)
          ·
            refine ⟨1995814222606683571339613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5322171260284489523572301 1995814222606683571339613)
            ·
              refine ⟨748430333477506339252355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1995814222606683571339613 748430333477506339252355)
              ·
                refine ⟨1122645500216259508878533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748430333477506339252355 1122645500216259508878533)
                ·
                  refine ⟨210496031290548657914725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1122645500216259508878533 210496031290548657914725)
                  ·
                    rfl

theorem cell21_922364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_922364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_922364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_922364 prefixEnd_922364 := by exact prefixLift 922364
  have htrace : WordTrace (prefixWord ++ tailWord_922364) baseStart_922364 baseEnd_922364 := by
    simpa [prefixWord, tailWord_922364, baseEnd_922364] using wordTrace_append hprefix tailTrace_922364
  have hstable : (prefixWord ++ tailWord_922364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922364).length < 2 ^ (prefixWord ++ tailWord_922364).sum := by decide
  have hdescent : baseEnd_922364 < baseStart_922364 := by decide
  rcases family_descends (prefixWord ++ tailWord_922364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922558 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_922558 : Nat := 118140960795 + 922558 * 2 ^ 59
def prefixEnd_922558 : Nat := 4983230072969 + 3 ^ 40 * 922558 * 2
def baseEnd_922558 : Nat := 210540304733647431680995

theorem tailTrace_922558 : CollatzResearch.WordTrace tailWord_922558 prefixEnd_922558 210540304733647431680995 := by
  unfold tailWord_922558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4206056823967175150936041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22432303061158267471658885 4206056823967175150936041)
  ·
    refine ⟨3154542617975381363202031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4206056823967175150936041 3154542617975381363202031)
    ·
      refine ⟨4731813926963072044803047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3154542617975381363202031 4731813926963072044803047)
      ·
        refine ⟨7097720890444608067204571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4731813926963072044803047 7097720890444608067204571)
        ·
          refine ⟨10646581335666912100806857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7097720890444608067204571 10646581335666912100806857)
          ·
            refine ⟨7984936001750184075605143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10646581335666912100806857 7984936001750184075605143)
            ·
              refine ⟨11977404002625276113407715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7984936001750184075605143 11977404002625276113407715)
              ·
                refine ⟨17966106003937914170111573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11977404002625276113407715 17966106003937914170111573)
                ·
                  refine ⟨210540304733647431680995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17966106003937914170111573 210540304733647431680995)
                  ·
                    rfl

theorem cell21_922558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_922558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_922558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_922558 prefixEnd_922558 := by exact prefixLift 922558
  have htrace : WordTrace (prefixWord ++ tailWord_922558) baseStart_922558 baseEnd_922558 := by
    simpa [prefixWord, tailWord_922558, baseEnd_922558] using wordTrace_append hprefix tailTrace_922558
  have hstable : (prefixWord ++ tailWord_922558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922558).length < 2 ^ (prefixWord ++ tailWord_922558).sum := by decide
  have hdescent : baseEnd_922558 < baseStart_922558 := by decide
  rcases family_descends (prefixWord ++ tailWord_922558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922589 : List Nat := [1, 4, 3, 1, 2, 1, 1, 8]
def baseStart_922589 : Nat := 118140960795 + 922589 * 2 ^ 59
def prefixEnd_922589 : Nat := 4983230072969 + 3 ^ 40 * 922589 * 2
def baseEnd_922589 : Nat := 70182459785332755554755

theorem tailTrace_922589 : CollatzResearch.WordTrace tailWord_922589 prefixEnd_922589 70182459785332755554755 := by
  unfold tailWord_922589
  simp only [CollatzResearch.WordTrace]
  refine ⟨33649585254625093501866821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22433056836416729001244547 33649585254625093501866821)
  ·
    refine ⟨6309297235242205031600029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33649585254625093501866821 6309297235242205031600029)
    ·
      refine ⟨2365986463215826886850011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6309297235242205031600029 2365986463215826886850011)
      ·
        refine ⟨3548979694823740330275017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2365986463215826886850011 3548979694823740330275017)
        ·
          refine ⟨2661734771117805247706263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3548979694823740330275017 2661734771117805247706263)
          ·
            refine ⟨3992602156676707871559395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2661734771117805247706263 3992602156676707871559395)
            ·
              refine ⟨5988903235015061807339093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3992602156676707871559395 5988903235015061807339093)
              ·
                refine ⟨70182459785332755554755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5988903235015061807339093 70182459785332755554755)
                ·
                  rfl

theorem cell21_922589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 8].length) (baseStart_922589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_922589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_922589 prefixEnd_922589 := by exact prefixLift 922589
  have htrace : WordTrace (prefixWord ++ tailWord_922589) baseStart_922589 baseEnd_922589 := by
    simpa [prefixWord, tailWord_922589, baseEnd_922589] using wordTrace_append hprefix tailTrace_922589
  have hstable : (prefixWord ++ tailWord_922589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922589).length < 2 ^ (prefixWord ++ tailWord_922589).sum := by decide
  have hdescent : baseEnd_922589 < baseStart_922589 := by decide
  rcases family_descends (prefixWord ++ tailWord_922589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922696 : List Nat := [2, 1, 3, 1, 1, 1, 3, 6, 3]
def baseStart_922696 : Nat := 118140960795 + 922696 * 2 ^ 59
def prefixEnd_922696 : Nat := 4983230072969 + 3 ^ 40 * 922696 * 2
def baseEnd_922696 : Nat := 210571798213789858380713

theorem tailTrace_922696 : CollatzResearch.WordTrace tailWord_922696 prefixEnd_922696 210571798213789858380713 := by
  unfold tailWord_922696
  simp only [CollatzResearch.WordTrace]
  refine ⟨16826743932618725388005971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22435658576824967184007961 16826743932618725388005971)
  ·
    refine ⟨25240115898928088082008957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16826743932618725388005971 25240115898928088082008957)
    ·
      refine ⟨9465043462098033030753359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25240115898928088082008957 9465043462098033030753359)
      ·
        refine ⟨14197565193147049546130039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9465043462098033030753359 14197565193147049546130039)
        ·
          refine ⟨21296347789720574319195059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14197565193147049546130039 21296347789720574319195059)
          ·
            refine ⟨31944521684580861478792589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21296347789720574319195059 31944521684580861478792589)
            ·
              refine ⟨11979195631717823054547221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31944521684580861478792589 11979195631717823054547221)
              ·
                refine ⟨561524795236772955681901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11979195631717823054547221 561524795236772955681901)
                ·
                  refine ⟨210571798213789858380713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561524795236772955681901 210571798213789858380713)
                  ·
                    rfl

theorem cell21_922696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 3].length) (baseStart_922696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_922696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_922696 prefixEnd_922696 := by exact prefixLift 922696
  have htrace : WordTrace (prefixWord ++ tailWord_922696) baseStart_922696 baseEnd_922696 := by
    simpa [prefixWord, tailWord_922696, baseEnd_922696] using wordTrace_append hprefix tailTrace_922696
  have hstable : (prefixWord ++ tailWord_922696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922696).length < 2 ^ (prefixWord ++ tailWord_922696).sum := by decide
  have hdescent : baseEnd_922696 < baseStart_922696 := by decide
  rcases family_descends (prefixWord ++ tailWord_922696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922730 : List Nat := [3, 1, 3, 2, 2, 3, 1, 3, 3]
def baseStart_922730 : Nat := 118140960795 + 922730 * 2 ^ 59
def prefixEnd_922730 : Nat := 4983230072969 + 3 ^ 40 * 922730 * 2
def baseEnd_922730 : Nat := 210579557477013354813977

theorem tailTrace_922730 : CollatzResearch.WordTrace tailWord_922730 prefixEnd_922730 210579557477013354813977 := by
  unfold tailWord_922730
  simp only [CollatzResearch.WordTrace]
  refine ⟨8413681986778568645687411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22436485298076183055166429 8413681986778568645687411)
  ·
    refine ⟨12620522980167852968531117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8413681986778568645687411 12620522980167852968531117)
    ·
      refine ⟨4732696117562944863199169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12620522980167852968531117 4732696117562944863199169)
      ·
        refine ⟨3549522088172208647399377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4732696117562944863199169 3549522088172208647399377)
        ·
          refine ⟨2662141566129156485549533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3549522088172208647399377 2662141566129156485549533)
          ·
            refine ⟨998303087298433682081075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2662141566129156485549533 998303087298433682081075)
            ·
              refine ⟨1497454630947650523121613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998303087298433682081075 1497454630947650523121613)
              ·
                refine ⟨561545486605368946170605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1497454630947650523121613 561545486605368946170605)
                ·
                  refine ⟨210579557477013354813977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561545486605368946170605 210579557477013354813977)
                  ·
                    rfl

theorem cell21_922730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_922730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_922730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_922730 prefixEnd_922730 := by exact prefixLift 922730
  have htrace : WordTrace (prefixWord ++ tailWord_922730) baseStart_922730 baseEnd_922730 := by
    simpa [prefixWord, tailWord_922730, baseEnd_922730] using wordTrace_append hprefix tailTrace_922730
  have hstable : (prefixWord ++ tailWord_922730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922730).length < 2 ^ (prefixWord ++ tailWord_922730).sum := by decide
  have hdescent : baseEnd_922730 < baseStart_922730 := by decide
  rcases family_descends (prefixWord ++ tailWord_922730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922848 : List Nat := [2, 1, 1, 3, 1, 4, 1, 5, 3]
def baseStart_922848 : Nat := 118140960795 + 922848 * 2 ^ 59
def prefixEnd_922848 : Nat := 4983230072969 + 3 ^ 40 * 922848 * 2
def baseEnd_922848 : Nat := 210606486684671371847069

theorem tailTrace_922848 : CollatzResearch.WordTrace tailWord_922848 prefixEnd_922848 210606486684671371847069 := by
  unfold tailWord_922848
  simp only [CollatzResearch.WordTrace]
  refine ⟨16829515880343390367772599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22439354507124520490363465 16829515880343390367772599)
  ·
    refine ⟨25244273820515085551658899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16829515880343390367772599 25244273820515085551658899)
    ·
      refine ⟨37866410730772628327488349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25244273820515085551658899 37866410730772628327488349)
      ·
        refine ⟨14199904024039735622808131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37866410730772628327488349 14199904024039735622808131)
        ·
          refine ⟨21299856036059603434212197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14199904024039735622808131 21299856036059603434212197)
          ·
            refine ⟨3993723006761175643914787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21299856036059603434212197 3993723006761175643914787)
            ·
              refine ⟨5990584510141763465872181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3993723006761175643914787 5990584510141763465872181)
              ·
                refine ⟨561617297825790324925517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5990584510141763465872181 561617297825790324925517)
                ·
                  refine ⟨210606486684671371847069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561617297825790324925517 210606486684671371847069)
                  ·
                    rfl

theorem cell21_922848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 3].length) (baseStart_922848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_922848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_922848 prefixEnd_922848 := by exact prefixLift 922848
  have htrace : WordTrace (prefixWord ++ tailWord_922848) baseStart_922848 baseEnd_922848 := by
    simpa [prefixWord, tailWord_922848, baseEnd_922848] using wordTrace_append hprefix tailTrace_922848
  have hstable : (prefixWord ++ tailWord_922848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922848).length < 2 ^ (prefixWord ++ tailWord_922848).sum := by decide
  have hdescent : baseEnd_922848 < baseStart_922848 := by decide
  rcases family_descends (prefixWord ++ tailWord_922848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922879 : List Nat := [1, 1, 2, 2, 1, 6, 3, 1, 4]
def baseStart_922879 : Nat := 118140960795 + 922879 * 2 ^ 59
def prefixEnd_922879 : Nat := 4983230072969 + 3 ^ 40 * 922879 * 2
def baseEnd_922879 : Nat := 210613561307022206830339

theorem tailTrace_922879 : CollatzResearch.WordTrace tailWord_922879 prefixEnd_922879 210613561307022206830339 := by
  unfold tailWord_922879
  simp only [CollatzResearch.WordTrace]
  refine ⟨33660162423574473029923691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22440108282382982019949127 33660162423574473029923691)
  ·
    refine ⟨50490243635361709544885537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33660162423574473029923691 50490243635361709544885537)
    ·
      refine ⟨37867682726521282158664153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50490243635361709544885537 37867682726521282158664153)
      ·
        refine ⟨28400762044890961618998115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37867682726521282158664153 28400762044890961618998115)
        ·
          refine ⟨42601143067336442428497173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28400762044890961618998115 42601143067336442428497173)
          ·
            refine ⟨1996928581281395738835805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42601143067336442428497173 1996928581281395738835805)
            ·
              refine ⟨748848217980523402063427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1996928581281395738835805 748848217980523402063427)
              ·
                refine ⟨1123272326970785103095141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748848217980523402063427 1123272326970785103095141)
                ·
                  refine ⟨210613561307022206830339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1123272326970785103095141 210613561307022206830339)
                  ·
                    rfl

theorem cell21_922879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 4].length) (baseStart_922879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_922879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_922879 prefixEnd_922879 := by exact prefixLift 922879
  have htrace : WordTrace (prefixWord ++ tailWord_922879) baseStart_922879 baseEnd_922879 := by
    simpa [prefixWord, tailWord_922879, baseEnd_922879] using wordTrace_append hprefix tailTrace_922879
  have hstable : (prefixWord ++ tailWord_922879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922879).length < 2 ^ (prefixWord ++ tailWord_922879).sum := by decide
  have hdescent : baseEnd_922879 < baseStart_922879 := by decide
  rcases family_descends (prefixWord ++ tailWord_922879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922938 : List Nat := [3, 1, 1, 1, 4, 1, 3, 3, 4]
def baseStart_922938 : Nat := 118140960795 + 922938 * 2 ^ 59
def prefixEnd_922938 : Nat := 4983230072969 + 3 ^ 40 * 922938 * 2
def baseEnd_922938 : Nat := 210627025910851215346885

theorem tailTrace_922938 : CollatzResearch.WordTrace tailWord_922938 prefixEnd_922938 210627025910851215346885 := by
  unfold tailWord_922938
  simp only [CollatzResearch.WordTrace]
  refine ⟨8415578582590181526580367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22441542886907150737547645 8415578582590181526580367)
  ·
    refine ⟨12623367873885272289870551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8415578582590181526580367 12623367873885272289870551)
    ·
      refine ⟨18935051810827908434805827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12623367873885272289870551 18935051810827908434805827)
      ·
        refine ⟨28402577716241862652208741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18935051810827908434805827 28402577716241862652208741)
        ·
          refine ⟨5325483321795349247289139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28402577716241862652208741 5325483321795349247289139)
          ·
            refine ⟨7988224982693023870933709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5325483321795349247289139 7988224982693023870933709)
            ·
              refine ⟨2995584368509883951600141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7988224982693023870933709 2995584368509883951600141)
              ·
                refine ⟨1123344138191206481850053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2995584368509883951600141 1123344138191206481850053)
                ·
                  refine ⟨210627025910851215346885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1123344138191206481850053 210627025910851215346885)
                  ·
                    rfl

theorem cell21_922938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_922938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_922938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_922938 prefixEnd_922938 := by exact prefixLift 922938
  have htrace : WordTrace (prefixWord ++ tailWord_922938) baseStart_922938 baseEnd_922938 := by
    simpa [prefixWord, tailWord_922938, baseEnd_922938] using wordTrace_append hprefix tailTrace_922938
  have hstable : (prefixWord ++ tailWord_922938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922938).length < 2 ^ (prefixWord ++ tailWord_922938).sum := by decide
  have hdescent : baseEnd_922938 < baseStart_922938 := by decide
  rcases family_descends (prefixWord ++ tailWord_922938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922986 : List Nat := [3, 1, 3, 3, 2, 2, 1, 6]
def baseStart_922986 : Nat := 118140960795 + 922986 * 2 ^ 59
def prefixEnd_922986 : Nat := 4983230072969 + 3 ^ 40 * 922986 * 2
def baseEnd_922986 : Nat := 70212660054937932848929

theorem tailTrace_922986 : CollatzResearch.WordTrace tailWord_922986 prefixEnd_922986 70212660054937932848929 := by
  unfold tailWord_922986
  simp only [CollatzResearch.WordTrace]
  refine ⟨8416016258546707576017203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22442710022791220202712541 8416016258546707576017203)
  ·
    refine ⟨12624024387820061364025805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8416016258546707576017203 12624024387820061364025805)
    ·
      refine ⟨4734009145432523011509677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12624024387820061364025805 4734009145432523011509677)
      ·
        refine ⟨1775253429537196129316129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4734009145432523011509677 1775253429537196129316129)
        ·
          refine ⟨1331440072152897096987097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1775253429537196129316129 1331440072152897096987097)
          ·
            refine ⟨998580054114672822740323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1331440072152897096987097 998580054114672822740323)
            ·
              refine ⟨1497870081172009234110485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998580054114672822740323 1497870081172009234110485)
              ·
                refine ⟨70212660054937932848929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1497870081172009234110485 70212660054937932848929)
                ·
                  rfl

theorem cell21_922986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_922986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_922986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_922986 prefixEnd_922986 := by exact prefixLift 922986
  have htrace : WordTrace (prefixWord ++ tailWord_922986) baseStart_922986 baseEnd_922986 := by
    simpa [prefixWord, tailWord_922986, baseEnd_922986] using wordTrace_append hprefix tailTrace_922986
  have hstable : (prefixWord ++ tailWord_922986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922986).length < 2 ^ (prefixWord ++ tailWord_922986).sum := by decide
  have hdescent : baseEnd_922986 < baseStart_922986 := by decide
  rcases family_descends (prefixWord ++ tailWord_922986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923017 : List Nat := [1, 2, 1, 1, 7, 1, 2, 3, 3]
def baseStart_923017 : Nat := 118140960795 + 923017 * 2 ^ 59
def prefixEnd_923017 : Nat := 4983230072969 + 3 ^ 40 * 923017 * 2
def baseEnd_923017 : Nat := 210645054787164633530057

theorem tailTrace_923017 : CollatzResearch.WordTrace tailWord_923017 prefixEnd_923017 210645054787164633530057 := by
  unfold tailWord_923017
  simp only [CollatzResearch.WordTrace]
  refine ⟨33665195697074522598447305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22443463798049681732298203 33665195697074522598447305)
  ·
    refine ⟨25248896772805891948835479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33665195697074522598447305 25248896772805891948835479)
    ·
      refine ⟨37873345159208837923253219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25248896772805891948835479 37873345159208837923253219)
      ·
        refine ⟨56810017738813256884879829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37873345159208837923253219 56810017738813256884879829)
        ·
          refine ⟨1331484790753435708239371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 56810017738813256884879829 1331484790753435708239371)
          ·
            refine ⟨1997227186130153562359057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331484790753435708239371 1997227186130153562359057)
            ·
              refine ⟨1497920389597615171769293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1997227186130153562359057 1497920389597615171769293)
              ·
                refine ⟨561720146099105689413485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1497920389597615171769293 561720146099105689413485)
                ·
                  refine ⟨210645054787164633530057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561720146099105689413485 210645054787164633530057)
                  ·
                    rfl

theorem cell21_923017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 3].length) (baseStart_923017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923017 prefixEnd_923017 := by exact prefixLift 923017
  have htrace : WordTrace (prefixWord ++ tailWord_923017) baseStart_923017 baseEnd_923017 := by
    simpa [prefixWord, tailWord_923017, baseEnd_923017] using wordTrace_append hprefix tailTrace_923017
  have hstable : (prefixWord ++ tailWord_923017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923017).length < 2 ^ (prefixWord ++ tailWord_923017).sum := by decide
  have hdescent : baseEnd_923017 < baseStart_923017 := by decide
  rcases family_descends (prefixWord ++ tailWord_923017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923087 : List Nat := [1, 1, 2, 1, 1, 4, 11]
def baseStart_923087 : Nat := 118140960795 + 923087 * 2 ^ 59
def prefixEnd_923087 : Nat := 4983230072969 + 3 ^ 40 * 923087 * 2
def baseEnd_923087 : Nat := 23406781082317785262583

theorem tailTrace_923087 : CollatzResearch.WordTrace tailWord_923087 prefixEnd_923087 23406781082317785262583 := by
  unfold tailWord_923087
  simp only [CollatzResearch.WordTrace]
  refine ⟨33667748806820924553495515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22445165871213949702330343 33667748806820924553495515)
  ·
    refine ⟨50501623210231386830243273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33667748806820924553495515 50501623210231386830243273)
    ·
      refine ⟨37876217407673540122682455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50501623210231386830243273 37876217407673540122682455)
      ·
        refine ⟨56814326111510310184023683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37876217407673540122682455 56814326111510310184023683)
        ·
          refine ⟨85221489167265465276035525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56814326111510310184023683 85221489167265465276035525)
          ·
            refine ⟨15979029218862274739256661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85221489167265465276035525 15979029218862274739256661)
            ·
              refine ⟨23406781082317785262583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15979029218862274739256661 23406781082317785262583)
              ·
                rfl

theorem cell21_923087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 11].length) (baseStart_923087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923087 prefixEnd_923087 := by exact prefixLift 923087
  have htrace : WordTrace (prefixWord ++ tailWord_923087) baseStart_923087 baseEnd_923087 := by
    simpa [prefixWord, tailWord_923087, baseEnd_923087] using wordTrace_append hprefix tailTrace_923087
  have hstable : (prefixWord ++ tailWord_923087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923087).length < 2 ^ (prefixWord ++ tailWord_923087).sum := by decide
  have hdescent : baseEnd_923087 < baseStart_923087 := by decide
  rcases family_descends (prefixWord ++ tailWord_923087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923093 : List Nat := [1, 3, 2, 3, 1, 1, 5, 2, 3]
def baseStart_923093 : Nat := 118140960795 + 923093 * 2 ^ 59
def prefixEnd_923093 : Nat := 4983230072969 + 3 ^ 40 * 923093 * 2
def baseEnd_923093 : Nat := 210662399022605390263235

theorem tailTrace_923093 : CollatzResearch.WordTrace tailWord_923093 prefixEnd_923093 210662399022605390263235 := by
  unfold tailWord_923093
  simp only [CollatzResearch.WordTrace]
  refine ⟨33667967644799187578213933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22445311763199458385475955 33667967644799187578213933)
  ·
    refine ⟨12625487866799695341830225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33667967644799187578213933 12625487866799695341830225)
    ·
      refine ⟨9469115900099771506372669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12625487866799695341830225 9469115900099771506372669)
      ·
        refine ⟨3550918462537414314889751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9469115900099771506372669 3550918462537414314889751)
        ·
          refine ⟨5326377693806121472334627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3550918462537414314889751 5326377693806121472334627)
          ·
            refine ⟨7989566540709182208501941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5326377693806121472334627 7989566540709182208501941)
            ·
              refine ⟨749021863191485832047057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7989566540709182208501941 749021863191485832047057)
              ·
                refine ⟨561766397393614374035293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749021863191485832047057 561766397393614374035293)
                ·
                  refine ⟨210662399022605390263235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 561766397393614374035293 210662399022605390263235)
                  ·
                    rfl

theorem cell21_923093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_923093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923093 prefixEnd_923093 := by exact prefixLift 923093
  have htrace : WordTrace (prefixWord ++ tailWord_923093) baseStart_923093 baseEnd_923093 := by
    simpa [prefixWord, tailWord_923093, baseEnd_923093] using wordTrace_append hprefix tailTrace_923093
  have hstable : (prefixWord ++ tailWord_923093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923093).length < 2 ^ (prefixWord ++ tailWord_923093).sum := by decide
  have hdescent : baseEnd_923093 < baseStart_923093 := by decide
  rcases family_descends (prefixWord ++ tailWord_923093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923107 : List Nat := [1, 1, 1, 6, 2, 1, 4, 1, 4]
def baseStart_923107 : Nat := 118140960795 + 923107 * 2 ^ 59
def prefixEnd_923107 : Nat := 4983230072969 + 3 ^ 40 * 923107 * 2
def baseEnd_923107 : Nat := 210665594013344477029873

theorem tailTrace_923107 : CollatzResearch.WordTrace tailWord_923107 prefixEnd_923107 210665594013344477029873 := by
  unfold tailWord_923107
  simp only [CollatzResearch.WordTrace]
  refine ⟨33668478266748467969223575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22445652177832311979482383 33668478266748467969223575)
  ·
    refine ⟨50502717400122701953835363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33668478266748467969223575 50502717400122701953835363)
    ·
      refine ⟨75754076100184052930753045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50502717400122701953835363 75754076100184052930753045)
      ·
        refine ⟨3550972317196127481129049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75754076100184052930753045 3550972317196127481129049)
        ·
          refine ⟨2663229237897095610846787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3550972317196127481129049 2663229237897095610846787)
          ·
            refine ⟨3994843856845643416270181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2663229237897095610846787 3994843856845643416270181)
            ·
              refine ⟨749033223158558140550659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3994843856845643416270181 749033223158558140550659)
              ·
                refine ⟨1123549834737837210825989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 749033223158558140550659 1123549834737837210825989)
                ·
                  refine ⟨210665594013344477029873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1123549834737837210825989 210665594013344477029873)
                  ·
                    rfl

theorem cell21_923107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 4].length) (baseStart_923107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923107 prefixEnd_923107 := by exact prefixLift 923107
  have htrace : WordTrace (prefixWord ++ tailWord_923107) baseStart_923107 baseEnd_923107 := by
    simpa [prefixWord, tailWord_923107, baseEnd_923107] using wordTrace_append hprefix tailTrace_923107
  have hstable : (prefixWord ++ tailWord_923107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923107).length < 2 ^ (prefixWord ++ tailWord_923107).sum := by decide
  have hdescent : baseEnd_923107 < baseStart_923107 := by decide
  rcases family_descends (prefixWord ++ tailWord_923107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923194 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 7]
def baseStart_923194 : Nat := 118140960795 + 923194 * 2 ^ 59
def prefixEnd_923194 : Nat := 4983230072969 + 3 ^ 40 * 923194 * 2
def baseEnd_923194 : Nat := 210685448598651659079695

theorem tailTrace_923194 : CollatzResearch.WordTrace tailWord_923194 prefixEnd_923194 210685448598651659079695 := by
  unfold tailWord_923194
  simp only [CollatzResearch.WordTrace]
  refine ⟨8417912854358320456910159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22447767611622187885093757 8417912854358320456910159)
  ·
    refine ⟨12626869281537480685365239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8417912854358320456910159 12626869281537480685365239)
    ·
      refine ⟨18940303922306221028047859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12626869281537480685365239 18940303922306221028047859)
      ·
        refine ⟨28410455883459331542071789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18940303922306221028047859 28410455883459331542071789)
        ·
          refine ⟨10653920956297249328276921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28410455883459331542071789 10653920956297249328276921)
          ·
            refine ⟨7990440717222936996207691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10653920956297249328276921 7990440717222936996207691)
            ·
              refine ⟨11985661075834405494311537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7990440717222936996207691 11985661075834405494311537)
              ·
                refine ⟨8989245806875804120733653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11985661075834405494311537 8989245806875804120733653)
                ·
                  refine ⟨210685448598651659079695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8989245806875804120733653 210685448598651659079695)
                  ·
                    rfl

theorem cell21_923194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_923194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923194 prefixEnd_923194 := by exact prefixLift 923194
  have htrace : WordTrace (prefixWord ++ tailWord_923194) baseStart_923194 baseEnd_923194 := by
    simpa [prefixWord, tailWord_923194, baseEnd_923194] using wordTrace_append hprefix tailTrace_923194
  have hstable : (prefixWord ++ tailWord_923194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923194).length < 2 ^ (prefixWord ++ tailWord_923194).sum := by decide
  have hdescent : baseEnd_923194 < baseStart_923194 := by decide
  rcases family_descends (prefixWord ++ tailWord_923194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923225 : List Nat := [1, 2, 1, 2, 2, 1, 1, 7, 4]
def baseStart_923225 : Nat := 118140960795 + 923225 * 2 ^ 59
def prefixEnd_923225 : Nat := 4983230072969 + 3 ^ 40 * 923225 * 2
def baseEnd_923225 : Nat := 210692523221002494062965

theorem tailTrace_923225 : CollatzResearch.WordTrace tailWord_923225 prefixEnd_923225 210692523221002494062965 := by
  unfold tailWord_923225
  simp only [CollatzResearch.WordTrace]
  refine ⟨33672782080320974122019129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22448521386880649414679419 33672782080320974122019129)
  ·
    refine ⟨25254586560240730591514347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33672782080320974122019129 25254586560240730591514347)
    ·
      refine ⟨37881879840361095887271521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25254586560240730591514347 37881879840361095887271521)
      ·
        refine ⟨28411409880270821915453641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37881879840361095887271521 28411409880270821915453641)
        ·
          refine ⟨21308557410203116436590231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28411409880270821915453641 21308557410203116436590231)
          ·
            refine ⟨31962836115304674654885347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21308557410203116436590231 31962836115304674654885347)
            ·
              refine ⟨47944254172957011982328021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31962836115304674654885347 47944254172957011982328021)
              ·
                refine ⟨1123693457178679968335813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47944254172957011982328021 1123693457178679968335813)
                ·
                  refine ⟨210692523221002494062965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1123693457178679968335813 210692523221002494062965)
                  ·
                    rfl

theorem cell21_923225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 4].length) (baseStart_923225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923225 prefixEnd_923225 := by exact prefixLift 923225
  have htrace : WordTrace (prefixWord ++ tailWord_923225) baseStart_923225 baseEnd_923225 := by
    simpa [prefixWord, tailWord_923225, baseEnd_923225] using wordTrace_append hprefix tailTrace_923225
  have hstable : (prefixWord ++ tailWord_923225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923225).length < 2 ^ (prefixWord ++ tailWord_923225).sum := by decide
  have hdescent : baseEnd_923225 < baseStart_923225 := by decide
  rcases family_descends (prefixWord ++ tailWord_923225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923377 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 6]
def baseStart_923377 : Nat := 118140960795 + 923377 * 2 ^ 59
def prefixEnd_923377 : Nat := 4983230072969 + 3 ^ 40 * 923377 * 2
def baseEnd_923377 : Nat := 210727211691884007529321

theorem tailTrace_923377 : CollatzResearch.WordTrace tailWord_923377 prefixEnd_923377 210727211691884007529321 := by
  unfold tailWord_923377
  simp only [CollatzResearch.WordTrace]
  refine ⟨33678325975770304081552385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22452217317180202721034923 33678325975770304081552385)
  ·
    refine ⟨25258744481827728061164289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33678325975770304081552385 25258744481827728061164289)
    ·
      refine ⟨18944058361370796045873217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25258744481827728061164289 18944058361370796045873217)
      ·
        refine ⟨14208043771028097034404913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18944058361370796045873217 14208043771028097034404913)
        ·
          refine ⟨10656032828271072775803685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14208043771028097034404913 10656032828271072775803685)
          ·
            refine ⟨1998006155300826145463191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10656032828271072775803685 1998006155300826145463191)
            ·
              refine ⟨2997009232951239218194787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1998006155300826145463191 2997009232951239218194787)
              ·
                refine ⟨4495513849426858827292181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2997009232951239218194787 4495513849426858827292181)
                ·
                  refine ⟨210727211691884007529321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4495513849426858827292181 210727211691884007529321)
                  ·
                    rfl

theorem cell21_923377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_923377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923377 prefixEnd_923377 := by exact prefixLift 923377
  have htrace : WordTrace (prefixWord ++ tailWord_923377) baseStart_923377 baseEnd_923377 := by
    simpa [prefixWord, tailWord_923377, baseEnd_923377] using wordTrace_append hprefix tailTrace_923377
  have hstable : (prefixWord ++ tailWord_923377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923377).length < 2 ^ (prefixWord ++ tailWord_923377).sum := by decide
  have hdescent : baseEnd_923377 < baseStart_923377 := by decide
  rcases family_descends (prefixWord ++ tailWord_923377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923484 : List Nat := [2, 2, 4, 2, 2, 9]
def baseStart_923484 : Nat := 118140960795 + 923484 * 2 ^ 59
def prefixEnd_923484 : Nat := 4983230072969 + 3 ^ 40 * 923484 * 2
def baseEnd_923484 : Nat := 7805615946284281453547

theorem tailTrace_923484 : CollatzResearch.WordTrace tailWord_923484 prefixEnd_923484 7805615946284281453547 := by
  unfold tailWord_923484
  simp only [CollatzResearch.WordTrace]
  refine ⟨16841114293191330677848753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22454819057588440903798337 16841114293191330677848753)
  ·
    refine ⟨12630835719893498008386565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16841114293191330677848753 12630835719893498008386565)
    ·
      refine ⟨2368281697480030876572481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12630835719893498008386565 2368281697480030876572481)
      ·
        refine ⟨1776211273110023157429361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2368281697480030876572481 1776211273110023157429361)
        ·
          refine ⟨1332158454832517368072021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1776211273110023157429361 1332158454832517368072021)
          ·
            refine ⟨7805615946284281453547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1332158454832517368072021 7805615946284281453547)
            ·
              rfl

theorem cell21_923484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 9].length) (baseStart_923484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923484 prefixEnd_923484 := by exact prefixLift 923484
  have htrace : WordTrace (prefixWord ++ tailWord_923484) baseStart_923484 baseEnd_923484 := by
    simpa [prefixWord, tailWord_923484, baseEnd_923484] using wordTrace_append hprefix tailTrace_923484
  have hstable : (prefixWord ++ tailWord_923484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923484).length < 2 ^ (prefixWord ++ tailWord_923484).sum := by decide
  have hdescent : baseEnd_923484 < baseStart_923484 := by decide
  rcases family_descends (prefixWord ++ tailWord_923484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923490 : List Nat := [3, 3, 2, 1, 2, 3, 2, 2, 3]
def baseStart_923490 : Nat := 118140960795 + 923490 * 2 ^ 59
def prefixEnd_923490 : Nat := 4983230072969 + 3 ^ 40 * 923490 * 2
def baseEnd_923490 : Nat := 210752999831420922145757

theorem tailTrace_923490 : CollatzResearch.WordTrace tailWord_923490 prefixEnd_923490 210752999831420922145757 := by
  unfold tailWord_923490
  simp only [CollatzResearch.WordTrace]
  refine ⟨8420611856090231095103981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22454964949573949586943949 8420611856090231095103981)
  ·
    refine ⟨3157729446033836660663993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8420611856090231095103981 3157729446033836660663993)
    ·
      refine ⟨2368297084525377495497995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3157729446033836660663993 2368297084525377495497995)
      ·
        refine ⟨3552445626788066243246993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2368297084525377495497995 3552445626788066243246993)
        ·
          refine ⟨2664334220091049682435245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3552445626788066243246993 2664334220091049682435245)
          ·
            refine ⟨999125332534143630913217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2664334220091049682435245 999125332534143630913217)
            ·
              refine ⟨749343999400607723184913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 999125332534143630913217 749343999400607723184913)
              ·
                refine ⟨562007999550455792388685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749343999400607723184913 562007999550455792388685)
                ·
                  refine ⟨210752999831420922145757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562007999550455792388685 210752999831420922145757)
                  ·
                    rfl

theorem cell21_923490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_923490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923490 prefixEnd_923490 := by exact prefixLift 923490
  have htrace : WordTrace (prefixWord ++ tailWord_923490) baseStart_923490 baseEnd_923490 := by
    simpa [prefixWord, tailWord_923490, baseEnd_923490] using wordTrace_append hprefix tailTrace_923490
  have hstable : (prefixWord ++ tailWord_923490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923490).length < 2 ^ (prefixWord ++ tailWord_923490).sum := by decide
  have hdescent : baseEnd_923490 < baseStart_923490 := by decide
  rcases family_descends (prefixWord ++ tailWord_923490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923518 : List Nat := [4, 2, 3, 1, 1, 2, 3, 5]
def baseStart_923518 : Nat := 118140960795 + 923518 * 2 ^ 59
def prefixEnd_923518 : Nat := 4983230072969 + 3 ^ 40 * 923518 * 2
def baseEnd_923518 : Nat := 70253129937633031893011

theorem tailTrace_923518 : CollatzResearch.WordTrace tailWord_923518 prefixEnd_923518 70253129937633031893011 := by
  unfold tailWord_923518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4210433583532435645304401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22455645778839656774956805 4210433583532435645304401)
  ·
    refine ⟨3157825187649326733978301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4210433583532435645304401 3157825187649326733978301)
    ·
      refine ⟨1184184445368497525241863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3157825187649326733978301 1184184445368497525241863)
      ·
        refine ⟨1776276668052746287862795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1184184445368497525241863 1776276668052746287862795)
        ·
          refine ⟨2664415002079119431794193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1776276668052746287862795 2664415002079119431794193)
          ·
            refine ⟨1998311251559339573845645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2664415002079119431794193 1998311251559339573845645)
            ·
              refine ⟨749366719334752340192117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1998311251559339573845645 749366719334752340192117)
              ·
                refine ⟨70253129937633031893011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 749366719334752340192117 70253129937633031893011)
                ·
                  rfl

theorem cell21_923518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_923518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923518 prefixEnd_923518 := by exact prefixLift 923518
  have htrace : WordTrace (prefixWord ++ tailWord_923518) baseStart_923518 baseEnd_923518 := by
    simpa [prefixWord, tailWord_923518, baseEnd_923518] using wordTrace_append hprefix tailTrace_923518
  have hstable : (prefixWord ++ tailWord_923518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923518).length < 2 ^ (prefixWord ++ tailWord_923518).sum := by decide
  have hdescent : baseEnd_923518 < baseStart_923518 := by decide
  rcases family_descends (prefixWord ++ tailWord_923518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923543 : List Nat := [1, 1, 3, 3, 1, 4, 8]
def baseStart_923543 : Nat := 118140960795 + 923543 * 2 ^ 59
def prefixEnd_923543 : Nat := 4983230072969 + 3 ^ 40 * 923543 * 2
def baseEnd_923543 : Nat := 23418343905944956418035

theorem tailTrace_923543 : CollatzResearch.WordTrace tailWord_923543 prefixEnd_923543 23418343905944956418035 := by
  unfold tailWord_923543
  simp only [CollatzResearch.WordTrace]
  refine ⟨33684380493168914432095283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22456253662112609621396855 33684380493168914432095283)
  ·
    refine ⟨50526570739753371648142925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33684380493168914432095283 50526570739753371648142925)
    ·
      refine ⟨18947464027407514368053597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50526570739753371648142925 18947464027407514368053597)
      ·
        refine ⟨7105299010277817888020099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18947464027407514368053597 7105299010277817888020099)
        ·
          refine ⟨10657948515416726832030149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7105299010277817888020099 10657948515416726832030149)
          ·
            refine ⟨1998365346640636281005653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10657948515416726832030149 1998365346640636281005653)
            ·
              refine ⟨23418343905944956418035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1998365346640636281005653 23418343905944956418035)
              ·
                rfl

theorem cell21_923543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 8].length) (baseStart_923543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923543 prefixEnd_923543 := by exact prefixLift 923543
  have htrace : WordTrace (prefixWord ++ tailWord_923543) baseStart_923543 baseEnd_923543 := by
    simpa [prefixWord, tailWord_923543, baseEnd_923543] using wordTrace_append hprefix tailTrace_923543
  have hstable : (prefixWord ++ tailWord_923543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923543).length < 2 ^ (prefixWord ++ tailWord_923543).sum := by decide
  have hdescent : baseEnd_923543 < baseStart_923543 := by decide
  rcases family_descends (prefixWord ++ tailWord_923543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923546 : List Nat := [3, 1, 1, 4, 2, 1, 3, 2, 4]
def baseStart_923546 : Nat := 118140960795 + 923546 * 2 ^ 59
def prefixEnd_923546 : Nat := 4983230072969 + 3 ^ 40 * 923546 * 2
def baseEnd_923546 : Nat := 210765779794377269212309

theorem tailTrace_923546 : CollatzResearch.WordTrace tailWord_923546 prefixEnd_923546 210765779794377269212309 := by
  unfold tailWord_923546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8421122478039511486113623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22456326608105363962969661 8421122478039511486113623)
  ·
    refine ⟨12631683717059267229170435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8421122478039511486113623 12631683717059267229170435)
    ·
      refine ⟨18947525575588900843755653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12631683717059267229170435 18947525575588900843755653)
      ·
        refine ⟨3552661045422918908204185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18947525575588900843755653 3552661045422918908204185)
        ·
          refine ⟨2664495784067189181153139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3552661045422918908204185 2664495784067189181153139)
          ·
            refine ⟨3996743676100783771729709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2664495784067189181153139 3996743676100783771729709)
            ·
              refine ⟨1498778878537793914398641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3996743676100783771729709 1498778878537793914398641)
              ·
                refine ⟨1124084158903345435798981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1498778878537793914398641 1124084158903345435798981)
                ·
                  refine ⟨210765779794377269212309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1124084158903345435798981 210765779794377269212309)
                  ·
                    rfl

theorem cell21_923546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_923546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923546 prefixEnd_923546 := by exact prefixLift 923546
  have htrace : WordTrace (prefixWord ++ tailWord_923546) baseStart_923546 baseEnd_923546 := by
    simpa [prefixWord, tailWord_923546, baseEnd_923546] using wordTrace_append hprefix tailTrace_923546
  have hstable : (prefixWord ++ tailWord_923546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923546).length < 2 ^ (prefixWord ++ tailWord_923546).sum := by decide
  have hdescent : baseEnd_923546 < baseStart_923546 := by decide
  rcases family_descends (prefixWord ++ tailWord_923546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923605 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 6]
def baseStart_923605 : Nat := 118140960795 + 923605 * 2 ^ 59
def prefixEnd_923605 : Nat := 4983230072969 + 3 ^ 40 * 923605 * 2
def baseEnd_923605 : Nat := 210779244398206277728855

theorem tailTrace_923605 : CollatzResearch.WordTrace tailWord_923605 prefixEnd_923605 210779244398206277728855 := by
  unfold tailWord_923605
  simp only [CollatzResearch.WordTrace]
  refine ⟨33686641818944299020852269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22457761212629532680568179 33686641818944299020852269)
  ·
    refine ⟨12632490682104112132819601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33686641818944299020852269 12632490682104112132819601)
    ·
      refine ⟨9474368011578084099614701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12632490682104112132819601 9474368011578084099614701)
      ·
        refine ⟨3552888004341781537355513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9474368011578084099614701 3552888004341781537355513)
        ·
          refine ⟨2664666003256336153016635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3552888004341781537355513 2664666003256336153016635)
          ·
            refine ⟨3996999004884504229524953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2664666003256336153016635 3996999004884504229524953)
            ·
              refine ⟨2997749253663378172143715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3996999004884504229524953 2997749253663378172143715)
              ·
                refine ⟨4496623880495067258215573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2997749253663378172143715 4496623880495067258215573)
                ·
                  refine ⟨210779244398206277728855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4496623880495067258215573 210779244398206277728855)
                  ·
                    rfl

theorem cell21_923605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_923605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923605 prefixEnd_923605 := by exact prefixLift 923605
  have htrace : WordTrace (prefixWord ++ tailWord_923605) baseStart_923605 baseEnd_923605 := by
    simpa [prefixWord, tailWord_923605, baseEnd_923605] using wordTrace_append hprefix tailTrace_923605
  have hstable : (prefixWord ++ tailWord_923605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923605).length < 2 ^ (prefixWord ++ tailWord_923605).sum := by decide
  have hdescent : baseEnd_923605 < baseStart_923605 := by decide
  rcases family_descends (prefixWord ++ tailWord_923605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923608 : List Nat := [2, 1, 2, 2, 2, 2, 5, 2, 3]
def baseStart_923608 : Nat := 118140960795 + 923608 * 2 ^ 59
def prefixEnd_923608 : Nat := 4983230072969 + 3 ^ 40 * 923608 * 2
def baseEnd_923608 : Nat := 210779929039078939178849

theorem tailTrace_923608 : CollatzResearch.WordTrace tailWord_923608 prefixEnd_923608 210779929039078939178849 := by
  unfold tailWord_923608
  simp only [CollatzResearch.WordTrace]
  refine ⟨16843375618966715266605739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22457834158622287022140985 16843375618966715266605739)
  ·
    refine ⟨25265063428450072899908609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16843375618966715266605739 25265063428450072899908609)
    ·
      refine ⟨18948797571337554674931457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25265063428450072899908609 18948797571337554674931457)
      ·
        refine ⟨14211598178503166006198593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18948797571337554674931457 14211598178503166006198593)
        ·
          refine ⟨10658698633877374504648945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14211598178503166006198593 10658698633877374504648945)
          ·
            refine ⟨7994023975408030878486709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10658698633877374504648945 7994023975408030878486709)
            ·
              refine ⟨749439747694502894858129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7994023975408030878486709 749439747694502894858129)
              ·
                refine ⟨562079810770877171143597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749439747694502894858129 562079810770877171143597)
                ·
                  refine ⟨210779929039078939178849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562079810770877171143597 210779929039078939178849)
                  ·
                    rfl

theorem cell21_923608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 3].length) (baseStart_923608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923608 prefixEnd_923608 := by exact prefixLift 923608
  have htrace : WordTrace (prefixWord ++ tailWord_923608) baseStart_923608 baseEnd_923608 := by
    simpa [prefixWord, tailWord_923608, baseEnd_923608] using wordTrace_append hprefix tailTrace_923608
  have hstable : (prefixWord ++ tailWord_923608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923608).length < 2 ^ (prefixWord ++ tailWord_923608).sum := by decide
  have hdescent : baseEnd_923608 < baseStart_923608 := by decide
  rcases family_descends (prefixWord ++ tailWord_923608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923619 : List Nat := [1, 1, 1, 6, 1, 2, 1, 8]
def baseStart_923619 : Nat := 118140960795 + 923619 * 2 ^ 59
def prefixEnd_923619 : Nat := 4983230072969 + 3 ^ 40 * 923619 * 2
def baseEnd_923619 : Nat := 70260813129648454831831

theorem tailTrace_923619 : CollatzResearch.WordTrace tailWord_923619 prefixEnd_923619 70260813129648454831831 := by
  unfold tailWord_923619
  simp only [CollatzResearch.WordTrace]
  refine ⟨33687152440893579411861911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22458101627262386274574607 33687152440893579411861911)
  ·
    refine ⟨50530728661340369117792867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33687152440893579411861911 50530728661340369117792867)
    ·
      refine ⟨75796092992010553676689301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50530728661340369117792867 75796092992010553676689301)
      ·
        refine ⟨3552941859000494703594811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75796092992010553676689301 3552941859000494703594811)
        ·
          refine ⟨5329412788500742055392217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3552941859000494703594811 5329412788500742055392217)
          ·
            refine ⟨3997059591375556541544163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5329412788500742055392217 3997059591375556541544163)
            ·
              refine ⟨5995589387063334812316245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3997059591375556541544163 5995589387063334812316245)
              ·
                refine ⟨70260813129648454831831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5995589387063334812316245 70260813129648454831831)
                ·
                  rfl

theorem cell21_923619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 8].length) (baseStart_923619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923619 prefixEnd_923619 := by exact prefixLift 923619
  have htrace : WordTrace (prefixWord ++ tailWord_923619) baseStart_923619 baseEnd_923619 := by
    simpa [prefixWord, tailWord_923619, baseEnd_923619] using wordTrace_append hprefix tailTrace_923619
  have hstable : (prefixWord ++ tailWord_923619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923619).length < 2 ^ (prefixWord ++ tailWord_923619).sum := by decide
  have hdescent : baseEnd_923619 < baseStart_923619 := by decide
  rcases family_descends (prefixWord ++ tailWord_923619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923726 : List Nat := [4, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_923726 : Nat := 118140960795 + 923726 * 2 ^ 59
def prefixEnd_923726 : Nat := 4983230072969 + 3 ^ 40 * 923726 * 2
def baseEnd_923726 : Nat := 210806858246736956211941

theorem tailTrace_923726 : CollatzResearch.WordTrace tailWord_923726 prefixEnd_923726 210806858246736956211941 := by
  unfold tailWord_923726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4211381881438242085750879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22460703367670624457338021 4211381881438242085750879)
  ·
    refine ⟨6317072822157363128626319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4211381881438242085750879 6317072822157363128626319)
    ·
      refine ⟨9475609233236044692939479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6317072822157363128626319 9475609233236044692939479)
      ·
        refine ⟨14213413849854067039409219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9475609233236044692939479 14213413849854067039409219)
        ·
          refine ⟨21320120774781100559113829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14213413849854067039409219 21320120774781100559113829)
          ·
            refine ⟨3997522645271456354833843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21320120774781100559113829 3997522645271456354833843)
            ·
              refine ⟨5996283967907184532250765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3997522645271456354833843 5996283967907184532250765)
              ·
                refine ⟨2248606487965194199594037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5996283967907184532250765 2248606487965194199594037)
                ·
                  refine ⟨210806858246736956211941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2248606487965194199594037 210806858246736956211941)
                  ·
                    rfl

theorem cell21_923726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_923726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923726 prefixEnd_923726 := by exact prefixLift 923726
  have htrace : WordTrace (prefixWord ++ tailWord_923726) baseStart_923726 baseEnd_923726 := by
    simpa [prefixWord, tailWord_923726, baseEnd_923726] using wordTrace_append hprefix tailTrace_923726
  have hstable : (prefixWord ++ tailWord_923726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923726).length < 2 ^ (prefixWord ++ tailWord_923726).sum := by decide
  have hdescent : baseEnd_923726 < baseStart_923726 := by decide
  rcases family_descends (prefixWord ++ tailWord_923726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923746 : List Nat := [3, 3, 2, 2, 2, 2, 2, 5]
def baseStart_923746 : Nat := 118140960795 + 923746 * 2 ^ 59
def prefixEnd_923746 : Nat := 4983230072969 + 3 ^ 40 * 923746 * 2
def baseEnd_923746 : Nat := 70270474173073788626189

theorem tailTrace_923746 : CollatzResearch.WordTrace tailWord_923746 prefixEnd_923746 70270474173073788626189 := by
  unfold tailWord_923746
  simp only [CollatzResearch.WordTrace]
  refine ⟨8422946127858370025433773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22461189674288986734490061 8422946127858370025433773)
  ·
    refine ⟨3158604797946888759537665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8422946127858370025433773 3158604797946888759537665)
    ·
      refine ⟨2368953598460166569653249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3158604797946888759537665 2368953598460166569653249)
      ·
        refine ⟨1776715198845124927239937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2368953598460166569653249 1776715198845124927239937)
        ·
          refine ⟨1332536399133843695429953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1776715198845124927239937 1332536399133843695429953)
          ·
            refine ⟨999402299350382771572465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1332536399133843695429953 999402299350382771572465)
            ·
              refine ⟨749551724512787078679349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 999402299350382771572465 749551724512787078679349)
              ·
                refine ⟨70270474173073788626189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 749551724512787078679349 70270474173073788626189)
                ·
                  rfl

theorem cell21_923746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_923746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923746 prefixEnd_923746 := by exact prefixLift 923746
  have htrace : WordTrace (prefixWord ++ tailWord_923746) baseStart_923746 baseEnd_923746 := by
    simpa [prefixWord, tailWord_923746, baseEnd_923746] using wordTrace_append hprefix tailTrace_923746
  have hstable : (prefixWord ++ tailWord_923746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923746).length < 2 ^ (prefixWord ++ tailWord_923746).sum := by decide
  have hdescent : baseEnd_923746 < baseStart_923746 := by decide
  rcases family_descends (prefixWord ++ tailWord_923746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923760 : List Nat := [2, 1, 1, 1, 5, 4, 1, 3, 3]
def baseStart_923760 : Nat := 118140960795 + 923760 * 2 ^ 59
def prefixEnd_923760 : Nat := 4983230072969 + 3 ^ 40 * 923760 * 2
def baseEnd_923760 : Nat := 210814617509960452645205

theorem tailTrace_923760 : CollatzResearch.WordTrace tailWord_923760 prefixEnd_923760 210814617509960452645205 := by
  unfold tailWord_923760
  simp only [CollatzResearch.WordTrace]
  refine ⟨16846147566691380246372367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22461530088921840328496489 16846147566691380246372367)
  ·
    refine ⟨25269221350037070369558551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16846147566691380246372367 25269221350037070369558551)
    ·
      refine ⟨37903832025055605554337827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25269221350037070369558551 37903832025055605554337827)
      ·
        refine ⟨56855748037583408331506741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37903832025055605554337827 56855748037583408331506741)
        ·
          refine ⟨5330226378523444531078757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56855748037583408331506741 5330226378523444531078757)
          ·
            refine ⟨999417445973145849577267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5330226378523444531078757 999417445973145849577267)
            ·
              refine ⟨1499126168959718774365901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999417445973145849577267 1499126168959718774365901)
              ·
                refine ⟨562172313359894540387213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1499126168959718774365901 562172313359894540387213)
                ·
                  refine ⟨210814617509960452645205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562172313359894540387213 210814617509960452645205)
                  ·
                    rfl

theorem cell21_923760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 3].length) (baseStart_923760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923760 prefixEnd_923760 := by exact prefixLift 923760
  have htrace : WordTrace (prefixWord ++ tailWord_923760) baseStart_923760 baseEnd_923760 := by
    simpa [prefixWord, tailWord_923760, baseEnd_923760] using wordTrace_append hprefix tailTrace_923760
  have hstable : (prefixWord ++ tailWord_923760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923760).length < 2 ^ (prefixWord ++ tailWord_923760).sum := by decide
  have hdescent : baseEnd_923760 < baseStart_923760 := by decide
  rcases family_descends (prefixWord ++ tailWord_923760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923777 : List Nat := [1, 2, 4, 2, 3, 1, 3, 2, 3]
def baseStart_923777 : Nat := 118140960795 + 923777 * 2 ^ 59
def prefixEnd_923777 : Nat := 4983230072969 + 3 ^ 40 * 923777 * 2
def baseEnd_923777 : Nat := 210818497141572200861837

theorem tailTrace_923777 : CollatzResearch.WordTrace tailWord_923777 prefixEnd_923777 210818497141572200861837 := by
  unfold tailWord_923777
  simp only [CollatzResearch.WordTrace]
  refine ⟨33692915174321172396113585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22461943449547448264075723 33692915174321172396113585)
  ·
    refine ⟨25269686380740879297085189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33692915174321172396113585 25269686380740879297085189)
    ·
      refine ⟨4738066196388914868203473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25269686380740879297085189 4738066196388914868203473)
      ·
        refine ⟨3553549647291686151152605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4738066196388914868203473 3553549647291686151152605)
        ·
          refine ⟨1332581117734382306682227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3553549647291686151152605 1332581117734382306682227)
          ·
            refine ⟨1998871676601573460023341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332581117734382306682227 1998871676601573460023341)
            ·
              refine ⟨749576878725590047508753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1998871676601573460023341 749576878725590047508753)
              ·
                refine ⟨562182659044192535631565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749576878725590047508753 562182659044192535631565)
                ·
                  refine ⟨210818497141572200861837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562182659044192535631565 210818497141572200861837)
                  ·
                    rfl

theorem cell21_923777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 3].length) (baseStart_923777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923777 prefixEnd_923777 := by exact prefixLift 923777
  have htrace : WordTrace (prefixWord ++ tailWord_923777) baseStart_923777 baseEnd_923777 := by
    simpa [prefixWord, tailWord_923777, baseEnd_923777] using wordTrace_append hprefix tailTrace_923777
  have hstable : (prefixWord ++ tailWord_923777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923777).length < 2 ^ (prefixWord ++ tailWord_923777).sum := by decide
  have hdescent : baseEnd_923777 < baseStart_923777 := by decide
  rcases family_descends (prefixWord ++ tailWord_923777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923828 : List Nat := [2, 5, 3, 1, 1, 2, 2, 2, 3]
def baseStart_923828 : Nat := 118140960795 + 923828 * 2 ^ 59
def prefixEnd_923828 : Nat := 4983230072969 + 3 ^ 40 * 923828 * 2
def baseEnd_923828 : Nat := 210830136036407445511733

theorem tailTrace_923828 : CollatzResearch.WordTrace tailWord_923828 prefixEnd_923828 210830136036407445511733 := by
  unfold tailWord_923828
  simp only [CollatzResearch.WordTrace]
  refine ⟨16847387648568204053110069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22463183531424272070813425 16847387648568204053110069)
  ·
    refine ⟨1579442592053269129979069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16847387648568204053110069 1579442592053269129979069)
    ·
      refine ⟨592290972019975923742151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1579442592053269129979069 592290972019975923742151)
      ·
        refine ⟨888436458029963885613227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592290972019975923742151 888436458029963885613227)
        ·
          refine ⟨1332654687044945828419841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888436458029963885613227 1332654687044945828419841)
          ·
            refine ⟨999491015283709371314881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1332654687044945828419841 999491015283709371314881)
            ·
              refine ⟨749618261462782028486161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 999491015283709371314881 749618261462782028486161)
              ·
                refine ⟨562213696097086521364621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749618261462782028486161 562213696097086521364621)
                ·
                  refine ⟨210830136036407445511733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562213696097086521364621 210830136036407445511733)
                  ·
                    rfl

theorem cell21_923828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_923828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923828 prefixEnd_923828 := by exact prefixLift 923828
  have htrace : WordTrace (prefixWord ++ tailWord_923828) baseStart_923828 baseEnd_923828 := by
    simpa [prefixWord, tailWord_923828, baseEnd_923828] using wordTrace_append hprefix tailTrace_923828
  have hstable : (prefixWord ++ tailWord_923828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923828).length < 2 ^ (prefixWord ++ tailWord_923828).sum := by decide
  have hdescent : baseEnd_923828 < baseStart_923828 := by decide
  rcases family_descends (prefixWord ++ tailWord_923828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923833 : List Nat := [1, 2, 1, 4, 1, 2, 4, 2, 4]
def baseStart_923833 : Nat := 118140960795 + 923833 * 2 ^ 59
def prefixEnd_923833 : Nat := 4983230072969 + 3 ^ 40 * 923833 * 2
def baseEnd_923833 : Nat := 210831277104528547928389

theorem tailTrace_923833 : CollatzResearch.WordTrace tailWord_923833 prefixEnd_923833 210831277104528547928389 := by
  unfold tailWord_923833
  simp only [CollatzResearch.WordTrace]
  refine ⟨33694957662118293960152153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22463305108078862640101435 33694957662118293960152153)
  ·
    refine ⟨25271218246588720470114115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33694957662118293960152153 25271218246588720470114115)
    ·
      refine ⟨37906827369883080705171173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25271218246588720470114115 37906827369883080705171173)
      ·
        refine ⟨7107530131853077632219595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37906827369883080705171173 7107530131853077632219595)
        ·
          refine ⟨10661295197779616448329393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7107530131853077632219595 10661295197779616448329393)
          ·
            refine ⟨7995971398334712336247045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10661295197779616448329393 7995971398334712336247045)
            ·
              refine ⟨1499244637187758563046321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7995971398334712336247045 1499244637187758563046321)
              ·
                refine ⟨1124433477890818922284741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1499244637187758563046321 1124433477890818922284741)
                ·
                  refine ⟨210831277104528547928389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1124433477890818922284741 210831277104528547928389)
                  ·
                    rfl

theorem cell21_923833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_923833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923833 prefixEnd_923833 := by exact prefixLift 923833
  have htrace : WordTrace (prefixWord ++ tailWord_923833) baseStart_923833 baseEnd_923833 := by
    simpa [prefixWord, tailWord_923833, baseEnd_923833] using wordTrace_append hprefix tailTrace_923833
  have hstable : (prefixWord ++ tailWord_923833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923833).length < 2 ^ (prefixWord ++ tailWord_923833).sum := by decide
  have hdescent : baseEnd_923833 < baseStart_923833 := by decide
  rcases family_descends (prefixWord ++ tailWord_923833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923836 : List Nat := [2, 2, 2, 3, 3, 1, 1, 4, 3]
def baseStart_923836 : Nat := 118140960795 + 923836 * 2 ^ 59
def prefixEnd_923836 : Nat := 4983230072969 + 3 ^ 40 * 923836 * 2
def baseEnd_923836 : Nat := 210831961745401209378383

theorem tailTrace_923836 : CollatzResearch.WordTrace tailWord_923836 prefixEnd_923836 210831961745401209378383 := by
  unfold tailWord_923836
  simp only [CollatzResearch.WordTrace]
  refine ⟨16847533540553712736255681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22463378054071616981674241 16847533540553712736255681)
  ·
    refine ⟨12635650155415284552191761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16847533540553712736255681 12635650155415284552191761)
    ·
      refine ⟨9476737616561463414143821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12635650155415284552191761 9476737616561463414143821)
      ·
        refine ⟨3553776606210548780303933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9476737616561463414143821 3553776606210548780303933)
        ·
          refine ⟨1332666227328955792613975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3553776606210548780303933 1332666227328955792613975)
          ·
            refine ⟨1998999340993433688920963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332666227328955792613975 1998999340993433688920963)
            ·
              refine ⟨2998499011490150533381445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1998999340993433688920963 2998499011490150533381445)
              ·
                refine ⟨562218564654403225009021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2998499011490150533381445 562218564654403225009021)
                ·
                  refine ⟨210831961745401209378383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562218564654403225009021 210831961745401209378383)
                  ·
                    rfl

theorem cell21_923836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_923836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923836 prefixEnd_923836 := by exact prefixLift 923836
  have htrace : WordTrace (prefixWord ++ tailWord_923836) baseStart_923836 baseEnd_923836 := by
    simpa [prefixWord, tailWord_923836, baseEnd_923836] using wordTrace_append hprefix tailTrace_923836
  have hstable : (prefixWord ++ tailWord_923836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923836).length < 2 ^ (prefixWord ++ tailWord_923836).sum := by decide
  have hdescent : baseEnd_923836 < baseStart_923836 := by decide
  rcases family_descends (prefixWord ++ tailWord_923836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923864 : List Nat := [2, 1, 2, 2, 4, 2, 3, 5]
def baseStart_923864 : Nat := 118140960795 + 923864 * 2 ^ 59
def prefixEnd_923864 : Nat := 4983230072969 + 3 ^ 40 * 923864 * 2
def baseEnd_923864 : Nat := 70279450575626460970553

theorem tailTrace_923864 : CollatzResearch.WordTrace tailWord_923864 prefixEnd_923864 70279450575626460970553 := by
  unfold tailWord_923864
  simp only [CollatzResearch.WordTrace]
  refine ⟨16848044162502993127265323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22464058883337324169687097 16848044162502993127265323)
  ·
    refine ⟨25272066243754489690897985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16848044162502993127265323 25272066243754489690897985)
    ·
      refine ⟨18954049682815867268173489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25272066243754489690897985 18954049682815867268173489)
      ·
        refine ⟨14215537262111900451130117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18954049682815867268173489 14215537262111900451130117)
        ·
          refine ⟨2665413236645981334586897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14215537262111900451130117 2665413236645981334586897)
          ·
            refine ⟨1999059927484486000940173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2665413236645981334586897 1999059927484486000940173)
            ·
              refine ⟨749647472806682250352565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1999059927484486000940173 749647472806682250352565)
              ·
                refine ⟨70279450575626460970553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 749647472806682250352565 70279450575626460970553)
                ·
                  rfl

theorem cell21_923864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 5].length) (baseStart_923864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923864 prefixEnd_923864 := by exact prefixLift 923864
  have htrace : WordTrace (prefixWord ++ tailWord_923864) baseStart_923864 baseEnd_923864 := by
    simpa [prefixWord, tailWord_923864, baseEnd_923864] using wordTrace_append hprefix tailTrace_923864
  have hstable : (prefixWord ++ tailWord_923864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923864).length < 2 ^ (prefixWord ++ tailWord_923864).sum := by decide
  have hdescent : baseEnd_923864 < baseStart_923864 := by decide
  rcases family_descends (prefixWord ++ tailWord_923864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923937 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 7]
def baseStart_923937 : Nat := 118140960795 + 923937 * 2 ^ 59
def prefixEnd_923937 : Nat := 4983230072969 + 3 ^ 40 * 923937 * 2
def baseEnd_923937 : Nat := 210855011321447478194843

theorem tailTrace_923937 : CollatzResearch.WordTrace tailWord_923937 prefixEnd_923937 210855011321447478194843 := by
  unfold tailWord_923937
  simp only [CollatzResearch.WordTrace]
  refine ⟨33698750853741519721938065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22465833902494346481292043 33698750853741519721938065)
  ·
    refine ⟨25274063140306139791453549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33698750853741519721938065 25274063140306139791453549)
    ·
      refine ⟨9477773677614802421795081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25274063140306139791453549 9477773677614802421795081)
      ·
        refine ⟨7108330258211101816346311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9477773677614802421795081 7108330258211101816346311)
        ·
          refine ⟨10662495387316652724519467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7108330258211101816346311 10662495387316652724519467)
          ·
            refine ⟨15993743080974979086779201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10662495387316652724519467 15993743080974979086779201)
            ·
              refine ⟨11995307310731234315084401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15993743080974979086779201 11995307310731234315084401)
              ·
                refine ⟨8996480483048425736313301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11995307310731234315084401 8996480483048425736313301)
                ·
                  refine ⟨210855011321447478194843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8996480483048425736313301 210855011321447478194843)
                  ·
                    rfl

theorem cell21_923937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_923937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_923937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_923937 prefixEnd_923937 := by exact prefixLift 923937
  have htrace : WordTrace (prefixWord ++ tailWord_923937) baseStart_923937 baseEnd_923937 := by
    simpa [prefixWord, tailWord_923937, baseEnd_923937] using wordTrace_append hprefix tailTrace_923937
  have hstable : (prefixWord ++ tailWord_923937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923937).length < 2 ^ (prefixWord ++ tailWord_923937).sum := by decide
  have hdescent : baseEnd_923937 < baseStart_923937 := by decide
  rcases family_descends (prefixWord ++ tailWord_923937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924002 : List Nat := [3, 3, 2, 1, 1, 3, 2, 2, 4]
def baseStart_924002 : Nat := 118140960795 + 924002 * 2 ^ 59
def prefixEnd_924002 : Nat := 4983230072969 + 3 ^ 40 * 924002 * 2
def baseEnd_924002 : Nat := 210869845207021809611377

theorem tailTrace_924002 : CollatzResearch.WordTrace tailWord_924002 prefixEnd_924002 210869845207021809611377 := by
  unfold tailWord_924002
  simp only [CollatzResearch.WordTrace]
  refine ⟨8425280399626508955763565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22467414399004023882036173 8425280399626508955763565)
  ·
    refine ⟨3159480149859940858411337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8425280399626508955763565 3159480149859940858411337)
    ·
      refine ⟨2369610112394955643808503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3159480149859940858411337 2369610112394955643808503)
      ·
        refine ⟨3554415168592433465712755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2369610112394955643808503 3554415168592433465712755)
        ·
          refine ⟨5331622752888650198569133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3554415168592433465712755 5331622752888650198569133)
          ·
            refine ⟨1999358532333243824463425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5331622752888650198569133 1999358532333243824463425)
            ·
              refine ⟨1499518899249932868347569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1999358532333243824463425 1499518899249932868347569)
              ·
                refine ⟨1124639174437449651260677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1499518899249932868347569 1124639174437449651260677)
                ·
                  refine ⟨210869845207021809611377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1124639174437449651260677 210869845207021809611377)
                  ·
                    rfl

theorem cell21_924002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_924002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924002 prefixEnd_924002 := by exact prefixLift 924002
  have htrace : WordTrace (prefixWord ++ tailWord_924002) baseStart_924002 baseEnd_924002 := by
    simpa [prefixWord, tailWord_924002, baseEnd_924002] using wordTrace_append hprefix tailTrace_924002
  have hstable : (prefixWord ++ tailWord_924002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924002).length < 2 ^ (prefixWord ++ tailWord_924002).sum := by decide
  have hdescent : baseEnd_924002 < baseStart_924002 := by decide
  rcases family_descends (prefixWord ++ tailWord_924002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924061 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 6]
def baseStart_924061 : Nat := 118140960795 + 924061 * 2 ^ 59
def prefixEnd_924061 : Nat := 4983230072969 + 3 ^ 40 * 924061 * 2
def baseEnd_924061 : Nat := 210883309810850818127923

theorem tailTrace_924061 : CollatzResearch.WordTrace tailWord_924061 prefixEnd_924061 210883309810850818127923 := by
  unfold tailWord_924061
  simp only [CollatzResearch.WordTrace]
  refine ⟨33703273505292288899452037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22468849003528192599634691 33703273505292288899452037)
  ·
    refine ⟨6319363782242304168647257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33703273505292288899452037 6319363782242304168647257)
    ·
      refine ⟨4739522836681728126485443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6319363782242304168647257 4739522836681728126485443)
      ·
        refine ⟨7109284255022592189728165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4739522836681728126485443 7109284255022592189728165)
        ·
          refine ⟨1332990797816736035574031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7109284255022592189728165 1332990797816736035574031)
          ·
            refine ⟨1999486196725104053361047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332990797816736035574031 1999486196725104053361047)
            ·
              refine ⟨2999229295087656080041571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999486196725104053361047 2999229295087656080041571)
              ·
                refine ⟨4498843942631484120062357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2999229295087656080041571 4498843942631484120062357)
                ·
                  refine ⟨210883309810850818127923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4498843942631484120062357 210883309810850818127923)
                  ·
                    rfl

theorem cell21_924061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_924061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924061 prefixEnd_924061 := by exact prefixLift 924061
  have htrace : WordTrace (prefixWord ++ tailWord_924061) baseStart_924061 baseEnd_924061 := by
    simpa [prefixWord, tailWord_924061, baseEnd_924061] using wordTrace_append hprefix tailTrace_924061
  have hstable : (prefixWord ++ tailWord_924061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924061).length < 2 ^ (prefixWord ++ tailWord_924061).sum := by decide
  have hdescent : baseEnd_924061 < baseStart_924061 := by decide
  rcases family_descends (prefixWord ++ tailWord_924061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924092 : List Nat := [2, 2, 2, 4, 1, 1, 4, 5]
def baseStart_924092 : Nat := 118140960795 + 924092 * 2 ^ 59
def prefixEnd_924092 : Nat := 4983230072969 + 3 ^ 40 * 924092 * 2
def baseEnd_924092 : Nat := 70296794811067217703731

theorem tailTrace_924092 : CollatzResearch.WordTrace tailWord_924092 prefixEnd_924092 70296794811067217703731 := by
  unfold tailWord_924092
  simp only [CollatzResearch.WordTrace]
  refine ⟨16852202084089990596915265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22469602778786654129220353 16852202084089990596915265)
  ·
    refine ⟨12639151563067492947686449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16852202084089990596915265 12639151563067492947686449)
    ·
      refine ⟨9479363672300619710764837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12639151563067492947686449 9479363672300619710764837)
      ·
        refine ⟨1777380688556366195768407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9479363672300619710764837 1777380688556366195768407)
        ·
          refine ⟨2666071032834549293652611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1777380688556366195768407 2666071032834549293652611)
          ·
            refine ⟨3999106549251823940478917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2666071032834549293652611 3999106549251823940478917)
            ·
              refine ⟨749832477984716988839797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3999106549251823940478917 749832477984716988839797)
              ·
                refine ⟨70296794811067217703731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 749832477984716988839797 70296794811067217703731)
                ·
                  rfl

theorem cell21_924092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 5].length) (baseStart_924092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924092 prefixEnd_924092 := by exact prefixLift 924092
  have htrace : WordTrace (prefixWord ++ tailWord_924092) baseStart_924092 baseEnd_924092 := by
    simpa [prefixWord, tailWord_924092, baseEnd_924092] using wordTrace_append hprefix tailTrace_924092
  have hstable : (prefixWord ++ tailWord_924092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924092).length < 2 ^ (prefixWord ++ tailWord_924092).sum := by decide
  have hdescent : baseEnd_924092 < baseStart_924092 := by decide
  rcases family_descends (prefixWord ++ tailWord_924092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924120 : List Nat := [2, 1, 2, 2, 2, 1, 1, 6, 4]
def baseStart_924120 : Nat := 118140960795 + 924120 * 2 ^ 59
def prefixEnd_924120 : Nat := 4983230072969 + 3 ^ 40 * 924120 * 2
def baseEnd_924120 : Nat := 210896774414679826644469

theorem tailTrace_924120 : CollatzResearch.WordTrace tailWord_924120 prefixEnd_924120 210896774414679826644469 := by
  unfold tailWord_924120
  simp only [CollatzResearch.WordTrace]
  refine ⟨16852712706039270987924907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22470283608052361317233209 16852712706039270987924907)
  ·
    refine ⟨25279069059058906481887361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16852712706039270987924907 25279069059058906481887361)
    ·
      refine ⟨18959301794294179861415521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25279069059058906481887361 18959301794294179861415521)
      ·
        refine ⟨14219476345720634896061641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18959301794294179861415521 14219476345720634896061641)
        ·
          refine ⟨10664607259290476172046231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14219476345720634896061641 10664607259290476172046231)
          ·
            refine ⟨15996910888935714258069347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10664607259290476172046231 15996910888935714258069347)
            ·
              refine ⟨23995366333403571387104021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15996910888935714258069347 23995366333403571387104021)
              ·
                refine ⟨1124782796878292408770501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23995366333403571387104021 1124782796878292408770501)
                ·
                  refine ⟨210896774414679826644469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1124782796878292408770501 210896774414679826644469)
                  ·
                    rfl

theorem cell21_924120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_924120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924120 prefixEnd_924120 := by exact prefixLift 924120
  have htrace : WordTrace (prefixWord ++ tailWord_924120) baseStart_924120 baseEnd_924120 := by
    simpa [prefixWord, tailWord_924120, baseEnd_924120] using wordTrace_append hprefix tailTrace_924120
  have hstable : (prefixWord ++ tailWord_924120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924120).length < 2 ^ (prefixWord ++ tailWord_924120).sum := by decide
  have hdescent : baseEnd_924120 < baseStart_924120 := by decide
  rcases family_descends (prefixWord ++ tailWord_924120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924210 : List Nat := [3, 2, 1, 1, 2, 1, 2, 9]
def baseStart_924210 : Nat := 118140960795 + 924210 * 2 ^ 59
def prefixEnd_924210 : Nat := 4983230072969 + 3 ^ 40 * 924210 * 2
def baseEnd_924210 : Nat := 70305771213619890048095

theorem tailTrace_924210 : CollatzResearch.WordTrace tailWord_924210 prefixEnd_924210 70305771213619890048095 := by
  unfold tailWord_924210
  simp only [CollatzResearch.WordTrace]
  refine ⟨8427176995438121836656521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22472471987834991564417389 8427176995438121836656521)
  ·
    refine ⟨6320382746578591377492391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8427176995438121836656521 6320382746578591377492391)
    ·
      refine ⟨9480574119867887066238587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6320382746578591377492391 9480574119867887066238587)
      ·
        refine ⟨14220861179801830599357881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9480574119867887066238587 14220861179801830599357881)
        ·
          refine ⟨10665645884851372949518411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14220861179801830599357881 10665645884851372949518411)
          ·
            refine ⟨15998468827277059424277617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10665645884851372949518411 15998468827277059424277617)
            ·
              refine ⟨11998851620457794568208213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15998468827277059424277617 11998851620457794568208213)
              ·
                refine ⟨70305771213619890048095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11998851620457794568208213 70305771213619890048095)
                ·
                  rfl

theorem cell21_924210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_924210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924210 prefixEnd_924210 := by exact prefixLift 924210
  have htrace : WordTrace (prefixWord ++ tailWord_924210) baseStart_924210 baseEnd_924210 := by
    simpa [prefixWord, tailWord_924210, baseEnd_924210] using wordTrace_append hprefix tailTrace_924210
  have hstable : (prefixWord ++ tailWord_924210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924210).length < 2 ^ (prefixWord ++ tailWord_924210).sum := by decide
  have hdescent : baseEnd_924210 < baseStart_924210 := by decide
  rcases family_descends (prefixWord ++ tailWord_924210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924230 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_924230 : Nat := 118140960795 + 924230 * 2 ^ 59
def prefixEnd_924230 : Nat := 4983230072969 + 3 ^ 40 * 924230 * 2
def baseEnd_924230 : Nat := 210921877913344079810911

theorem tailTrace_924230 : CollatzResearch.WordTrace tailWord_924230 prefixEnd_924230 210921877913344079810911 := by
  unfold tailWord_924230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1053419920052500961323567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22472958294453353841569429 1053419920052500961323567)
  ·
    refine ⟨1580129880078751441985351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1053419920052500961323567 1580129880078751441985351)
    ·
      refine ⟨2370194820118127162978027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1580129880078751441985351 2370194820118127162978027)
      ·
        refine ⟨3555292230177190744467041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2370194820118127162978027 3555292230177190744467041)
        ·
          refine ⟨2666469172632893058350281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3555292230177190744467041 2666469172632893058350281)
          ·
            refine ⟨1999851879474669793762711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2666469172632893058350281 1999851879474669793762711)
            ·
              refine ⟨2999777819212004690644067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999851879474669793762711 2999777819212004690644067)
              ·
                refine ⟨4499666728818007035966101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2999777819212004690644067 4499666728818007035966101)
                ·
                  refine ⟨210921877913344079810911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4499666728818007035966101 210921877913344079810911)
                  ·
                    rfl

theorem cell21_924230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_924230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924230 prefixEnd_924230 := by exact prefixLift 924230
  have htrace : WordTrace (prefixWord ++ tailWord_924230) baseStart_924230 baseEnd_924230 := by
    simpa [prefixWord, tailWord_924230, baseEnd_924230] using wordTrace_append hprefix tailTrace_924230
  have hstable : (prefixWord ++ tailWord_924230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924230).length < 2 ^ (prefixWord ++ tailWord_924230).sum := by decide
  have hdescent : baseEnd_924230 < baseStart_924230 := by decide
  rcases family_descends (prefixWord ++ tailWord_924230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924241 : List Nat := [1, 2, 2, 1, 3, 3, 1, 3, 5]
def baseStart_924241 : Nat := 118140960795 + 924241 * 2 ^ 59
def prefixEnd_924241 : Nat := 4983230072969 + 3 ^ 40 * 924241 * 2
def baseEnd_924241 : Nat := 210924388263210505127555

theorem tailTrace_924241 : CollatzResearch.WordTrace tailWord_924241 prefixEnd_924241 210924388263210505127555 := by
  unfold tailWord_924241
  simp only [CollatzResearch.WordTrace]
  refine ⟨33709838644640179641004577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22473225763093453094003051 33709838644640179641004577)
  ·
    refine ⟨25282378983480134730753433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33709838644640179641004577 25282378983480134730753433)
    ·
      refine ⟨18961784237610101048065075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25282378983480134730753433 18961784237610101048065075)
      ·
        refine ⟨28442676356415151572097613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18961784237610101048065075 28442676356415151572097613)
        ·
          refine ⟨10666003633655681839536605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28442676356415151572097613 10666003633655681839536605)
          ·
            refine ⟨3999751362620880689826227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10666003633655681839536605 3999751362620880689826227)
            ·
              refine ⟨5999627043931321034739341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3999751362620880689826227 5999627043931321034739341)
              ·
                refine ⟨2249860141474245388027253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5999627043931321034739341 2249860141474245388027253)
                ·
                  refine ⟨210924388263210505127555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2249860141474245388027253 210924388263210505127555)
                  ·
                    rfl

theorem cell21_924241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_924241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924241 prefixEnd_924241 := by exact prefixLift 924241
  have htrace : WordTrace (prefixWord ++ tailWord_924241) baseStart_924241 baseEnd_924241 := by
    simpa [prefixWord, tailWord_924241, baseEnd_924241] using wordTrace_append hprefix tailTrace_924241
  have hstable : (prefixWord ++ tailWord_924241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924241).length < 2 ^ (prefixWord ++ tailWord_924241).sum := by decide
  have hdescent : baseEnd_924241 < baseStart_924241 := by decide
  rcases family_descends (prefixWord ++ tailWord_924241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924261 : List Nat := [1, 3, 1, 3, 5, 1, 2, 5]
def baseStart_924261 : Nat := 118140960795 + 924261 * 2 ^ 59
def prefixEnd_924261 : Nat := 4983230072969 + 3 ^ 40 * 924261 * 2
def baseEnd_924261 : Nat := 70309650845231638264727

theorem tailTrace_924261 : CollatzResearch.WordTrace tailWord_924261 prefixEnd_924261 70309650845231638264727 := by
  unfold tailWord_924261
  simp only [CollatzResearch.WordTrace]
  refine ⟨33710568104567723056732637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22473712069711815371155091 33710568104567723056732637)
  ·
    refine ⟨12641463039212896146274739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33710568104567723056732637 12641463039212896146274739)
    ·
      refine ⟨18962194558819344219412109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12641463039212896146274739 18962194558819344219412109)
      ·
        refine ⟨7110822959557254082279541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18962194558819344219412109 7110822959557254082279541)
        ·
          refine ⟨666639652458492570213707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7110822959557254082279541 666639652458492570213707)
          ·
            refine ⟨999959478687738855320561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666639652458492570213707 999959478687738855320561)
            ·
              refine ⟨749969609015804141490421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 999959478687738855320561 749969609015804141490421)
              ·
                refine ⟨70309650845231638264727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 749969609015804141490421 70309650845231638264727)
                ·
                  rfl

theorem cell21_924261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 5].length) (baseStart_924261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924261 prefixEnd_924261 := by exact prefixLift 924261
  have htrace : WordTrace (prefixWord ++ tailWord_924261) baseStart_924261 baseEnd_924261 := by
    simpa [prefixWord, tailWord_924261, baseEnd_924261] using wordTrace_append hprefix tailTrace_924261
  have hstable : (prefixWord ++ tailWord_924261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924261).length < 2 ^ (prefixWord ++ tailWord_924261).sum := by decide
  have hdescent : baseEnd_924261 < baseStart_924261 := by decide
  rcases family_descends (prefixWord ++ tailWord_924261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924292 : List Nat := [2, 3, 2, 1, 3, 2, 3, 2, 3]
def baseStart_924292 : Nat := 118140960795 + 924292 * 2 ^ 59
def prefixEnd_924292 : Nat := 4983230072969 + 3 ^ 40 * 924292 * 2
def baseEnd_924292 : Nat := 210936027158045749777451

theorem tailTrace_924292 : CollatzResearch.WordTrace tailWord_924292 prefixEnd_924292 210936027158045749777451 := by
  unfold tailWord_924292
  simp only [CollatzResearch.WordTrace]
  refine ⟨16855849383727707675555565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22474465844970276900740753 16855849383727707675555565)
  ·
    refine ⟨6320943518897890378333337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16855849383727707675555565 6320943518897890378333337)
    ·
      refine ⟨4740707639173417783750003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6320943518897890378333337 4740707639173417783750003)
      ·
        refine ⟨7111061458760126675625005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4740707639173417783750003 7111061458760126675625005)
        ·
          refine ⟨2666648047035047503359377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7111061458760126675625005 2666648047035047503359377)
          ·
            refine ⟨1999986035276285627519533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2666648047035047503359377 1999986035276285627519533)
            ·
              refine ⟨749994763228607110319825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1999986035276285627519533 749994763228607110319825)
              ·
                refine ⟨562496072421455332739869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749994763228607110319825 562496072421455332739869)
                ·
                  refine ⟨210936027158045749777451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562496072421455332739869 210936027158045749777451)
                  ·
                    rfl

theorem cell21_924292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_924292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924292 prefixEnd_924292 := by exact prefixLift 924292
  have htrace : WordTrace (prefixWord ++ tailWord_924292) baseStart_924292 baseEnd_924292 := by
    simpa [prefixWord, tailWord_924292, baseEnd_924292] using wordTrace_append hprefix tailTrace_924292
  have hstable : (prefixWord ++ tailWord_924292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924292).length < 2 ^ (prefixWord ++ tailWord_924292).sum := by decide
  have hdescent : baseEnd_924292 < baseStart_924292 := by decide
  rcases family_descends (prefixWord ++ tailWord_924292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924306 : List Nat := [3, 2, 3, 1, 2, 1, 4, 1, 4]
def baseStart_924306 : Nat := 118140960795 + 924306 * 2 ^ 59
def prefixEnd_924306 : Nat := 4983230072969 + 3 ^ 40 * 924306 * 2
def baseEnd_924306 : Nat := 210939222148784836544089

theorem tailTrace_924306 : CollatzResearch.WordTrace tailWord_924306 prefixEnd_924306 210939222148784836544089 := by
  unfold tailWord_924306
  simp only [CollatzResearch.WordTrace]
  refine ⟨8428052347351173935530193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22474806259603130494747181 8428052347351173935530193)
  ·
    refine ⟨6321039260513380451647645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8428052347351173935530193 6321039260513380451647645)
    ·
      refine ⟨2370389722692517669367867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6321039260513380451647645 2370389722692517669367867)
      ·
        refine ⟨3555584584038776504051801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2370389722692517669367867 3555584584038776504051801)
        ·
          refine ⟨2666688438029082378038851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3555584584038776504051801 2666688438029082378038851)
          ·
            refine ⟨4000032657043623567058277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2666688438029082378038851 4000032657043623567058277)
            ·
              refine ⟨750006123195679418823427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4000032657043623567058277 750006123195679418823427)
              ·
                refine ⟨1125009184793519128235141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750006123195679418823427 1125009184793519128235141)
                ·
                  refine ⟨210939222148784836544089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1125009184793519128235141 210939222148784836544089)
                  ·
                    rfl

theorem cell21_924306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_924306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924306 prefixEnd_924306 := by exact prefixLift 924306
  have htrace : WordTrace (prefixWord ++ tailWord_924306) baseStart_924306 baseEnd_924306 := by
    simpa [prefixWord, tailWord_924306, baseEnd_924306] using wordTrace_append hprefix tailTrace_924306
  have hstable : (prefixWord ++ tailWord_924306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924306).length < 2 ^ (prefixWord ++ tailWord_924306).sum := by decide
  have hdescent : baseEnd_924306 < baseStart_924306 := by decide
  rcases family_descends (prefixWord ++ tailWord_924306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924317 : List Nat := [1, 4, 2, 1, 1, 1, 2, 4, 5]
def baseStart_924317 : Nat := 118140960795 + 924317 * 2 ^ 59
def prefixEnd_924317 : Nat := 4983230072969 + 3 ^ 40 * 924317 * 2
def baseEnd_924317 : Nat := 210941732498651261860733

theorem tailTrace_924317 : CollatzResearch.WordTrace tailWord_924317 prefixEnd_924317 210941732498651261860733 := by
  unfold tailWord_924317
  simp only [CollatzResearch.WordTrace]
  refine ⟨33712610592364844620771205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22475073728243229747180803 33712610592364844620771205)
  ·
    refine ⟨6321114486068408366394601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33712610592364844620771205 6321114486068408366394601)
    ·
      refine ⟨4740835864551306274795951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6321114486068408366394601 4740835864551306274795951)
      ·
        refine ⟨7111253796826959412193927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4740835864551306274795951 7111253796826959412193927)
        ·
          refine ⟨10666880695240439118290891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7111253796826959412193927 10666880695240439118290891)
          ·
            refine ⟨16000321042860658677436337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10666880695240439118290891 16000321042860658677436337)
            ·
              refine ⟨12000240782145494008077253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16000321042860658677436337 12000240782145494008077253)
              ·
                refine ⟨2250045146652280126514485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12000240782145494008077253 2250045146652280126514485)
                ·
                  refine ⟨210941732498651261860733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2250045146652280126514485 210941732498651261860733)
                  ·
                    rfl

theorem cell21_924317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_924317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924317 prefixEnd_924317 := by exact prefixLift 924317
  have htrace : WordTrace (prefixWord ++ tailWord_924317) baseStart_924317 baseEnd_924317 := by
    simpa [prefixWord, tailWord_924317, baseEnd_924317] using wordTrace_append hprefix tailTrace_924317
  have hstable : (prefixWord ++ tailWord_924317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924317).length < 2 ^ (prefixWord ++ tailWord_924317).sum := by decide
  have hdescent : baseEnd_924317 < baseStart_924317 := by decide
  rcases family_descends (prefixWord ++ tailWord_924317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924351 : List Nat := [1, 1, 2, 2, 2, 4, 4, 2, 3]
def baseStart_924351 : Nat := 118140960795 + 924351 * 2 ^ 59
def prefixEnd_924351 : Nat := 4983230072969 + 3 ^ 40 * 924351 * 2
def baseEnd_924351 : Nat := 210949491761874758293997

theorem tailTrace_924351 : CollatzResearch.WordTrace tailWord_924351 prefixEnd_924351 210949491761874758293997 := by
  unfold tailWord_924351
  simp only [CollatzResearch.WordTrace]
  refine ⟨33713850674241668427508907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22475900449494445618339271 33713850674241668427508907)
  ·
    refine ⟨50570776011362502641263361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33713850674241668427508907 50570776011362502641263361)
    ·
      refine ⟨37928082008521876980947521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50570776011362502641263361 37928082008521876980947521)
      ·
        refine ⟨28446061506391407735710641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37928082008521876980947521 28446061506391407735710641)
        ·
          refine ⟨21334546129793555801782981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28446061506391407735710641 21334546129793555801782981)
          ·
            refine ⟨4000227399336291712834309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21334546129793555801782981 4000227399336291712834309)
            ·
              refine ⟨750042637375554696156433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4000227399336291712834309 750042637375554696156433)
              ·
                refine ⟨562531978031666022117325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750042637375554696156433 562531978031666022117325)
                ·
                  refine ⟨210949491761874758293997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562531978031666022117325 210949491761874758293997)
                  ·
                    rfl

theorem cell21_924351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 3].length) (baseStart_924351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924351 prefixEnd_924351 := by exact prefixLift 924351
  have htrace : WordTrace (prefixWord ++ tailWord_924351) baseStart_924351 baseEnd_924351 := by
    simpa [prefixWord, tailWord_924351, baseEnd_924351] using wordTrace_append hprefix tailTrace_924351
  have hstable : (prefixWord ++ tailWord_924351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924351).length < 2 ^ (prefixWord ++ tailWord_924351).sum := by decide
  have hdescent : baseEnd_924351 < baseStart_924351 := by decide
  rcases family_descends (prefixWord ++ tailWord_924351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924410 : List Nat := [3, 1, 1, 1, 1, 3, 4, 4, 3]
def baseStart_924410 : Nat := 118140960795 + 924410 * 2 ^ 59
def prefixEnd_924410 : Nat := 4983230072969 + 3 ^ 40 * 924410 * 2
def baseEnd_924410 : Nat := 210962956365703766810543

theorem tailTrace_924410 : CollatzResearch.WordTrace tailWord_924410 prefixEnd_924410 210962956365703766810543 := by
  unfold tailWord_924410
  simp only [CollatzResearch.WordTrace]
  refine ⟨8429000645256980375976671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22477335054018614335937789 8429000645256980375976671)
  ·
    refine ⟨12643500967885470563965007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8429000645256980375976671 12643500967885470563965007)
    ·
      refine ⟨18965251451828205845947511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12643500967885470563965007 18965251451828205845947511)
      ·
        refine ⟨28447877177742308768921267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18965251451828205845947511 28447877177742308768921267)
        ·
          refine ⟨42671815766613463153381901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28447877177742308768921267 42671815766613463153381901)
          ·
            refine ⟨16001930912480048682518213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42671815766613463153381901 16001930912480048682518213)
            ·
              refine ⟨3000362046090009127972165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16001930912480048682518213 3000362046090009127972165)
              ·
                refine ⟨562567883641876711494781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3000362046090009127972165 562567883641876711494781)
                ·
                  refine ⟨210962956365703766810543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562567883641876711494781 210962956365703766810543)
                  ·
                    rfl

theorem cell21_924410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_924410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924410 prefixEnd_924410 := by exact prefixLift 924410
  have htrace : WordTrace (prefixWord ++ tailWord_924410) baseStart_924410 baseEnd_924410 := by
    simpa [prefixWord, tailWord_924410, baseEnd_924410] using wordTrace_append hprefix tailTrace_924410
  have hstable : (prefixWord ++ tailWord_924410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924410).length < 2 ^ (prefixWord ++ tailWord_924410).sum := by decide
  have hdescent : baseEnd_924410 < baseStart_924410 := by decide
  rcases family_descends (prefixWord ++ tailWord_924410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924461 : List Nat := [1, 5, 3, 2, 2, 1, 1, 1, 5]
def baseStart_924461 : Nat := 118140960795 + 924461 * 2 ^ 59
def prefixEnd_924461 : Nat := 4983230072969 + 3 ^ 40 * 924461 * 2
def baseEnd_924461 : Nat := 210974595260539011460439

theorem tailTrace_924461 : CollatzResearch.WordTrace tailWord_924461 prefixEnd_924461 210974595260539011460439 := by
  unfold tailWord_924461
  simp only [CollatzResearch.WordTrace]
  refine ⟨33717862703843157214013237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22478575135895438142675491 33717862703843157214013237)
  ·
    refine ⟨3161049628485295988813741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33717862703843157214013237 3161049628485295988813741)
    ·
      refine ⟨1185393610681985995805153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3161049628485295988813741 1185393610681985995805153)
      ·
        refine ⟨889045208011489496853865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1185393610681985995805153 889045208011489496853865)
        ·
          refine ⟨666783906008617122640399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 889045208011489496853865 666783906008617122640399)
          ·
            refine ⟨1000175859012925683960599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666783906008617122640399 1000175859012925683960599)
            ·
              refine ⟨1500263788519388525940899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000175859012925683960599 1500263788519388525940899)
              ·
                refine ⟨2250395682779082788911349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1500263788519388525940899 2250395682779082788911349)
                ·
                  refine ⟨210974595260539011460439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2250395682779082788911349 210974595260539011460439)
                  ·
                    rfl

theorem cell21_924461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_924461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924461 prefixEnd_924461 := by exact prefixLift 924461
  have htrace : WordTrace (prefixWord ++ tailWord_924461) baseStart_924461 baseEnd_924461 := by
    simpa [prefixWord, tailWord_924461, baseEnd_924461] using wordTrace_append hprefix tailTrace_924461
  have hstable : (prefixWord ++ tailWord_924461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924461).length < 2 ^ (prefixWord ++ tailWord_924461).sum := by decide
  have hdescent : baseEnd_924461 < baseStart_924461 := by decide
  rcases family_descends (prefixWord ++ tailWord_924461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924514 : List Nat := [3, 3, 2, 1, 12]
def baseStart_924514 : Nat := 118140960795 + 924514 * 2 ^ 59
def prefixEnd_924514 : Nat := 4983230072969 + 3 ^ 40 * 924514 * 2
def baseEnd_924514 : Nat := 2604773957810156754037

theorem tailTrace_924514 : CollatzResearch.WordTrace tailWord_924514 prefixEnd_924514 2604773957810156754037 := by
  unfold tailWord_924514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8429948943162786816423149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22479863848434098177128397 8429948943162786816423149)
  ·
    refine ⟨3161230853686045056158681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8429948943162786816423149 3161230853686045056158681)
    ·
      refine ⟨2370923140264533792119011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3161230853686045056158681 2370923140264533792119011)
      ·
        refine ⟨3556384710396800688178517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2370923140264533792119011 3556384710396800688178517)
        ·
          refine ⟨2604773957810156754037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3556384710396800688178517 2604773957810156754037)
          ·
            rfl

theorem cell21_924514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 12].length) (baseStart_924514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924514 prefixEnd_924514 := by exact prefixLift 924514
  have htrace : WordTrace (prefixWord ++ tailWord_924514) baseStart_924514 baseEnd_924514 := by
    simpa [prefixWord, tailWord_924514, baseEnd_924514] using wordTrace_append hprefix tailTrace_924514
  have hstable : (prefixWord ++ tailWord_924514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924514).length < 2 ^ (prefixWord ++ tailWord_924514).sum := by decide
  have hdescent : baseEnd_924514 < baseStart_924514 := by decide
  rcases family_descends (prefixWord ++ tailWord_924514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924520 : List Nat := [2, 1, 4, 2, 1, 4, 2, 2, 3]
def baseStart_924520 : Nat := 118140960795 + 924520 * 2 ^ 59
def prefixEnd_924520 : Nat := 4983230072969 + 3 ^ 40 * 924520 * 2
def baseEnd_924520 : Nat := 210988059864368019976985

theorem tailTrace_924520 : CollatzResearch.WordTrace tailWord_924520 prefixEnd_924520 210988059864368019976985 := by
  unfold tailWord_924520
  simp only [CollatzResearch.WordTrace]
  refine ⟨16860007305314705145205507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22480009740419606860274009 16860007305314705145205507)
  ·
    refine ⟨25290010957972057717808261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16860007305314705145205507 25290010957972057717808261)
    ·
      refine ⟨4741877054619760822089049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25290010957972057717808261 4741877054619760822089049)
      ·
        refine ⟨3556407790964820616566787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4741877054619760822089049 3556407790964820616566787)
        ·
          refine ⟨5334611686447230924850181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3556407790964820616566787 5334611686447230924850181)
          ·
            refine ⟨1000239691208855798409409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5334611686447230924850181 1000239691208855798409409)
            ·
              refine ⟨750179768406641848807057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1000239691208855798409409 750179768406641848807057)
              ·
                refine ⟨562634826304981386605293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750179768406641848807057 562634826304981386605293)
                ·
                  refine ⟨210988059864368019976985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562634826304981386605293 210988059864368019976985)
                  ·
                    rfl

theorem cell21_924520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 3].length) (baseStart_924520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924520 prefixEnd_924520 := by exact prefixLift 924520
  have htrace : WordTrace (prefixWord ++ tailWord_924520) baseStart_924520 baseEnd_924520 := by
    simpa [prefixWord, tailWord_924520, baseEnd_924520] using wordTrace_append hprefix tailTrace_924520
  have hstable : (prefixWord ++ tailWord_924520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924520).length < 2 ^ (prefixWord ++ tailWord_924520).sum := by decide
  have hdescent : baseEnd_924520 < baseStart_924520 := by decide
  rcases family_descends (prefixWord ++ tailWord_924520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924576 : List Nat := [2, 1, 1, 4, 1, 1, 5, 2, 4]
def baseStart_924576 : Nat := 118140960795 + 924576 * 2 ^ 59
def prefixEnd_924576 : Nat := 4983230072969 + 3 ^ 40 * 924576 * 2
def baseEnd_924576 : Nat := 211000839827324367043537

theorem tailTrace_924576 : CollatzResearch.WordTrace tailWord_924576 prefixEnd_924576 211000839827324367043537 := by
  unfold tailWord_924576
  simp only [CollatzResearch.WordTrace]
  refine ⟨16861028549213265927224791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22481371398951021236299721 16861028549213265927224791)
  ·
    refine ⟨25291542823819898890837187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16861028549213265927224791 25291542823819898890837187)
    ·
      refine ⟨37937314235729848336255781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25291542823819898890837187 37937314235729848336255781)
      ·
        refine ⟨7113246419199346563047959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37937314235729848336255781 7113246419199346563047959)
        ·
          refine ⟨10669869628799019844571939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7113246419199346563047959 10669869628799019844571939)
          ·
            refine ⟨16004804443198529766857909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10669869628799019844571939 16004804443198529766857909)
            ·
              refine ⟨1500450416549862165642929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16004804443198529766857909 1500450416549862165642929)
              ·
                refine ⟨1125337812412396624232197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1500450416549862165642929 1125337812412396624232197)
                ·
                  refine ⟨211000839827324367043537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1125337812412396624232197 211000839827324367043537)
                  ·
                    rfl

theorem cell21_924576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_924576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924576 prefixEnd_924576 := by exact prefixLift 924576
  have htrace : WordTrace (prefixWord ++ tailWord_924576) baseStart_924576 baseEnd_924576 := by
    simpa [prefixWord, tailWord_924576, baseEnd_924576] using wordTrace_append hprefix tailTrace_924576
  have hstable : (prefixWord ++ tailWord_924576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924576).length < 2 ^ (prefixWord ++ tailWord_924576).sum := by decide
  have hdescent : baseEnd_924576 < baseStart_924576 := by decide
  rcases family_descends (prefixWord ++ tailWord_924576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924700 : List Nat := [2, 2, 3, 1, 5, 1, 1, 6]
def baseStart_924700 : Nat := 118140960795 + 924700 * 2 ^ 59
def prefixEnd_924700 : Nat := 4983230072969 + 3 ^ 40 * 924700 * 2
def baseEnd_924700 : Nat := 70343046105575902325539

theorem tailTrace_924700 : CollatzResearch.WordTrace tailWord_924700 prefixEnd_924700 70343046105575902325539 := by
  unfold tailWord_924700
  simp only [CollatzResearch.WordTrace]
  refine ⟨16863289874988650515981777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22484386499984867354642369 16863289874988650515981777)
  ·
    refine ⟨12647467406241487886986333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16863289874988650515981777 12647467406241487886986333)
    ·
      refine ⟨4742800277340557957619875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12647467406241487886986333 4742800277340557957619875)
      ·
        refine ⟨7114200416010836936429813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4742800277340557957619875 7114200416010836936429813)
        ·
          refine ⟨666956289001015962790295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7114200416010836936429813 666956289001015962790295)
          ·
            refine ⟨1000434433501523944185443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666956289001015962790295 1000434433501523944185443)
            ·
              refine ⟨1500651650252285916278165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000434433501523944185443 1500651650252285916278165)
              ·
                refine ⟨70343046105575902325539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1500651650252285916278165 70343046105575902325539)
                ·
                  rfl

theorem cell21_924700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 6].length) (baseStart_924700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924700 prefixEnd_924700 := by exact prefixLift 924700
  have htrace : WordTrace (prefixWord ++ tailWord_924700) baseStart_924700 baseEnd_924700 := by
    simpa [prefixWord, tailWord_924700, baseEnd_924700] using wordTrace_append hprefix tailTrace_924700
  have hstable : (prefixWord ++ tailWord_924700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924700).length < 2 ^ (prefixWord ++ tailWord_924700).sum := by decide
  have hdescent : baseEnd_924700 < baseStart_924700 := by decide
  rcases family_descends (prefixWord ++ tailWord_924700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924714 : List Nat := [3, 1, 4, 1, 3, 1, 1, 2, 5]
def baseStart_924714 : Nat := 118140960795 + 924714 * 2 ^ 59
def prefixEnd_924714 : Nat := 4983230072969 + 3 ^ 40 * 924714 * 2
def baseEnd_924714 : Nat := 211032333307466793743255

theorem tailTrace_924714 : CollatzResearch.WordTrace tailWord_924714 prefixEnd_924714 211032333307466793743255 := by
  unfold tailWord_924714
  simp only [CollatzResearch.WordTrace]
  refine ⟨8431772592981645355743299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22484726914617720948648797 8431772592981645355743299)
  ·
    refine ⟨12647658889472468033614949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8431772592981645355743299 12647658889472468033614949)
    ·
      refine ⟨2371436041776087756302803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12647658889472468033614949 2371436041776087756302803)
      ·
        refine ⟨3557154062664131634454205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2371436041776087756302803 3557154062664131634454205)
        ·
          refine ⟨1333932773499049362920327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3557154062664131634454205 1333932773499049362920327)
          ·
            refine ⟨2000899160248574044380491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1333932773499049362920327 2000899160248574044380491)
            ·
              refine ⟨3001348740372861066570737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2000899160248574044380491 3001348740372861066570737)
              ·
                refine ⟨2251011555279645799928053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3001348740372861066570737 2251011555279645799928053)
                ·
                  refine ⟨211032333307466793743255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2251011555279645799928053 211032333307466793743255)
                  ·
                    rfl

theorem cell21_924714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_924714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924714 prefixEnd_924714 := by exact prefixLift 924714
  have htrace : WordTrace (prefixWord ++ tailWord_924714) baseStart_924714 baseEnd_924714 := by
    simpa [prefixWord, tailWord_924714, baseEnd_924714] using wordTrace_append hprefix tailTrace_924714
  have hstable : (prefixWord ++ tailWord_924714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924714).length < 2 ^ (prefixWord ++ tailWord_924714).sum := by decide
  have hdescent : baseEnd_924714 < baseStart_924714 := by decide
  rcases family_descends (prefixWord ++ tailWord_924714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924818 : List Nat := [3, 2, 3, 1, 1, 2, 1, 8]
def baseStart_924818 : Nat := 118140960795 + 924818 * 2 ^ 59
def prefixEnd_924818 : Nat := 4983230072969 + 3 ^ 40 * 924818 * 2
def baseEnd_924818 : Nat := 70352022508128574669903

theorem tailTrace_924818 : CollatzResearch.WordTrace tailWord_924818 prefixEnd_924818 70352022508128574669903 := by
  unfold tailWord_924818
  simp only [CollatzResearch.WordTrace]
  refine ⟨8432720890887451796189777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22487255709033204789839405 8432720890887451796189777)
  ·
    refine ⟨6324540668165588847142333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8432720890887451796189777 6324540668165588847142333)
    ·
      refine ⟨2371702750562095817678375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6324540668165588847142333 2371702750562095817678375)
      ·
        refine ⟨3557554125843143726517563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2371702750562095817678375 3557554125843143726517563)
        ·
          refine ⟨5336331188764715589776345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3557554125843143726517563 5336331188764715589776345)
          ·
            refine ⟨4002248391573536692332259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5336331188764715589776345 4002248391573536692332259)
            ·
              refine ⟨6003372587360305038498389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4002248391573536692332259 6003372587360305038498389)
              ·
                refine ⟨70352022508128574669903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6003372587360305038498389 70352022508128574669903)
                ·
                  rfl

theorem cell21_924818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_924818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924818 prefixEnd_924818 := by exact prefixLift 924818
  have htrace : WordTrace (prefixWord ++ tailWord_924818) baseStart_924818 baseEnd_924818 := by
    simpa [prefixWord, tailWord_924818, baseEnd_924818] using wordTrace_append hprefix tailTrace_924818
  have hstable : (prefixWord ++ tailWord_924818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924818).length < 2 ^ (prefixWord ++ tailWord_924818).sum := by decide
  have hdescent : baseEnd_924818 < baseStart_924818 := by decide
  rcases family_descends (prefixWord ++ tailWord_924818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924832 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 7]
def baseStart_924832 : Nat := 118140960795 + 924832 * 2 ^ 59
def prefixEnd_924832 : Nat := 4983230072969 + 3 ^ 40 * 924832 * 2
def baseEnd_924832 : Nat := 211059262515124810776347

theorem tailTrace_924832 : CollatzResearch.WordTrace tailWord_924832 prefixEnd_924832 211059262515124810776347 := by
  unfold tailWord_924832
  simp only [CollatzResearch.WordTrace]
  refine ⟨16865697092749543787884375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22487596123666058383845833 16865697092749543787884375)
  ·
    refine ⟨25298545639124315681826563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16865697092749543787884375 25298545639124315681826563)
    ·
      refine ⟨37947818458686473522739845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25298545639124315681826563 37947818458686473522739845)
      ·
        refine ⟨7115215961003713785513721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37947818458686473522739845 7115215961003713785513721)
        ·
          refine ⟨5336411970752785339135291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7115215961003713785513721 5336411970752785339135291)
          ·
            refine ⟨8004617956129178008702937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5336411970752785339135291 8004617956129178008702937)
            ·
              refine ⟨6003463467096883506527203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8004617956129178008702937 6003463467096883506527203)
              ·
                refine ⟨9005195200645325259790805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6003463467096883506527203 9005195200645325259790805)
                ·
                  refine ⟨211059262515124810776347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9005195200645325259790805 211059262515124810776347)
                  ·
                    rfl

theorem cell21_924832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_924832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924832 prefixEnd_924832 := by exact prefixLift 924832
  have htrace : WordTrace (prefixWord ++ tailWord_924832) baseStart_924832 baseEnd_924832 := by
    simpa [prefixWord, tailWord_924832, baseEnd_924832] using wordTrace_append hprefix tailTrace_924832
  have hstable : (prefixWord ++ tailWord_924832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924832).length < 2 ^ (prefixWord ++ tailWord_924832).sum := by decide
  have hdescent : baseEnd_924832 < baseStart_924832 := by decide
  rcases family_descends (prefixWord ++ tailWord_924832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924863 : List Nat := [1, 1, 2, 2, 2, 2, 3, 4, 4]
def baseStart_924863 : Nat := 118140960795 + 924863 * 2 ^ 59
def prefixEnd_924863 : Nat := 4983230072969 + 3 ^ 40 * 924863 * 2
def baseEnd_924863 : Nat := 211066337137475645759617

theorem tailTrace_924863 : CollatzResearch.WordTrace tailWord_924863 prefixEnd_924863 211066337137475645759617 := by
  unfold tailWord_924863
  simp only [CollatzResearch.WordTrace]
  refine ⟨33732524848386779870147243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22488349898924519913431495 33732524848386779870147243)
  ·
    refine ⟨50598787272580169805220865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33732524848386779870147243 50598787272580169805220865)
    ·
      refine ⟨37949090454435127353915649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50598787272580169805220865 37949090454435127353915649)
      ·
        refine ⟨28461817840826345515436737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37949090454435127353915649 28461817840826345515436737)
        ·
          refine ⟨21346363380619759136577553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28461817840826345515436737 21346363380619759136577553)
          ·
            refine ⟨16009772535464819352433165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21346363380619759136577553 16009772535464819352433165)
            ·
              refine ⟨6003664700799307257162437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16009772535464819352433165 6003664700799307257162437)
              ·
                refine ⟨1125687131399870110717957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6003664700799307257162437 1125687131399870110717957)
                ·
                  refine ⟨211066337137475645759617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1125687131399870110717957 211066337137475645759617)
                  ·
                    rfl

theorem cell21_924863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 4].length) (baseStart_924863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924863 prefixEnd_924863 := by exact prefixLift 924863
  have htrace : WordTrace (prefixWord ++ tailWord_924863) baseStart_924863 baseEnd_924863 := by
    simpa [prefixWord, tailWord_924863, baseEnd_924863] using wordTrace_append hprefix tailTrace_924863
  have hstable : (prefixWord ++ tailWord_924863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924863).length < 2 ^ (prefixWord ++ tailWord_924863).sum := by decide
  have hdescent : baseEnd_924863 < baseStart_924863 := by decide
  rcases family_descends (prefixWord ++ tailWord_924863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924914 : List Nat := [3, 2, 1, 3, 4, 1, 1, 2, 4]
def baseStart_924914 : Nat := 118140960795 + 924914 * 2 ^ 59
def prefixEnd_924914 : Nat := 4983230072969 + 3 ^ 40 * 924914 * 2
def baseEnd_924914 : Nat := 211077976032310890409513

theorem tailTrace_924914 : CollatzResearch.WordTrace tailWord_924914 prefixEnd_924914 211077976032310890409513 := by
  unfold tailWord_924914
  simp only [CollatzResearch.WordTrace]
  refine ⟨8433596242800503895063449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22489589980801343720169197 8433596242800503895063449)
  ·
    refine ⟨6325197182100377921297587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8433596242800503895063449 6325197182100377921297587)
    ·
      refine ⟨9487795773150566881946381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6325197182100377921297587 9487795773150566881946381)
      ·
        refine ⟨3557923414931462580729893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9487795773150566881946381 3557923414931462580729893)
        ·
          refine ⟨667110640299649233886855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3557923414931462580729893 667110640299649233886855)
          ·
            refine ⟨1000665960449473850830283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667110640299649233886855 1000665960449473850830283)
            ·
              refine ⟨1500998940674210776245425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000665960449473850830283 1500998940674210776245425)
              ·
                refine ⟨1125749205505658082184069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1500998940674210776245425 1125749205505658082184069)
                ·
                  refine ⟨211077976032310890409513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1125749205505658082184069 211077976032310890409513)
                  ·
                    rfl

theorem cell21_924914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_924914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924914 prefixEnd_924914 := by exact prefixLift 924914
  have htrace : WordTrace (prefixWord ++ tailWord_924914) baseStart_924914 baseEnd_924914 := by
    simpa [prefixWord, tailWord_924914, baseEnd_924914] using wordTrace_append hprefix tailTrace_924914
  have hstable : (prefixWord ++ tailWord_924914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924914).length < 2 ^ (prefixWord ++ tailWord_924914).sum := by decide
  have hdescent : baseEnd_924914 < baseStart_924914 := by decide
  rcases family_descends (prefixWord ++ tailWord_924914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924959 : List Nat := [1, 1, 2, 4, 4, 2, 1, 3, 3]
def baseStart_924959 : Nat := 118140960795 + 924959 * 2 ^ 59
def prefixEnd_924959 : Nat := 4983230072969 + 3 ^ 40 * 924959 * 2
def baseEnd_924959 : Nat := 211088245645400812159421

theorem tailTrace_924959 : CollatzResearch.WordTrace tailWord_924959 prefixEnd_924959 211088245645400812159421 := by
  unfold tailWord_924959
  simp only [CollatzResearch.WordTrace]
  refine ⟨33736026256038988265641931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22490684170692658843761287 33736026256038988265641931)
  ·
    refine ⟨50604039384058482398462897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33736026256038988265641931 50604039384058482398462897)
    ·
      refine ⟨37953029538043861798847173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50604039384058482398462897 37953029538043861798847173)
      ·
        refine ⟨7116193038383224087283845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37953029538043861798847173 7116193038383224087283845)
        ·
          refine ⟨1334286194696854516365721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7116193038383224087283845 1334286194696854516365721)
          ·
            refine ⟨1000714646022640887274291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1334286194696854516365721 1000714646022640887274291)
            ·
              refine ⟨1501071969033961330911437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000714646022640887274291 1501071969033961330911437)
              ·
                refine ⟨562901988387735499091789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1501071969033961330911437 562901988387735499091789)
                ·
                  refine ⟨211088245645400812159421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562901988387735499091789 211088245645400812159421)
                  ·
                    rfl

theorem cell21_924959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 3].length) (baseStart_924959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924959 prefixEnd_924959 := by exact prefixLift 924959
  have htrace : WordTrace (prefixWord ++ tailWord_924959) baseStart_924959 baseEnd_924959 := by
    simpa [prefixWord, tailWord_924959, baseEnd_924959] using wordTrace_append hprefix tailTrace_924959
  have hstable : (prefixWord ++ tailWord_924959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924959).length < 2 ^ (prefixWord ++ tailWord_924959).sum := by decide
  have hdescent : baseEnd_924959 < baseStart_924959 := by decide
  rcases family_descends (prefixWord ++ tailWord_924959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924970 : List Nat := [3, 1, 4, 2, 1, 1, 9]
def baseStart_924970 : Nat := 118140960795 + 924970 * 2 ^ 59
def prefixEnd_924970 : Nat := 4983230072969 + 3 ^ 40 * 924970 * 2
def baseEnd_924970 : Nat := 23454528443918581941785

theorem tailTrace_924970 : CollatzResearch.WordTrace tailWord_924970 prefixEnd_924970 23454528443918581941785 := by
  unfold tailWord_924970
  simp only [CollatzResearch.WordTrace]
  refine ⟨8434106864749784286073091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22490951639332758096194909 8434106864749784286073091)
  ·
    refine ⟨12651160297124676429109637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8434106864749784286073091 12651160297124676429109637)
    ·
      refine ⟨2372092555710876830458057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12651160297124676429109637 2372092555710876830458057)
      ·
        refine ⟨1779069416783157622843543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2372092555710876830458057 1779069416783157622843543)
        ·
          refine ⟨2668604125174736434265315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1779069416783157622843543 2668604125174736434265315)
          ·
            refine ⟨4002906187762104651397973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2668604125174736434265315 4002906187762104651397973)
            ·
              refine ⟨23454528443918581941785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4002906187762104651397973 23454528443918581941785)
              ·
                rfl

theorem cell21_924970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 9].length) (baseStart_924970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_924970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_924970 prefixEnd_924970 := by exact prefixLift 924970
  have htrace : WordTrace (prefixWord ++ tailWord_924970) baseStart_924970 baseEnd_924970 := by
    simpa [prefixWord, tailWord_924970, baseEnd_924970] using wordTrace_append hprefix tailTrace_924970
  have hstable : (prefixWord ++ tailWord_924970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924970).length < 2 ^ (prefixWord ++ tailWord_924970).sum := by decide
  have hdescent : baseEnd_924970 < baseStart_924970 := by decide
  rcases family_descends (prefixWord ++ tailWord_924970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925060 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 7]
def baseStart_925060 : Nat := 118140960795 + 925060 * 2 ^ 59
def prefixEnd_925060 : Nat := 4983230072969 + 3 ^ 40 * 925060 * 2
def baseEnd_925060 : Nat := 211111295221447080975881

theorem tailTrace_925060 : CollatzResearch.WordTrace tailWord_925060 prefixEnd_925060 211111295221447080975881 := by
  unfold tailWord_925060
  simp only [CollatzResearch.WordTrace]
  refine ⟨16869855014336541257534317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22493140019115388343379089 16869855014336541257534317)
  ·
    refine ⟨6326195630376202971575369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16869855014336541257534317 6326195630376202971575369)
    ·
      refine ⟨4744646722782152228681527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6326195630376202971575369 4744646722782152228681527)
      ·
        refine ⟨7116970084173228343022291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4744646722782152228681527 7116970084173228343022291)
        ·
          refine ⟨10675455126259842514533437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7116970084173228343022291 10675455126259842514533437)
          ·
            refine ⟨4003295672347440942950039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10675455126259842514533437 4003295672347440942950039)
            ·
              refine ⟨6004943508521161414425059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4003295672347440942950039 6004943508521161414425059)
              ·
                refine ⟨9007415262781742121637589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6004943508521161414425059 9007415262781742121637589)
                ·
                  refine ⟨211111295221447080975881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9007415262781742121637589 211111295221447080975881)
                  ·
                    rfl

theorem cell21_925060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_925060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925060 prefixEnd_925060 := by exact prefixLift 925060
  have htrace : WordTrace (prefixWord ++ tailWord_925060) baseStart_925060 baseEnd_925060 := by
    simpa [prefixWord, tailWord_925060, baseEnd_925060] using wordTrace_append hprefix tailTrace_925060
  have hstable : (prefixWord ++ tailWord_925060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925060).length < 2 ^ (prefixWord ++ tailWord_925060).sum := by decide
  have hdescent : baseEnd_925060 < baseStart_925060 := by decide
  rcases family_descends (prefixWord ++ tailWord_925060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925077 : List Nat := [1, 3, 2, 1, 1, 2, 3, 5, 3]
def baseStart_925077 : Nat := 118140960795 + 925077 * 2 ^ 59
def prefixEnd_925077 : Nat := 4983230072969 + 3 ^ 40 * 925077 * 2
def baseEnd_925077 : Nat := 211115174853058829192513

theorem tailTrace_925077 : CollatzResearch.WordTrace tailWord_925077 prefixEnd_925077 211115174853058829192513 := by
  unfold tailWord_925077
  simp only [CollatzResearch.WordTrace]
  refine ⟨33740330069611494418437485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22493553379740996278958323 33740330069611494418437485)
  ·
    refine ⟨12652623776104310406914057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33740330069611494418437485 12652623776104310406914057)
    ·
      refine ⟨9489467832078232805185543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12652623776104310406914057 9489467832078232805185543)
      ·
        refine ⟨14234201748117349207778315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9489467832078232805185543 14234201748117349207778315)
        ·
          refine ⟨21351302622176023811667473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14234201748117349207778315 21351302622176023811667473)
          ·
            refine ⟨16013476966632017858750605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21351302622176023811667473 16013476966632017858750605)
            ·
              refine ⟨6005053862487006697031477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16013476966632017858750605 6005053862487006697031477)
              ·
                refine ⟨562973799608156877846701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6005053862487006697031477 562973799608156877846701)
                ·
                  refine ⟨211115174853058829192513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 562973799608156877846701 211115174853058829192513)
                  ·
                    rfl

theorem cell21_925077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_925077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925077 prefixEnd_925077 := by exact prefixLift 925077
  have htrace : WordTrace (prefixWord ++ tailWord_925077) baseStart_925077 baseEnd_925077 := by
    simpa [prefixWord, tailWord_925077, baseEnd_925077] using wordTrace_append hprefix tailTrace_925077
  have hstable : (prefixWord ++ tailWord_925077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925077).length < 2 ^ (prefixWord ++ tailWord_925077).sum := by decide
  have hdescent : baseEnd_925077 < baseStart_925077 := by decide
  rcases family_descends (prefixWord ++ tailWord_925077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925105 : List Nat := [1, 2, 2, 4, 1, 1, 2, 8]
def baseStart_925105 : Nat := 118140960795 + 925105 * 2 ^ 59
def prefixEnd_925105 : Nat := 4983230072969 + 3 ^ 40 * 925105 * 2
def baseEnd_925105 : Nat := 70373854944845667575263

theorem tailTrace_925105 : CollatzResearch.WordTrace tailWord_925105 prefixEnd_925105 70373854944845667575263 := by
  unfold tailWord_925105
  simp only [CollatzResearch.WordTrace]
  refine ⟨33741351313510055200456769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22494234209006703466971179 33741351313510055200456769)
  ·
    refine ⟨25306013485132541400342577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33741351313510055200456769 25306013485132541400342577)
    ·
      refine ⟨18979510113849406050256933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25306013485132541400342577 18979510113849406050256933)
      ·
        refine ⟨3558658146346763634423175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18979510113849406050256933 3558658146346763634423175)
        ·
          refine ⟨5337987219520145451634763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3558658146346763634423175 5337987219520145451634763)
          ·
            refine ⟨8006980829280218177452145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5337987219520145451634763 8006980829280218177452145)
            ·
              refine ⟨6005235621960163633089109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8006980829280218177452145 6005235621960163633089109)
              ·
                refine ⟨70373854944845667575263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6005235621960163633089109 70373854944845667575263)
                ·
                  rfl

theorem cell21_925105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 8].length) (baseStart_925105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925105 prefixEnd_925105 := by exact prefixLift 925105
  have htrace : WordTrace (prefixWord ++ tailWord_925105) baseStart_925105 baseEnd_925105 := by
    simpa [prefixWord, tailWord_925105, baseEnd_925105] using wordTrace_append hprefix tailTrace_925105
  have hstable : (prefixWord ++ tailWord_925105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925105).length < 2 ^ (prefixWord ++ tailWord_925105).sum := by decide
  have hdescent : baseEnd_925105 < baseStart_925105 := by decide
  rcases family_descends (prefixWord ++ tailWord_925105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925153 : List Nat := [1, 2, 3, 1, 2, 5, 1, 1, 5]
def baseStart_925153 : Nat := 118140960795 + 925153 * 2 ^ 59
def prefixEnd_925153 : Nat := 4983230072969 + 3 ^ 40 * 925153 * 2
def baseEnd_925153 : Nat := 211132519088499585925691

theorem tailTrace_925153 : CollatzResearch.WordTrace tailWord_925153 prefixEnd_925153 211132519088499585925691 := by
  unfold tailWord_925153
  simp only [CollatzResearch.WordTrace]
  refine ⟨33743102017336159398204113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22495401344890772932136075 33743102017336159398204113)
  ·
    refine ⟨25307326513002119548653085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33743102017336159398204113 25307326513002119548653085)
    ·
      refine ⟨9490247442375794830744907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25307326513002119548653085 9490247442375794830744907)
      ·
        refine ⟨14235371163563692246117361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9490247442375794830744907 14235371163563692246117361)
        ·
          refine ⟨10676528372672769184588021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14235371163563692246117361 10676528372672769184588021)
          ·
            refine ⟨1000924534938072111055127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10676528372672769184588021 1000924534938072111055127)
            ·
              refine ⟨1501386802407108166582691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000924534938072111055127 1501386802407108166582691)
              ·
                refine ⟨2252080203610662249874037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1501386802407108166582691 2252080203610662249874037)
                ·
                  refine ⟨211132519088499585925691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2252080203610662249874037 211132519088499585925691)
                  ·
                    rfl

theorem cell21_925153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 5].length) (baseStart_925153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925153 prefixEnd_925153 := by exact prefixLift 925153
  have htrace : WordTrace (prefixWord ++ tailWord_925153) baseStart_925153 baseEnd_925153 := by
    simpa [prefixWord, tailWord_925153, baseEnd_925153] using wordTrace_append hprefix tailTrace_925153
  have hstable : (prefixWord ++ tailWord_925153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925153).length < 2 ^ (prefixWord ++ tailWord_925153).sum := by decide
  have hdescent : baseEnd_925153 < baseStart_925153 := by decide
  rcases family_descends (prefixWord ++ tailWord_925153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925181 : List Nat := [1, 4, 1, 1, 1, 4, 2, 7]
def baseStart_925181 : Nat := 118140960795 + 925181 * 2 ^ 59
def prefixEnd_925181 : Nat := 4983230072969 + 3 ^ 40 * 925181 * 2
def baseEnd_925181 : Nat := 70379636356659253152989

theorem tailTrace_925181 : CollatzResearch.WordTrace tailWord_925181 prefixEnd_925181 70379636356659253152989 := by
  unfold tailWord_925181
  simp only [CollatzResearch.WordTrace]
  refine ⟨33744123261234720180223397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22496082174156480120148931 33744123261234720180223397)
  ·
    refine ⟨6327023111481510033791887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33744123261234720180223397 6327023111481510033791887)
    ·
      refine ⟨9490534667222265050687831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6327023111481510033791887 9490534667222265050687831)
      ·
        refine ⟨14235802000833397576031747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9490534667222265050687831 14235802000833397576031747)
        ·
          refine ⟨21353703001250096364047621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14235802000833397576031747 21353703001250096364047621)
          ·
            refine ⟨4003819312734393068258929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21353703001250096364047621 4003819312734393068258929)
            ·
              refine ⟨3002864484550794801194197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4003819312734393068258929 3002864484550794801194197)
              ·
                refine ⟨70379636356659253152989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3002864484550794801194197 70379636356659253152989)
                ·
                  rfl

theorem cell21_925181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 7].length) (baseStart_925181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925181 prefixEnd_925181 := by exact prefixLift 925181
  have htrace : WordTrace (prefixWord ++ tailWord_925181) baseStart_925181 baseEnd_925181 := by
    simpa [prefixWord, tailWord_925181, baseEnd_925181] using wordTrace_append hprefix tailTrace_925181
  have hstable : (prefixWord ++ tailWord_925181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925181).length < 2 ^ (prefixWord ++ tailWord_925181).sum := by decide
  have hdescent : baseEnd_925181 < baseStart_925181 := by decide
  rcases family_descends (prefixWord ++ tailWord_925181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925198 : List Nat := [4, 1, 1, 2, 5, 8]
def baseStart_925198 : Nat := 118140960795 + 925198 * 2 ^ 59
def prefixEnd_925198 : Nat := 4983230072969 + 3 ^ 40 * 925198 * 2
def baseEnd_925198 : Nat := 7820103285244055839837

theorem tailTrace_925198 : CollatzResearch.WordTrace tailWord_925198 prefixEnd_925198 7820103285244055839837 := by
  unfold tailWord_925198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4218092912771641510449031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22496495534782088055728165 4218092912771641510449031)
  ·
    refine ⟨6327139369157462265673547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4218092912771641510449031 6327139369157462265673547)
    ·
      refine ⟨9490709053736193398510321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6327139369157462265673547 9490709053736193398510321)
      ·
        refine ⟨7118031790302145048882741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9490709053736193398510321 7118031790302145048882741)
        ·
          refine ⟨667315480340826098332757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7118031790302145048882741 667315480340826098332757)
          ·
            refine ⟨7820103285244055839837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 667315480340826098332757 7820103285244055839837)
            ·
              rfl

theorem cell21_925198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 8].length) (baseStart_925198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925198 prefixEnd_925198 := by exact prefixLift 925198
  have htrace : WordTrace (prefixWord ++ tailWord_925198) baseStart_925198 baseEnd_925198 := by
    simpa [prefixWord, tailWord_925198, baseEnd_925198] using wordTrace_append hprefix tailTrace_925198
  have hstable : (prefixWord ++ tailWord_925198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925198).length < 2 ^ (prefixWord ++ tailWord_925198).sum := by decide
  have hdescent : baseEnd_925198 < baseStart_925198 := by decide
  rcases family_descends (prefixWord ++ tailWord_925198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925212 : List Nat := [2, 2, 3, 1, 2, 1, 2, 3, 5]
def baseStart_925212 : Nat := 118140960795 + 925212 * 2 ^ 59
def prefixEnd_925212 : Nat := 4983230072969 + 3 ^ 40 * 925212 * 2
def baseEnd_925212 : Nat := 211145983692328594442237

theorem tailTrace_925212 : CollatzResearch.WordTrace tailWord_925212 prefixEnd_925212 211145983692328594442237 := by
  unfold tailWord_925212
  simp only [CollatzResearch.WordTrace]
  refine ⟨16872626962061206237300945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22496835949414941649734593 16872626962061206237300945)
  ·
    refine ⟨12654470221545904677975709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16872626962061206237300945 12654470221545904677975709)
    ·
      refine ⟨4745426333079714254240891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12654470221545904677975709 4745426333079714254240891)
      ·
        refine ⟨7118139499619571381361337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4745426333079714254240891 7118139499619571381361337)
        ·
          refine ⟨5338604624714678536021003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7118139499619571381361337 5338604624714678536021003)
          ·
            refine ⟨8007906937072017804031505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5338604624714678536021003 8007906937072017804031505)
            ·
              refine ⟨6005930202804013353023629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8007906937072017804031505 6005930202804013353023629)
              ·
                refine ⟨2252223826051505007383861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6005930202804013353023629 2252223826051505007383861)
                ·
                  refine ⟨211145983692328594442237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2252223826051505007383861 211145983692328594442237)
                  ·
                    rfl

theorem cell21_925212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_925212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925212 prefixEnd_925212 := by exact prefixLift 925212
  have htrace : WordTrace (prefixWord ++ tailWord_925212) baseStart_925212 baseEnd_925212 := by
    simpa [prefixWord, tailWord_925212, baseEnd_925212] using wordTrace_append hprefix tailTrace_925212
  have hstable : (prefixWord ++ tailWord_925212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925212).length < 2 ^ (prefixWord ++ tailWord_925212).sum := by decide
  have hdescent : baseEnd_925212 < baseStart_925212 := by decide
  rcases family_descends (prefixWord ++ tailWord_925212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925260 : List Nat := [2, 2, 1, 3, 1, 5, 1, 2, 4]
def baseStart_925260 : Nat := 118140960795 + 925260 * 2 ^ 59
def prefixEnd_925260 : Nat := 4983230072969 + 3 ^ 40 * 925260 * 2
def baseEnd_925260 : Nat := 211156937946291177642139

theorem tailTrace_925260 : CollatzResearch.WordTrace tailWord_925260 prefixEnd_925260 211156937946291177642139 := by
  unfold tailWord_925260
  simp only [CollatzResearch.WordTrace]
  refine ⟨16873502313974258336174617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22498003085299011114899489 16873502313974258336174617)
  ·
    refine ⟨12655126735480693752130963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16873502313974258336174617 12655126735480693752130963)
    ·
      refine ⟨18982690103221040628196445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12655126735480693752130963 18982690103221040628196445)
      ·
        refine ⟨7118508788707890235573667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18982690103221040628196445 7118508788707890235573667)
        ·
          refine ⟨10677763183061835353360501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7118508788707890235573667 10677763183061835353360501)
          ·
            refine ⟨1001040298412047064377547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10677763183061835353360501 1001040298412047064377547)
            ·
              refine ⟨1501560447618070596566321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001040298412047064377547 1501560447618070596566321)
              ·
                refine ⟨1126170335713552947424741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1501560447618070596566321 1126170335713552947424741)
                ·
                  refine ⟨211156937946291177642139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1126170335713552947424741 211156937946291177642139)
                  ·
                    rfl

theorem cell21_925260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_925260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925260 prefixEnd_925260 := by exact prefixLift 925260
  have htrace : WordTrace (prefixWord ++ tailWord_925260) baseStart_925260 baseEnd_925260 := by
    simpa [prefixWord, tailWord_925260, baseEnd_925260] using wordTrace_append hprefix tailTrace_925260
  have hstable : (prefixWord ++ tailWord_925260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925260).length < 2 ^ (prefixWord ++ tailWord_925260).sum := by decide
  have hdescent : baseEnd_925260 < baseStart_925260 := by decide
  rcases family_descends (prefixWord ++ tailWord_925260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925336 : List Nat := [2, 1, 2, 4, 1, 2, 4, 1, 4]
def baseStart_925336 : Nat := 118140960795 + 925336 * 2 ^ 59
def prefixEnd_925336 : Nat := 4983230072969 + 3 ^ 40 * 925336 * 2
def baseEnd_925336 : Nat := 211174282181731934375317

theorem tailTrace_925336 : CollatzResearch.WordTrace tailWord_925336 prefixEnd_925336 211174282181731934375317 := by
  unfold tailWord_925336
  simp only [CollatzResearch.WordTrace]
  refine ⟨16874888287836590826057931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22499851050448787768077241 16874888287836590826057931)
  ·
    refine ⟨25312332431754886239086897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16874888287836590826057931 25312332431754886239086897)
    ·
      refine ⟨18984249323816164679315173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25312332431754886239086897 18984249323816164679315173)
      ·
        refine ⟨3559546748215530877371595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18984249323816164679315173 3559546748215530877371595)
        ·
          refine ⟨5339320122323296316057393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3559546748215530877371595 5339320122323296316057393)
          ·
            refine ⟨4004490091742472237043045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5339320122323296316057393 4004490091742472237043045)
            ·
              refine ⟨750841892201713544445571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4004490091742472237043045 750841892201713544445571)
              ·
                refine ⟨1126262838302570316668357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750841892201713544445571 1126262838302570316668357)
                ·
                  refine ⟨211174282181731934375317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1126262838302570316668357 211174282181731934375317)
                  ·
                    rfl

theorem cell21_925336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 4].length) (baseStart_925336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925336 prefixEnd_925336 := by exact prefixLift 925336
  have htrace : WordTrace (prefixWord ++ tailWord_925336) baseStart_925336 baseEnd_925336 := by
    simpa [prefixWord, tailWord_925336, baseEnd_925336] using wordTrace_append hprefix tailTrace_925336
  have hstable : (prefixWord ++ tailWord_925336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925336).length < 2 ^ (prefixWord ++ tailWord_925336).sum := by decide
  have hdescent : baseEnd_925336 < baseStart_925336 := by decide
  rcases family_descends (prefixWord ++ tailWord_925336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925347 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 7]
def baseStart_925347 : Nat := 118140960795 + 925347 * 2 ^ 59
def prefixEnd_925347 : Nat := 4983230072969 + 3 ^ 40 * 925347 * 2
def baseEnd_925347 : Nat := 211176792531598359691961

theorem tailTrace_925347 : CollatzResearch.WordTrace tailWord_925347 prefixEnd_925347 211176792531598359691961 := by
  unfold tailWord_925347
  simp only [CollatzResearch.WordTrace]
  refine ⟨33750177778633330530766295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22500118519088887020510863 33750177778633330530766295)
  ·
    refine ⟨50625266667949995796149443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33750177778633330530766295 50625266667949995796149443)
    ·
      refine ⟨75937900001924993694224165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50625266667949995796149443 75937900001924993694224165)
      ·
        refine ⟨14238356250360936317667031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75937900001924993694224165 14238356250360936317667031)
        ·
          refine ⟨21357534375541404476500547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14238356250360936317667031 21357534375541404476500547)
          ·
            refine ⟨32036301563312106714750821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21357534375541404476500547 32036301563312106714750821)
            ·
              refine ⟨6006806543121020009015779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32036301563312106714750821 6006806543121020009015779)
              ·
                refine ⟨9010209814681530013523669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6006806543121020009015779 9010209814681530013523669)
                ·
                  refine ⟨211176792531598359691961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9010209814681530013523669 211176792531598359691961)
                  ·
                    rfl

theorem cell21_925347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 7].length) (baseStart_925347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925347 prefixEnd_925347 := by exact prefixLift 925347
  have htrace : WordTrace (prefixWord ++ tailWord_925347) baseStart_925347 baseEnd_925347 := by
    simpa [prefixWord, tailWord_925347, baseEnd_925347] using wordTrace_append hprefix tailTrace_925347
  have hstable : (prefixWord ++ tailWord_925347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925347).length < 2 ^ (prefixWord ++ tailWord_925347).sum := by decide
  have hdescent : baseEnd_925347 < baseStart_925347 := by decide
  rcases family_descends (prefixWord ++ tailWord_925347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925392 : List Nat := [2, 1, 1, 1, 1, 2, 1, 12]
def baseStart_925392 : Nat := 118140960795 + 925392 * 2 ^ 59
def prefixEnd_925392 : Nat := 4983230072969 + 3 ^ 40 * 925392 * 2
def baseEnd_925392 : Nat := 70395687381562760480623

theorem tailTrace_925392 : CollatzResearch.WordTrace tailWord_925392 prefixEnd_925392 70395687381562760480623 := by
  unfold tailWord_925392
  simp only [CollatzResearch.WordTrace]
  refine ⟨16875909531735151608077215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22501212708980202144102953 16875909531735151608077215)
  ·
    refine ⟨25313864297602727412115823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16875909531735151608077215 25313864297602727412115823)
    ·
      refine ⟨37970796446404091118173735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25313864297602727412115823 37970796446404091118173735)
      ·
        refine ⟨56956194669606136677260603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37970796446404091118173735 56956194669606136677260603)
        ·
          refine ⟨85434292004409205015890905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56956194669606136677260603 85434292004409205015890905)
          ·
            refine ⟨64075719003306903761918179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85434292004409205015890905 64075719003306903761918179)
            ·
              refine ⟨96113578504960355642877269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64075719003306903761918179 96113578504960355642877269)
              ·
                refine ⟨70395687381562760480623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 96113578504960355642877269 70395687381562760480623)
                ·
                  rfl

theorem cell21_925392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 12].length) (baseStart_925392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925392 prefixEnd_925392 := by exact prefixLift 925392
  have htrace : WordTrace (prefixWord ++ tailWord_925392) baseStart_925392 baseEnd_925392 := by
    simpa [prefixWord, tailWord_925392, baseEnd_925392] using wordTrace_append hprefix tailTrace_925392
  have hstable : (prefixWord ++ tailWord_925392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925392).length < 2 ^ (prefixWord ++ tailWord_925392).sum := by decide
  have hdescent : baseEnd_925392 < baseStart_925392 := by decide
  rcases family_descends (prefixWord ++ tailWord_925392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925415 : List Nat := [1, 1, 5, 4, 1, 1, 2, 3, 3]
def baseStart_925415 : Nat := 118140960795 + 925415 * 2 ^ 59
def prefixEnd_925415 : Nat := 4983230072969 + 3 ^ 40 * 925415 * 2
def baseEnd_925415 : Nat := 211192311058045352558489

theorem tailTrace_925415 : CollatzResearch.WordTrace tailWord_925415 prefixEnd_925415 211192311058045352558489 := by
  unfold tailWord_925415
  simp only [CollatzResearch.WordTrace]
  refine ⟨33752657942386978144241699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22501771961591318762827799 33752657942386978144241699)
  ·
    refine ⟨50628986913580467216362549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33752657942386978144241699 50628986913580467216362549)
    ·
      refine ⟨4746467523148168801533989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50628986913580467216362549 4746467523148168801533989)
      ·
        refine ⟨889962660590281650287623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4746467523148168801533989 889962660590281650287623)
        ·
          refine ⟨1334943990885422475431435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 889962660590281650287623 1334943990885422475431435)
          ·
            refine ⟨2002415986328133713147153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334943990885422475431435 2002415986328133713147153)
            ·
              refine ⟨1501811989746100284860365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2002415986328133713147153 1501811989746100284860365)
              ·
                refine ⟨563179496154787606822637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1501811989746100284860365 563179496154787606822637)
                ·
                  refine ⟨211192311058045352558489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 563179496154787606822637 211192311058045352558489)
                  ·
                    rfl

theorem cell21_925415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 3].length) (baseStart_925415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925415 prefixEnd_925415 := by exact prefixLift 925415
  have htrace : WordTrace (prefixWord ++ tailWord_925415) baseStart_925415 baseEnd_925415 := by
    simpa [prefixWord, tailWord_925415, baseEnd_925415] using wordTrace_append hprefix tailTrace_925415
  have hstable : (prefixWord ++ tailWord_925415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925415).length < 2 ^ (prefixWord ++ tailWord_925415).sum := by decide
  have hdescent : baseEnd_925415 < baseStart_925415 := by decide
  rcases family_descends (prefixWord ++ tailWord_925415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925423 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 7]
def baseStart_925423 : Nat := 118140960795 + 925423 * 2 ^ 59
def prefixEnd_925423 : Nat := 4983230072969 + 3 ^ 40 * 925423 * 2
def baseEnd_925423 : Nat := 211194136767039116425139

theorem tailTrace_925423 : CollatzResearch.WordTrace tailWord_925423 prefixEnd_925423 211194136767039116425139 := by
  unfold tailWord_925423
  simp only [CollatzResearch.WordTrace]
  refine ⟨33752949726357995510532923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22501966484238663673688615 33752949726357995510532923)
  ·
    refine ⟨50629424589536993265799385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33752949726357995510532923 50629424589536993265799385)
    ·
      refine ⟨37972068442152744949349539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50629424589536993265799385 37972068442152744949349539)
      ·
        refine ⟨56958102663229117424024309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37972068442152744949349539 56958102663229117424024309)
        ·
          refine ⟨5339822124677729758502279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56958102663229117424024309 5339822124677729758502279)
          ·
            refine ⟨8009733187016594637753419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5339822124677729758502279 8009733187016594637753419)
            ·
              refine ⟨12014599780524891956630129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8009733187016594637753419 12014599780524891956630129)
              ·
                refine ⟨9010949835393668967472597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12014599780524891956630129 9010949835393668967472597)
                ·
                  refine ⟨211194136767039116425139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9010949835393668967472597 211194136767039116425139)
                  ·
                    rfl

theorem cell21_925423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 7].length) (baseStart_925423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925423 prefixEnd_925423 := by exact prefixLift 925423
  have htrace : WordTrace (prefixWord ++ tailWord_925423) baseStart_925423 baseEnd_925423 := by
    simpa [prefixWord, tailWord_925423, baseEnd_925423] using wordTrace_append hprefix tailTrace_925423
  have hstable : (prefixWord ++ tailWord_925423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925423).length < 2 ^ (prefixWord ++ tailWord_925423).sum := by decide
  have hdescent : baseEnd_925423 < baseStart_925423 := by decide
  rcases family_descends (prefixWord ++ tailWord_925423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925460 : List Nat := [2, 4, 4, 1, 1, 1, 1, 7]
def baseStart_925460 : Nat := 118140960795 + 925460 * 2 ^ 59
def prefixEnd_925460 : Nat := 4983230072969 + 3 ^ 40 * 925460 * 2
def baseEnd_925460 : Nat := 70400860223711758102799

theorem tailTrace_925460 : CollatzResearch.WordTrace tailWord_925460 prefixEnd_925460 70400860223711758102799 := by
  unfold tailWord_925460
  simp only [CollatzResearch.WordTrace]
  refine ⟨16877149613611975414814917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22502866151482633886419889 16877149613611975414814917)
  ·
    refine ⟨3164465552552245390277797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16877149613611975414814917 3164465552552245390277797)
    ·
      refine ⟨593337291103546010677087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3164465552552245390277797 593337291103546010677087)
      ·
        refine ⟨890005936655319016015631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593337291103546010677087 890005936655319016015631)
        ·
          refine ⟨1335008904982978524023447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890005936655319016015631 1335008904982978524023447)
          ·
            refine ⟨2002513357474467786035171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335008904982978524023447 2002513357474467786035171)
            ·
              refine ⟨3003770036211701679052757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2002513357474467786035171 3003770036211701679052757)
              ·
                refine ⟨70400860223711758102799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3003770036211701679052757 70400860223711758102799)
                ·
                  rfl

theorem cell21_925460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 7].length) (baseStart_925460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925460 prefixEnd_925460 := by exact prefixLift 925460
  have htrace : WordTrace (prefixWord ++ tailWord_925460) baseStart_925460 baseEnd_925460 := by
    simpa [prefixWord, tailWord_925460, baseEnd_925460] using wordTrace_append hprefix tailTrace_925460
  have hstable : (prefixWord ++ tailWord_925460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925460).length < 2 ^ (prefixWord ++ tailWord_925460).sum := by decide
  have hdescent : baseEnd_925460 < baseStart_925460 := by decide
  rcases family_descends (prefixWord ++ tailWord_925460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925502 : List Nat := [4, 2, 1, 2, 2, 2, 2, 6]
def baseStart_925502 : Nat := 118140960795 + 925502 * 2 ^ 59
def prefixEnd_925502 : Nat := 4983230072969 + 3 ^ 40 * 925502 * 2
def baseEnd_925502 : Nat := 70404055214450844869437

theorem tailTrace_925502 : CollatzResearch.WordTrace tailWord_925502 prefixEnd_925502 70404055214450844869437 := by
  unfold tailWord_925502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4219478886633974000332345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22503887395381194668439173 4219478886633974000332345)
  ·
    refine ⟨3164609164975480500249259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4219478886633974000332345 3164609164975480500249259)
    ·
      refine ⟨4746913747463220750373889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3164609164975480500249259 4746913747463220750373889)
      ·
        refine ⟨3560185310597415562780417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4746913747463220750373889 3560185310597415562780417)
        ·
          refine ⟨2670138982948061672085313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3560185310597415562780417 2670138982948061672085313)
          ·
            refine ⟨2002604237211046254063985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2670138982948061672085313 2002604237211046254063985)
            ·
              refine ⟨1501953177908284690547989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2002604237211046254063985 1501953177908284690547989)
              ·
                refine ⟨70404055214450844869437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1501953177908284690547989 70404055214450844869437)
                ·
                  rfl

theorem cell21_925502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_925502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925502 prefixEnd_925502 := by exact prefixLift 925502
  have htrace : WordTrace (prefixWord ++ tailWord_925502) baseStart_925502 baseEnd_925502 := by
    simpa [prefixWord, tailWord_925502, baseEnd_925502] using wordTrace_append hprefix tailTrace_925502
  have hstable : (prefixWord ++ tailWord_925502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925502).length < 2 ^ (prefixWord ++ tailWord_925502).sum := by decide
  have hdescent : baseEnd_925502 < baseStart_925502 := by decide
  rcases family_descends (prefixWord ++ tailWord_925502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925550 : List Nat := [4, 1, 2, 3, 1, 2, 1, 4, 3]
def baseStart_925550 : Nat := 118140960795 + 925550 * 2 ^ 59
def prefixEnd_925550 : Nat := 4983230072969 + 3 ^ 40 * 925550 * 2
def baseEnd_925550 : Nat := 211223119897315117808213

theorem tailTrace_925550 : CollatzResearch.WordTrace tailWord_925550 prefixEnd_925550 211223119897315117808213 := by
  unfold tailWord_925550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4219697724612237025050763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22505054531265264133604069 4219697724612237025050763)
  ·
    refine ⟨6329546586918355537576145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4219697724612237025050763 6329546586918355537576145)
    ·
      refine ⟨4747159940188766653182109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6329546586918355537576145 4747159940188766653182109)
      ·
        refine ⟨1780184977570787494943291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4747159940188766653182109 1780184977570787494943291)
        ·
          refine ⟨2670277466356181242414937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1780184977570787494943291 2670277466356181242414937)
          ·
            refine ⟨2002708099767135931811203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2670277466356181242414937 2002708099767135931811203)
            ·
              refine ⟨3004062149650703897716805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2002708099767135931811203 3004062149650703897716805)
              ·
                refine ⟨563261653059506980821901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3004062149650703897716805 563261653059506980821901)
                ·
                  refine ⟨211223119897315117808213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 563261653059506980821901 211223119897315117808213)
                  ·
                    rfl

theorem cell21_925550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_925550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925550 prefixEnd_925550 := by exact prefixLift 925550
  have htrace : WordTrace (prefixWord ++ tailWord_925550) baseStart_925550 baseEnd_925550 := by
    simpa [prefixWord, tailWord_925550, baseEnd_925550] using wordTrace_append hprefix tailTrace_925550
  have hstable : (prefixWord ++ tailWord_925550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925550).length < 2 ^ (prefixWord ++ tailWord_925550).sum := by decide
  have hdescent : baseEnd_925550 < baseStart_925550 := by decide
  rcases family_descends (prefixWord ++ tailWord_925550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925598 : List Nat := [4, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_925598 : Nat := 118140960795 + 925598 * 2 ^ 59
def prefixEnd_925598 : Nat := 4983230072969 + 3 ^ 40 * 925598 * 2
def baseEnd_925598 : Nat := 211234074151277701008115

theorem tailTrace_925598 : CollatzResearch.WordTrace tailWord_925598 prefixEnd_925598 211234074151277701008115 := by
  unfold tailWord_925598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4219916562590500049769181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22506221667149333598768965 4219916562590500049769181)
  ·
    refine ⟨1582468710971437518663443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4219916562590500049769181 1582468710971437518663443)
    ·
      refine ⟨2373703066457156277995165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1582468710971437518663443 2373703066457156277995165)
      ·
        refine ⟨890138649921433604248187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2373703066457156277995165 890138649921433604248187)
        ·
          refine ⟨1335207974882150406372281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890138649921433604248187 1335207974882150406372281)
          ·
            refine ⟨1001405981161612804779211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1335207974882150406372281 1001405981161612804779211)
            ·
              refine ⟨1502108971742419207168817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001405981161612804779211 1502108971742419207168817)
              ·
                refine ⟨1126581728806814405376613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1502108971742419207168817 1126581728806814405376613)
                ·
                  refine ⟨211234074151277701008115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1126581728806814405376613 211234074151277701008115)
                  ·
                    rfl

theorem cell21_925598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_925598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925598 prefixEnd_925598 := by exact prefixLift 925598
  have htrace : WordTrace (prefixWord ++ tailWord_925598) baseStart_925598 baseEnd_925598 := by
    simpa [prefixWord, tailWord_925598, baseEnd_925598] using wordTrace_append hprefix tailTrace_925598
  have hstable : (prefixWord ++ tailWord_925598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925598).length < 2 ^ (prefixWord ++ tailWord_925598).sum := by decide
  have hdescent : baseEnd_925598 < baseStart_925598 := by decide
  rcases family_descends (prefixWord ++ tailWord_925598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925660 : List Nat := [2, 2, 6, 1, 2, 1, 1, 1, 5]
def baseStart_925660 : Nat := 118140960795 + 925660 * 2 ^ 59
def prefixEnd_925660 : Nat := 4983230072969 + 3 ^ 40 * 925660 * 2
def baseEnd_925660 : Nat := 211248223395979370974655

theorem tailTrace_925660 : CollatzResearch.WordTrace tailWord_925660 prefixEnd_925660 211248223395979370974655 := by
  unfold tailWord_925660
  simp only [CollatzResearch.WordTrace]
  refine ⟨16880796913249692493455217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22507729217666256657940289 16880796913249692493455217)
  ·
    refine ⟨12660597684937269370091413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16880796913249692493455217 12660597684937269370091413)
    ·
      refine ⟨593465516481434501723035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12660597684937269370091413 593465516481434501723035)
      ·
        refine ⟨890198274722151752584553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593465516481434501723035 890198274722151752584553)
        ·
          refine ⟨667648706041613814438415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 890198274722151752584553 667648706041613814438415)
          ·
            refine ⟨1001473059062420721657623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667648706041613814438415 1001473059062420721657623)
            ·
              refine ⟨1502209588593631082486435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001473059062420721657623 1502209588593631082486435)
              ·
                refine ⟨2253314382890446623729653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502209588593631082486435 2253314382890446623729653)
                ·
                  refine ⟨211248223395979370974655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2253314382890446623729653 211248223395979370974655)
                  ·
                    rfl

theorem cell21_925660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_925660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925660 prefixEnd_925660 := by exact prefixLift 925660
  have htrace : WordTrace (prefixWord ++ tailWord_925660) baseStart_925660 baseEnd_925660 := by
    simpa [prefixWord, tailWord_925660, baseEnd_925660] using wordTrace_append hprefix tailTrace_925660
  have hstable : (prefixWord ++ tailWord_925660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925660).length < 2 ^ (prefixWord ++ tailWord_925660).sum := by decide
  have hdescent : baseEnd_925660 < baseStart_925660 := by decide
  rcases family_descends (prefixWord ++ tailWord_925660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925719 : List Nat := [1, 1, 3, 5, 2, 2, 2, 2, 3]
def baseStart_925719 : Nat := 118140960795 + 925719 * 2 ^ 59
def prefixEnd_925719 : Nat := 4983230072969 + 3 ^ 40 * 925719 * 2
def baseEnd_925719 : Nat := 211261687999808379491201

theorem tailTrace_925719 : CollatzResearch.WordTrace tailWord_925719 prefixEnd_925719 211261687999808379491201 := by
  unfold tailWord_925719
  simp only [CollatzResearch.WordTrace]
  refine ⟨33763745733285638063308211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22509163822190425375538807 33763745733285638063308211)
  ·
    refine ⟨50645618599928457094962317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33763745733285638063308211 50645618599928457094962317)
    ·
      refine ⟨18992106974973171410610869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50645618599928457094962317 18992106974973171410610869)
      ·
        refine ⟨1780510028903734819744769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18992106974973171410610869 1780510028903734819744769)
        ·
          refine ⟨1335382521677801114808577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1780510028903734819744769 1335382521677801114808577)
          ·
            refine ⟨1001536891258350836106433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1335382521677801114808577 1001536891258350836106433)
            ·
              refine ⟨751152668443763127079825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1001536891258350836106433 751152668443763127079825)
              ·
                refine ⟨563364501332822345309869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751152668443763127079825 563364501332822345309869)
                ·
                  refine ⟨211261687999808379491201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 563364501332822345309869 211261687999808379491201)
                  ·
                    rfl

theorem cell21_925719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 3].length) (baseStart_925719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925719 prefixEnd_925719 := by exact prefixLift 925719
  have htrace : WordTrace (prefixWord ++ tailWord_925719) baseStart_925719 baseEnd_925719 := by
    simpa [prefixWord, tailWord_925719, baseEnd_925719] using wordTrace_append hprefix tailTrace_925719
  have hstable : (prefixWord ++ tailWord_925719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925719).length < 2 ^ (prefixWord ++ tailWord_925719).sum := by decide
  have hdescent : baseEnd_925719 < baseStart_925719 := by decide
  rcases family_descends (prefixWord ++ tailWord_925719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925727 : List Nat := [1, 1, 2, 4, 1, 2, 2, 3, 5]
def baseStart_925727 : Nat := 118140960795 + 925727 * 2 ^ 59
def prefixEnd_925727 : Nat := 4983230072969 + 3 ^ 40 * 925727 * 2
def baseEnd_925727 : Nat := 211263513708802143357851

theorem tailTrace_925727 : CollatzResearch.WordTrace tailWord_925727 prefixEnd_925727 211263513708802143357851 := by
  unfold tailWord_925727
  simp only [CollatzResearch.WordTrace]
  refine ⟨33764037517256655429599435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22509358344837770286399623 33764037517256655429599435)
  ·
    refine ⟨50646056275884983144399153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33764037517256655429599435 50646056275884983144399153)
    ·
      refine ⟨37984542206913737358299365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50646056275884983144399153 37984542206913737358299365)
      ·
        refine ⟨7122101663796325754681131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37984542206913737358299365 7122101663796325754681131)
        ·
          refine ⟨10683152495694488632021697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7122101663796325754681131 10683152495694488632021697)
          ·
            refine ⟨8012364371770866474016273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10683152495694488632021697 8012364371770866474016273)
            ·
              refine ⟨6009273278828149855512205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8012364371770866474016273 6009273278828149855512205)
              ·
                refine ⟨2253477479560556195817077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6009273278828149855512205 2253477479560556195817077)
                ·
                  refine ⟨211263513708802143357851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2253477479560556195817077 211263513708802143357851)
                  ·
                    rfl

theorem cell21_925727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 5].length) (baseStart_925727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925727 prefixEnd_925727 := by exact prefixLift 925727
  have htrace : WordTrace (prefixWord ++ tailWord_925727) baseStart_925727 baseEnd_925727 := by
    simpa [prefixWord, tailWord_925727, baseEnd_925727] using wordTrace_append hprefix tailTrace_925727
  have hstable : (prefixWord ++ tailWord_925727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925727).length < 2 ^ (prefixWord ++ tailWord_925727).sum := by decide
  have hdescent : baseEnd_925727 < baseStart_925727 := by decide
  rcases family_descends (prefixWord ++ tailWord_925727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925761 : List Nat := [1, 2, 5, 1, 2, 1, 1, 5, 3]
def baseStart_925761 : Nat := 118140960795 + 925761 * 2 ^ 59
def prefixEnd_925761 : Nat := 4983230072969 + 3 ^ 40 * 925761 * 2
def baseEnd_925761 : Nat := 211271272972025639791115

theorem tailTrace_925761 : CollatzResearch.WordTrace tailWord_925761 prefixEnd_925761 211271272972025639791115 := by
  unfold tailWord_925761
  simp only [CollatzResearch.WordTrace]
  refine ⟨33765277599133479236337137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22510185066088986157558091 33765277599133479236337137)
  ·
    refine ⟨25323958199350109427252853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33765277599133479236337137 25323958199350109427252853)
    ·
      refine ⟨2374121081189072758804955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25323958199350109427252853 2374121081189072758804955)
      ·
        refine ⟨3561181621783609138207433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2374121081189072758804955 3561181621783609138207433)
        ·
          refine ⟨2670886216337706853655575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3561181621783609138207433 2670886216337706853655575)
          ·
            refine ⟨4006329324506560280483363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2670886216337706853655575 4006329324506560280483363)
            ·
              refine ⟨6009493986759840420725045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4006329324506560280483363 6009493986759840420725045)
              ·
                refine ⟨563390061258735039442973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6009493986759840420725045 563390061258735039442973)
                ·
                  refine ⟨211271272972025639791115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 563390061258735039442973 211271272972025639791115)
                  ·
                    rfl

theorem cell21_925761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 3].length) (baseStart_925761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925761 prefixEnd_925761 := by exact prefixLift 925761
  have htrace : WordTrace (prefixWord ++ tailWord_925761) baseStart_925761 baseEnd_925761 := by
    simpa [prefixWord, tailWord_925761, baseEnd_925761] using wordTrace_append hprefix tailTrace_925761
  have hstable : (prefixWord ++ tailWord_925761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925761).length < 2 ^ (prefixWord ++ tailWord_925761).sum := by decide
  have hdescent : baseEnd_925761 < baseStart_925761 := by decide
  rcases family_descends (prefixWord ++ tailWord_925761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925834 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 6]
def baseStart_925834 : Nat := 118140960795 + 925834 * 2 ^ 59
def prefixEnd_925834 : Nat := 4983230072969 + 3 ^ 40 * 925834 * 2
def baseEnd_925834 : Nat := 211287932566593735074299

theorem tailTrace_925834 : CollatzResearch.WordTrace tailWord_925834 prefixEnd_925834 211287932566593735074299 := by
  unfold tailWord_925834
  simp only [CollatzResearch.WordTrace]
  refine ⟨8441985031967253175936139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22511960085246008469163037 8441985031967253175936139)
  ·
    refine ⟨12662977547950879763904209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8441985031967253175936139 12662977547950879763904209)
    ·
      refine ⟨9497233160963159822928157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12662977547950879763904209 9497233160963159822928157)
      ·
        refine ⟨3561462435361184933598059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9497233160963159822928157 3561462435361184933598059)
        ·
          refine ⟨5342193653041777400397089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3561462435361184933598059 5342193653041777400397089)
          ·
            refine ⟨4006645239781333050297817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5342193653041777400397089 4006645239781333050297817)
            ·
              refine ⟨3004983929835999787723363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4006645239781333050297817 3004983929835999787723363)
              ·
                refine ⟨4507475894753999681585045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3004983929835999787723363 4507475894753999681585045)
                ·
                  refine ⟨211287932566593735074299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4507475894753999681585045 211287932566593735074299)
                  ·
                    rfl

theorem cell21_925834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_925834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925834 prefixEnd_925834 := by exact prefixLift 925834
  have htrace : WordTrace (prefixWord ++ tailWord_925834) baseStart_925834 baseEnd_925834 := by
    simpa [prefixWord, tailWord_925834, baseEnd_925834] using wordTrace_append hprefix tailTrace_925834
  have hstable : (prefixWord ++ tailWord_925834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925834).length < 2 ^ (prefixWord ++ tailWord_925834).sum := by decide
  have hdescent : baseEnd_925834 < baseStart_925834 := by decide
  rcases family_descends (prefixWord ++ tailWord_925834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925893 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 6]
def baseStart_925893 : Nat := 118140960795 + 925893 * 2 ^ 59
def prefixEnd_925893 : Nat := 4983230072969 + 3 ^ 40 * 925893 * 2
def baseEnd_925893 : Nat := 211301397170422743590845

theorem tailTrace_925893 : CollatzResearch.WordTrace tailWord_925893 prefixEnd_925893 211301397170422743590845 := by
  unfold tailWord_925893
  simp only [CollatzResearch.WordTrace]
  refine ⟨33770092034655265780142333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22513394689770177186761555 33770092034655265780142333)
  ·
    refine ⟨12663784512995724667553375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33770092034655265780142333 12663784512995724667553375)
    ·
      refine ⟨18995676769493587001330063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12663784512995724667553375 18995676769493587001330063)
      ·
        refine ⟨28493515154240380501995095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18995676769493587001330063 28493515154240380501995095)
        ·
          refine ⟨42740272731360570752992643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28493515154240380501995095 42740272731360570752992643)
          ·
            refine ⟨64110409097040856129488965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42740272731360570752992643 64110409097040856129488965)
            ·
              refine ⟨12020701705695160524279181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64110409097040856129488965 12020701705695160524279181)
              ·
                refine ⟨4507763139635685196604693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12020701705695160524279181 4507763139635685196604693)
                ·
                  refine ⟨211301397170422743590845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4507763139635685196604693 211301397170422743590845)
                  ·
                    rfl

theorem cell21_925893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_925893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925893 prefixEnd_925893 := by exact prefixLift 925893
  have htrace : WordTrace (prefixWord ++ tailWord_925893) baseStart_925893 baseEnd_925893 := by
    simpa [prefixWord, tailWord_925893, baseEnd_925893] using wordTrace_append hprefix tailTrace_925893
  have hstable : (prefixWord ++ tailWord_925893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925893).length < 2 ^ (prefixWord ++ tailWord_925893).sum := by decide
  have hdescent : baseEnd_925893 < baseStart_925893 := by decide
  rcases family_descends (prefixWord ++ tailWord_925893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925955 : List Nat := [1, 1, 1, 3, 2, 3, 4, 1, 5]
def baseStart_925955 : Nat := 118140960795 + 925955 * 2 ^ 59
def prefixEnd_925955 : Nat := 4983230072969 + 3 ^ 40 * 925955 * 2
def baseEnd_925955 : Nat := 211315546415124413557385

theorem tailTrace_925955 : CollatzResearch.WordTrace tailWord_925955 prefixEnd_925955 211315546415124413557385 := by
  unfold tailWord_925955
  simp only [CollatzResearch.WordTrace]
  refine ⟨33772353360430650368899319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22514902240287100245932879 33772353360430650368899319)
  ·
    refine ⟨50658530040645975553348979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33772353360430650368899319 50658530040645975553348979)
    ·
      refine ⟨75987795060968963330023469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50658530040645975553348979 75987795060968963330023469)
      ·
        refine ⟨28495423147863361248758801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75987795060968963330023469 28495423147863361248758801)
        ·
          refine ⟨21371567360897520936569101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28495423147863361248758801 21371567360897520936569101)
          ·
            refine ⟨8014337760336570351213413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21371567360897520936569101 8014337760336570351213413)
            ·
              refine ⟨1502688330063106940852515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8014337760336570351213413 1502688330063106940852515)
              ·
                refine ⟨2254032495094660411278773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1502688330063106940852515 2254032495094660411278773)
                ·
                  refine ⟨211315546415124413557385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2254032495094660411278773 211315546415124413557385)
                  ·
                    rfl

theorem cell21_925955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 5].length) (baseStart_925955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925955 prefixEnd_925955 := by exact prefixLift 925955
  have htrace : WordTrace (prefixWord ++ tailWord_925955) baseStart_925955 baseEnd_925955 := by
    simpa [prefixWord, tailWord_925955, baseEnd_925955] using wordTrace_append hprefix tailTrace_925955
  have hstable : (prefixWord ++ tailWord_925955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925955).length < 2 ^ (prefixWord ++ tailWord_925955).sum := by decide
  have hdescent : baseEnd_925955 < baseStart_925955 := by decide
  rcases family_descends (prefixWord ++ tailWord_925955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925986 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 6]
def baseStart_925986 : Nat := 118140960795 + 925986 * 2 ^ 59
def prefixEnd_925986 : Nat := 4983230072969 + 3 ^ 40 * 925986 * 2
def baseEnd_925986 : Nat := 211322621037475248540655

theorem tailTrace_925986 : CollatzResearch.WordTrace tailWord_925986 prefixEnd_925986 211322621037475248540655 := by
  unfold tailWord_925986
  simp only [CollatzResearch.WordTrace]
  refine ⟨8443371005829585665819453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22515656015545561775518541 8443371005829585665819453)
  ·
    refine ⟨3166264127186094624682295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8443371005829585665819453 3166264127186094624682295)
    ·
      refine ⟨4749396190779141937023443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3166264127186094624682295 4749396190779141937023443)
      ·
        refine ⟨7124094286168712905535165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4749396190779141937023443 7124094286168712905535165)
        ·
          refine ⟨2671535357313267339575687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7124094286168712905535165 2671535357313267339575687)
          ·
            refine ⟨4007303035969901009363531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2671535357313267339575687 4007303035969901009363531)
            ·
              refine ⟨6010954553954851514045297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4007303035969901009363531 6010954553954851514045297)
              ·
                refine ⟨4508215915466138635533973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6010954553954851514045297 4508215915466138635533973)
                ·
                  refine ⟨211322621037475248540655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4508215915466138635533973 211322621037475248540655)
                  ·
                    rfl

theorem cell21_925986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_925986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_925986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_925986 prefixEnd_925986 := by exact prefixLift 925986
  have htrace : WordTrace (prefixWord ++ tailWord_925986) baseStart_925986 baseEnd_925986 := by
    simpa [prefixWord, tailWord_925986, baseEnd_925986] using wordTrace_append hprefix tailTrace_925986
  have hstable : (prefixWord ++ tailWord_925986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925986).length < 2 ^ (prefixWord ++ tailWord_925986).sum := by decide
  have hdescent : baseEnd_925986 < baseStart_925986 := by decide
  rcases family_descends (prefixWord ++ tailWord_925986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926020 : List Nat := [2, 3, 4, 1, 2, 1, 1, 3, 4]
def baseStart_926020 : Nat := 118140960795 + 926020 * 2 ^ 59
def prefixEnd_926020 : Nat := 4983230072969 + 3 ^ 40 * 926020 * 2
def baseEnd_926020 : Nat := 211330380300698744973919

theorem tailTrace_926020 : CollatzResearch.WordTrace tailWord_926020 prefixEnd_926020 211330380300698744973919 := by
  unfold tailWord_926020
  simp only [CollatzResearch.WordTrace]
  refine ⟨16887362052597583235007757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22516482736796777646677009 16887362052597583235007757)
  ·
    refine ⟨6332760769724093713127909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16887362052597583235007757 6332760769724093713127909)
    ·
      refine ⟨1187392644323267571211483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6332760769724093713127909 1187392644323267571211483)
      ·
        refine ⟨1781088966484901356817225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1187392644323267571211483 1781088966484901356817225)
        ·
          refine ⟨1335816724863676017612919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1781088966484901356817225 1335816724863676017612919)
          ·
            refine ⟨2003725087295514026419379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335816724863676017612919 2003725087295514026419379)
            ·
              refine ⟨3005587630943271039629069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2003725087295514026419379 3005587630943271039629069)
              ·
                refine ⟨1127095361603726639860901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3005587630943271039629069 1127095361603726639860901)
                ·
                  refine ⟨211330380300698744973919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1127095361603726639860901 211330380300698744973919)
                  ·
                    rfl

theorem cell21_926020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_926020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926020 prefixEnd_926020 := by exact prefixLift 926020
  have htrace : WordTrace (prefixWord ++ tailWord_926020) baseStart_926020 baseEnd_926020 := by
    simpa [prefixWord, tailWord_926020, baseEnd_926020] using wordTrace_append hprefix tailTrace_926020
  have hstable : (prefixWord ++ tailWord_926020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926020).length < 2 ^ (prefixWord ++ tailWord_926020).sum := by decide
  have hdescent : baseEnd_926020 < baseStart_926020 := by decide
  rcases family_descends (prefixWord ++ tailWord_926020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926113 : List Nat := [1, 2, 3, 5, 2, 1, 1, 2, 4]
def baseStart_926113 : Nat := 118140960795 + 926113 * 2 ^ 59
def prefixEnd_926113 : Nat := 4983230072969 + 3 ^ 40 * 926113 * 2
def baseEnd_926113 : Nat := 211351604167751249923729

theorem tailTrace_926113 : CollatzResearch.WordTrace tailWord_926113 prefixEnd_926113 211351604167751249923729 := by
  unfold tailWord_926113
  simp only [CollatzResearch.WordTrace]
  refine ⟨33778116093858243353150993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22518744062572162235433995 33778116093858243353150993)
  ·
    refine ⟨25333587070393682514863245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33778116093858243353150993 25333587070393682514863245)
    ·
      refine ⟨9500095151397630943073717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25333587070393682514863245 9500095151397630943073717)
      ·
        refine ⟨890633920443527900913161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9500095151397630943073717 890633920443527900913161)
        ·
          refine ⟨667975440332645925684871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 890633920443527900913161 667975440332645925684871)
          ·
            refine ⟨1001963160498968888527307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667975440332645925684871 1001963160498968888527307)
            ·
              refine ⟨1502944740748453332790961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001963160498968888527307 1502944740748453332790961)
              ·
                refine ⟨1127208555561339999593221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1502944740748453332790961 1127208555561339999593221)
                ·
                  refine ⟨211351604167751249923729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1127208555561339999593221 211351604167751249923729)
                  ·
                    rfl

theorem cell21_926113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 4].length) (baseStart_926113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926113 prefixEnd_926113 := by exact prefixLift 926113
  have htrace : WordTrace (prefixWord ++ tailWord_926113) baseStart_926113 baseEnd_926113 := by
    simpa [prefixWord, tailWord_926113, baseEnd_926113] using wordTrace_append hprefix tailTrace_926113
  have hstable : (prefixWord ++ tailWord_926113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926113).length < 2 ^ (prefixWord ++ tailWord_926113).sum := by decide
  have hdescent : baseEnd_926113 < baseStart_926113 := by decide
  rcases family_descends (prefixWord ++ tailWord_926113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926152 : List Nat := [2, 1, 3, 1, 3, 3, 1, 7]
def baseStart_926152 : Nat := 118140960795 + 926152 * 2 ^ 59
def prefixEnd_926152 : Nat := 4983230072969 + 3 ^ 40 * 926152 * 2
def baseEnd_926152 : Nat := 70453501499698616257883

theorem tailTrace_926152 : CollatzResearch.WordTrace tailWord_926152 prefixEnd_926152 70453501499698616257883 := by
  unfold tailWord_926152
  simp only [CollatzResearch.WordTrace]
  refine ⟨16889769270358476506910355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22519692360477968675880473 16889769270358476506910355)
  ·
    refine ⟨25334653905537714760365533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16889769270358476506910355 25334653905537714760365533)
    ·
      refine ⟨9500495214576643035137075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25334653905537714760365533 9500495214576643035137075)
      ·
        refine ⟨14250742821864964552705613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9500495214576643035137075 14250742821864964552705613)
        ·
          refine ⟨5344028558199361707264605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14250742821864964552705613 5344028558199361707264605)
          ·
            refine ⟨2004010709324760640224227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5344028558199361707264605 2004010709324760640224227)
            ·
              refine ⟨3006016063987140960336341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2004010709324760640224227 3006016063987140960336341)
              ·
                refine ⟨70453501499698616257883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3006016063987140960336341 70453501499698616257883)
                ·
                  rfl

theorem cell21_926152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 7].length) (baseStart_926152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926152 prefixEnd_926152 := by exact prefixLift 926152
  have htrace : WordTrace (prefixWord ++ tailWord_926152) baseStart_926152 baseEnd_926152 := by
    simpa [prefixWord, tailWord_926152, baseEnd_926152] using wordTrace_append hprefix tailTrace_926152
  have hstable : (prefixWord ++ tailWord_926152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926152).length < 2 ^ (prefixWord ++ tailWord_926152).sum := by decide
  have hdescent : baseEnd_926152 < baseStart_926152 := by decide
  rcases family_descends (prefixWord ++ tailWord_926152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926211 : List Nat := [1, 1, 1, 3, 2, 1, 3, 9]
def baseStart_926211 : Nat := 118140960795 + 926211 * 2 ^ 59
def prefixEnd_926211 : Nat := 4983230072969 + 3 ^ 40 * 926211 * 2
def baseEnd_926211 : Nat := 70457989700974952430065

theorem tailTrace_926211 : CollatzResearch.WordTrace tailWord_926211 prefixEnd_926211 70457989700974952430065 := by
  unfold tailWord_926211
  simp only [CollatzResearch.WordTrace]
  refine ⟨33781690447503206090218487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22521126965002137393478991 33781690447503206090218487)
  ·
    refine ⟨50672535671254809135327731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33781690447503206090218487 50672535671254809135327731)
    ·
      refine ⟨76008803506882213702991597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50672535671254809135327731 76008803506882213702991597)
      ·
        refine ⟨28503301315080830138621849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76008803506882213702991597 28503301315080830138621849)
        ·
          refine ⟨21377475986310622603966387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28503301315080830138621849 21377475986310622603966387)
          ·
            refine ⟨32066213979465933905949581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21377475986310622603966387 32066213979465933905949581)
            ·
              refine ⟨12024830242299725214731093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32066213979465933905949581 12024830242299725214731093)
              ·
                refine ⟨70457989700974952430065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12024830242299725214731093 70457989700974952430065)
                ·
                  rfl

theorem cell21_926211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 9].length) (baseStart_926211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926211 prefixEnd_926211 := by exact prefixLift 926211
  have htrace : WordTrace (prefixWord ++ tailWord_926211) baseStart_926211 baseEnd_926211 := by
    simpa [prefixWord, tailWord_926211, baseEnd_926211] using wordTrace_append hprefix tailTrace_926211
  have hstable : (prefixWord ++ tailWord_926211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926211).length < 2 ^ (prefixWord ++ tailWord_926211).sum := by decide
  have hdescent : baseEnd_926211 < baseStart_926211 := by decide
  rcases family_descends (prefixWord ++ tailWord_926211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926262 : List Nat := [5, 1, 2, 1, 2, 2, 3, 5]
def baseStart_926262 : Nat := 118140960795 + 926262 * 2 ^ 59
def prefixEnd_926262 : Nat := 4983230072969 + 3 ^ 40 * 926262 * 2
def baseEnd_926262 : Nat := 70461869332586700646697

theorem tailTrace_926262 : CollatzResearch.WordTrace tailWord_926262 prefixEnd_926262 70461869332586700646697 := by
  unfold tailWord_926262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2111471910644902612520315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22522367046878961200216693 2111471910644902612520315)
  ·
    refine ⟨3167207865967353918780473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2111471910644902612520315 3167207865967353918780473)
    ·
      refine ⟨2375405899475515439085355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3167207865967353918780473 2375405899475515439085355)
      ·
        refine ⟨3563108849213273158628033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2375405899475515439085355 3563108849213273158628033)
        ·
          refine ⟨2672331636909954868971025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3563108849213273158628033 2672331636909954868971025)
          ·
            refine ⟨2004248727682466151728269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2672331636909954868971025 2004248727682466151728269)
            ·
              refine ⟨751593272880924806898101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2004248727682466151728269 751593272880924806898101)
              ·
                refine ⟨70461869332586700646697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 751593272880924806898101 70461869332586700646697)
                ·
                  rfl

theorem cell21_926262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_926262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926262 prefixEnd_926262 := by exact prefixLift 926262
  have htrace : WordTrace (prefixWord ++ tailWord_926262) baseStart_926262 baseEnd_926262 := by
    simpa [prefixWord, tailWord_926262, baseEnd_926262] using wordTrace_append hprefix tailTrace_926262
  have hstable : (prefixWord ++ tailWord_926262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926262).length < 2 ^ (prefixWord ++ tailWord_926262).sum := by decide
  have hdescent : baseEnd_926262 < baseStart_926262 := by decide
  rcases family_descends (prefixWord ++ tailWord_926262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926335 : List Nat := [1, 1, 2, 2, 1, 1, 1, 9, 3]
def baseStart_926335 : Nat := 118140960795 + 926335 * 2 ^ 59
def prefixEnd_926335 : Nat := 4983230072969 + 3 ^ 40 * 926335 * 2
def baseEnd_926335 : Nat := 211402267592328197223275

theorem tailTrace_926335 : CollatzResearch.WordTrace tailWord_926335 prefixEnd_926335 211402267592328197223275 := by
  unfold tailWord_926335
  simp only [CollatzResearch.WordTrace]
  refine ⟨33786213099053975267732459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22524142066035983511821639 33786213099053975267732459)
  ·
    refine ⟨50679319648580962901598689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33786213099053975267732459 50679319648580962901598689)
    ·
      refine ⟨38009489736435722176199017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50679319648580962901598689 38009489736435722176199017)
      ·
        refine ⟨28507117302326791632149263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38009489736435722176199017 28507117302326791632149263)
        ·
          refine ⟨42760675953490187448223895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28507117302326791632149263 42760675953490187448223895)
          ·
            refine ⟨64141013930235281172335843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42760675953490187448223895 64141013930235281172335843)
            ·
              refine ⟨96211520895352921758503765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64141013930235281172335843 96211520895352921758503765)
              ·
                refine ⟨563739380246208525928733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 96211520895352921758503765 563739380246208525928733)
                ·
                  refine ⟨211402267592328197223275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 563739380246208525928733 211402267592328197223275)
                  ·
                    rfl

theorem cell21_926335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 3].length) (baseStart_926335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926335 prefixEnd_926335 := by exact prefixLift 926335
  have htrace : WordTrace (prefixWord ++ tailWord_926335) baseStart_926335 baseEnd_926335 := by
    simpa [prefixWord, tailWord_926335, baseEnd_926335] using wordTrace_append hprefix tailTrace_926335
  have hstable : (prefixWord ++ tailWord_926335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926335).length < 2 ^ (prefixWord ++ tailWord_926335).sum := by decide
  have hdescent : baseEnd_926335 < baseStart_926335 := by decide
  rcases family_descends (prefixWord ++ tailWord_926335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926425 : List Nat := [1, 2, 1, 2, 3, 2, 1, 5, 4]
def baseStart_926425 : Nat := 118140960795 + 926425 * 2 ^ 59
def prefixEnd_926425 : Nat := 4983230072969 + 3 ^ 40 * 926425 * 2
def baseEnd_926425 : Nat := 211422806818508040723091

theorem tailTrace_926425 : CollatzResearch.WordTrace tailWord_926425 prefixEnd_926425 211422806818508040723091 := by
  unfold tailWord_926425
  simp only [CollatzResearch.WordTrace]
  refine ⟨33789495668727920638508729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22526330445818613759005819 33789495668727920638508729)
  ·
    refine ⟨25342121751545940478881547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33789495668727920638508729 25342121751545940478881547)
    ·
      refine ⟨38013182627318910718322321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25342121751545940478881547 38013182627318910718322321)
      ·
        refine ⟨28509886970489183038741741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38013182627318910718322321 28509886970489183038741741)
        ·
          refine ⟨10691207613933443639528153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28509886970489183038741741 10691207613933443639528153)
          ·
            refine ⟨8018405710450082729646115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10691207613933443639528153 8018405710450082729646115)
            ·
              refine ⟨12027608565675124094469173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8018405710450082729646115 12027608565675124094469173)
              ·
                refine ⟨1127588303032042883856485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12027608565675124094469173 1127588303032042883856485)
                ·
                  refine ⟨211422806818508040723091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1127588303032042883856485 211422806818508040723091)
                  ·
                    rfl

theorem cell21_926425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_926425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926425 prefixEnd_926425 := by exact prefixLift 926425
  have htrace : WordTrace (prefixWord ++ tailWord_926425) baseStart_926425 baseEnd_926425 := by
    simpa [prefixWord, tailWord_926425, baseEnd_926425] using wordTrace_append hprefix tailTrace_926425
  have hstable : (prefixWord ++ tailWord_926425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926425).length < 2 ^ (prefixWord ++ tailWord_926425).sum := by decide
  have hdescent : baseEnd_926425 < baseStart_926425 := by decide
  rcases family_descends (prefixWord ++ tailWord_926425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926428 : List Nat := [2, 2, 5, 1, 1, 2, 1, 2, 5]
def baseStart_926428 : Nat := 118140960795 + 926428 * 2 ^ 59
def prefixEnd_926428 : Nat := 4983230072969 + 3 ^ 40 * 926428 * 2
def baseEnd_926428 : Nat := 211423491459380702173085

theorem tailTrace_926428 : CollatzResearch.WordTrace tailWord_926428 prefixEnd_926428 211423491459380702173085 := by
  unfold tailWord_926428
  simp only [CollatzResearch.WordTrace]
  refine ⟨16894802543858526075433969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22526403391811368100578625 16894802543858526075433969)
  ·
    refine ⟨12671101907893894556575477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16894802543858526075433969 12671101907893894556575477)
    ·
      refine ⟨1187915803865052614678951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12671101907893894556575477 1187915803865052614678951)
      ·
        refine ⟨1781873705797578922018427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1187915803865052614678951 1781873705797578922018427)
        ·
          refine ⟨2672810558696368383027641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1781873705797578922018427 2672810558696368383027641)
          ·
            refine ⟨2004607919022276287270731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2672810558696368383027641 2004607919022276287270731)
            ·
              refine ⟨3006911878533414430906097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2004607919022276287270731 3006911878533414430906097)
              ·
                refine ⟨2255183908900060823179573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3006911878533414430906097 2255183908900060823179573)
                ·
                  refine ⟨211423491459380702173085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2255183908900060823179573 211423491459380702173085)
                  ·
                    rfl

theorem cell21_926428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_926428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926428 prefixEnd_926428 := by exact prefixLift 926428
  have htrace : WordTrace (prefixWord ++ tailWord_926428) baseStart_926428 baseEnd_926428 := by
    simpa [prefixWord, tailWord_926428, baseEnd_926428] using wordTrace_append hprefix tailTrace_926428
  have hstable : (prefixWord ++ tailWord_926428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926428).length < 2 ^ (prefixWord ++ tailWord_926428).sum := by decide
  have hdescent : baseEnd_926428 < baseStart_926428 := by decide
  rcases family_descends (prefixWord ++ tailWord_926428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926515 : List Nat := [1, 1, 1, 2, 6, 1, 9]
def baseStart_926515 : Nat := 118140960795 + 926515 * 2 ^ 59
def prefixEnd_926515 : Nat := 4983230072969 + 3 ^ 40 * 926515 * 2
def baseEnd_926515 : Nat := 23493705116076431580323

theorem tailTrace_926515 : CollatzResearch.WordTrace tailWord_926515 prefixEnd_926515 23493705116076431580323 := by
  unfold tailWord_926515
  simp only [CollatzResearch.WordTrace]
  refine ⟨33792778238401866009284999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22528518825601244006189999 33792778238401866009284999)
  ·
    refine ⟨50689167357602799013927499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33792778238401866009284999 50689167357602799013927499)
    ·
      refine ⟨76033751036404198520891249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50689167357602799013927499 76033751036404198520891249)
      ·
        refine ⟨57025313277303148890668437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76033751036404198520891249 57025313277303148890668437)
        ·
          refine ⟨2673061559873585104250083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57025313277303148890668437 2673061559873585104250083)
          ·
            refine ⟨4009592339810377656375125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673061559873585104250083 4009592339810377656375125)
            ·
              refine ⟨23493705116076431580323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4009592339810377656375125 23493705116076431580323)
              ·
                rfl

theorem cell21_926515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 9].length) (baseStart_926515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926515 prefixEnd_926515 := by exact prefixLift 926515
  have htrace : WordTrace (prefixWord ++ tailWord_926515) baseStart_926515 baseEnd_926515 := by
    simpa [prefixWord, tailWord_926515, baseEnd_926515] using wordTrace_append hprefix tailTrace_926515
  have hstable : (prefixWord ++ tailWord_926515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926515).length < 2 ^ (prefixWord ++ tailWord_926515).sum := by decide
  have hdescent : baseEnd_926515 < baseStart_926515 := by decide
  rcases family_descends (prefixWord ++ tailWord_926515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926546 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 7]
def baseStart_926546 : Nat := 118140960795 + 926546 * 2 ^ 59
def prefixEnd_926546 : Nat := 4983230072969 + 3 ^ 40 * 926546 * 2
def baseEnd_926546 : Nat := 211450420667038719206177

theorem tailTrace_926546 : CollatzResearch.WordTrace tailWord_926546 prefixEnd_926546 211450420667038719206177 := by
  unfold tailWord_926546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8448477225322389575915873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22529272600859705535775661 8448477225322389575915873)
  ·
    refine ⟨6336357918991792181936905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8448477225322389575915873 6336357918991792181936905)
    ·
      refine ⟨4752268439243844136452679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6336357918991792181936905 4752268439243844136452679)
      ·
        refine ⟨7128402658865766204679019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4752268439243844136452679 7128402658865766204679019)
        ·
          refine ⟨10692603988298649307018529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7128402658865766204679019 10692603988298649307018529)
          ·
            refine ⟨8019452991223986980263897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10692603988298649307018529 8019452991223986980263897)
            ·
              refine ⟨6014589743417990235197923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8019452991223986980263897 6014589743417990235197923)
              ·
                refine ⟨9021884615126985352796885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6014589743417990235197923 9021884615126985352796885)
                ·
                  refine ⟨211450420667038719206177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9021884615126985352796885 211450420667038719206177)
                  ·
                    rfl

theorem cell21_926546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_926546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926546 prefixEnd_926546 := by exact prefixLift 926546
  have htrace : WordTrace (prefixWord ++ tailWord_926546) baseStart_926546 baseEnd_926546 := by
    simpa [prefixWord, tailWord_926546, baseEnd_926546] using wordTrace_append hprefix tailTrace_926546
  have hstable : (prefixWord ++ tailWord_926546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926546).length < 2 ^ (prefixWord ++ tailWord_926546).sum := by decide
  have hdescent : baseEnd_926546 < baseStart_926546 := by decide
  rcases family_descends (prefixWord ++ tailWord_926546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926577 : List Nat := [1, 2, 2, 2, 1, 4, 1, 4, 4]
def baseStart_926577 : Nat := 118140960795 + 926577 * 2 ^ 59
def prefixEnd_926577 : Nat := 4983230072969 + 3 ^ 40 * 926577 * 2
def baseEnd_926577 : Nat := 211457495289389554189447

theorem tailTrace_926577 : CollatzResearch.WordTrace tailWord_926577 prefixEnd_926577 211457495289389554189447 := by
  unfold tailWord_926577
  simp only [CollatzResearch.WordTrace]
  refine ⟨33795039564177250598041985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22530026376118167065361323 33795039564177250598041985)
  ·
    refine ⟨25346279673132937948531489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33795039564177250598041985 25346279673132937948531489)
    ·
      refine ⟨19009709754849703461398617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25346279673132937948531489 19009709754849703461398617)
      ·
        refine ⟨14257282316137277596048963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19009709754849703461398617 14257282316137277596048963)
        ·
          refine ⟨21385923474205916394073445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14257282316137277596048963 21385923474205916394073445)
          ·
            refine ⟨4009860651413609323888771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21385923474205916394073445 4009860651413609323888771)
            ·
              refine ⟨6014790977120413985833157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4009860651413609323888771 6014790977120413985833157)
              ·
                refine ⟨1127773308210077622343717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6014790977120413985833157 1127773308210077622343717)
                ·
                  refine ⟨211457495289389554189447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1127773308210077622343717 211457495289389554189447)
                  ·
                    rfl

theorem cell21_926577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_926577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926577 prefixEnd_926577 := by exact prefixLift 926577
  have htrace : WordTrace (prefixWord ++ tailWord_926577) baseStart_926577 baseEnd_926577 := by
    simpa [prefixWord, tailWord_926577, baseEnd_926577] using wordTrace_append hprefix tailTrace_926577
  have hstable : (prefixWord ++ tailWord_926577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926577).length < 2 ^ (prefixWord ++ tailWord_926577).sum := by decide
  have hdescent : baseEnd_926577 < baseStart_926577 := by decide
  rcases family_descends (prefixWord ++ tailWord_926577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926591 : List Nat := [1, 1, 2, 2, 1, 1, 7, 6]
def baseStart_926591 : Nat := 118140960795 + 926591 * 2 ^ 59
def prefixEnd_926591 : Nat := 4983230072969 + 3 ^ 40 * 926591 * 2
def baseEnd_926591 : Nat := 70486896760042880318695

theorem tailTrace_926591 : CollatzResearch.WordTrace tailWord_926591 prefixEnd_926591 70486896760042880318695 := by
  unfold tailWord_926591
  simp only [CollatzResearch.WordTrace]
  refine ⟨33795550186126530989051627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22530366790751020659367751 33795550186126530989051627)
  ·
    refine ⟨50693325279189796483577441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33795550186126530989051627 50693325279189796483577441)
    ·
      refine ⟨38019993959392347362683081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50693325279189796483577441 38019993959392347362683081)
      ·
        refine ⟨28514995469544260522012311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38019993959392347362683081 28514995469544260522012311)
        ·
          refine ⟨42772493204316390783018467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28514995469544260522012311 42772493204316390783018467)
          ·
            refine ⟨64158739806474586174527701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42772493204316390783018467 64158739806474586174527701)
            ·
              refine ⟨1503720464214248113465493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 64158739806474586174527701 1503720464214248113465493)
              ·
                refine ⟨70486896760042880318695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1503720464214248113465493 70486896760042880318695)
                ·
                  rfl

theorem cell21_926591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 6].length) (baseStart_926591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926591 prefixEnd_926591 := by exact prefixLift 926591
  have htrace : WordTrace (prefixWord ++ tailWord_926591) baseStart_926591 baseEnd_926591 := by
    simpa [prefixWord, tailWord_926591, baseEnd_926591] using wordTrace_append hprefix tailTrace_926591
  have hstable : (prefixWord ++ tailWord_926591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926591).length < 2 ^ (prefixWord ++ tailWord_926591).sum := by decide
  have hdescent : baseEnd_926591 < baseStart_926591 := by decide
  rcases family_descends (prefixWord ++ tailWord_926591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926614 : List Nat := [5, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_926614 : Nat := 118140960795 + 926614 * 2 ^ 59
def prefixEnd_926614 : Nat := 4983230072969 + 3 ^ 40 * 926614 * 2
def baseEnd_926614 : Nat := 211465939193485712072705

theorem tailTrace_926614 : CollatzResearch.WordTrace tailWord_926614 prefixEnd_926614 211465939193485712072705 := by
  unfold tailWord_926614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2112274316565200369821181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22530926043362137278092597 2112274316565200369821181)
  ·
    refine ⟨792102868711950138682943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2112274316565200369821181 792102868711950138682943)
    ·
      refine ⟨1188154303067925208024415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 792102868711950138682943 1188154303067925208024415)
      ·
        refine ⟨1782231454601887812036623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188154303067925208024415 1782231454601887812036623)
        ·
          refine ⟨2673347181902831718054935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1782231454601887812036623 2673347181902831718054935)
          ·
            refine ⟨4010020772854247577082403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673347181902831718054935 4010020772854247577082403)
            ·
              refine ⟨6015031159281371365623605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4010020772854247577082403 6015031159281371365623605)
              ·
                refine ⟨563909171182628565527213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6015031159281371365623605 563909171182628565527213)
                ·
                  refine ⟨211465939193485712072705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 563909171182628565527213 211465939193485712072705)
                  ·
                    rfl

theorem cell21_926614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_926614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926614 prefixEnd_926614 := by exact prefixLift 926614
  have htrace : WordTrace (prefixWord ++ tailWord_926614) baseStart_926614 baseEnd_926614 := by
    simpa [prefixWord, tailWord_926614, baseEnd_926614] using wordTrace_append hprefix tailTrace_926614
  have hstable : (prefixWord ++ tailWord_926614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926614).length < 2 ^ (prefixWord ++ tailWord_926614).sum := by decide
  have hdescent : baseEnd_926614 < baseStart_926614 := by decide
  rcases family_descends (prefixWord ++ tailWord_926614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926636 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 6]
def baseStart_926636 : Nat := 118140960795 + 926636 * 2 ^ 59
def prefixEnd_926636 : Nat := 4983230072969 + 3 ^ 40 * 926636 * 2
def baseEnd_926636 : Nat := 211470959893218562705993

theorem tailTrace_926636 : CollatzResearch.WordTrace tailWord_926636 prefixEnd_926636 211470959893218562705993 := by
  unfold tailWord_926636
  simp only [CollatzResearch.WordTrace]
  refine ⟨16898595735481751837219881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22531460980642335782959841 16898595735481751837219881)
  ·
    refine ⟨12673946801611313877914911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16898595735481751837219881 12673946801611313877914911)
    ·
      refine ⟨19010920202416970816872367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12673946801611313877914911 19010920202416970816872367)
      ·
        refine ⟨28516380303625456225308551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19010920202416970816872367 28516380303625456225308551)
        ·
          refine ⟨42774570455438184337962827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28516380303625456225308551 42774570455438184337962827)
          ·
            refine ⟨64161855683157276506944241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42774570455438184337962827 64161855683157276506944241)
            ·
              refine ⟨48121391762367957380208181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64161855683157276506944241 48121391762367957380208181)
              ·
                refine ⟨4511380477721996004394517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48121391762367957380208181 4511380477721996004394517)
                ·
                  refine ⟨211470959893218562705993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4511380477721996004394517 211470959893218562705993)
                  ·
                    rfl

theorem cell21_926636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_926636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926636 prefixEnd_926636 := by exact prefixLift 926636
  have htrace : WordTrace (prefixWord ++ tailWord_926636) baseStart_926636 baseEnd_926636 := by
    simpa [prefixWord, tailWord_926636, baseEnd_926636] using wordTrace_append hprefix tailTrace_926636
  have hstable : (prefixWord ++ tailWord_926636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926636).length < 2 ^ (prefixWord ++ tailWord_926636).sum := by decide
  have hdescent : baseEnd_926636 < baseStart_926636 := by decide
  rcases family_descends (prefixWord ++ tailWord_926636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926667 : List Nat := [1, 1, 1, 1, 3, 6, 1, 7]
def baseStart_926667 : Nat := 118140960795 + 926667 * 2 ^ 59
def prefixEnd_926667 : Nat := 4983230072969 + 3 ^ 40 * 926667 * 2
def baseEnd_926667 : Nat := 70492678171856465896421

theorem tailTrace_926667 : CollatzResearch.WordTrace tailWord_926667 prefixEnd_926667 70492678171856465896421 := by
  unfold tailWord_926667
  simp only [CollatzResearch.WordTrace]
  refine ⟨33798322133851195968818255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22532214755900797312545503 33798322133851195968818255)
  ·
    refine ⟨50697483200776793953227383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33798322133851195968818255 50697483200776793953227383)
    ·
      refine ⟨76046224801165190929841075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50697483200776793953227383 76046224801165190929841075)
      ·
        refine ⟨114069337201747786394761613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76046224801165190929841075 114069337201747786394761613)
        ·
          refine ⟨42776001450655419898035605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114069337201747786394761613 42776001450655419898035605)
          ·
            refine ⟨2005125067999472807720419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42776001450655419898035605 2005125067999472807720419)
            ·
              refine ⟨3007687601999209211580629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2005125067999472807720419 3007687601999209211580629)
              ·
                refine ⟨70492678171856465896421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3007687601999209211580629 70492678171856465896421)
                ·
                  rfl

theorem cell21_926667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 7].length) (baseStart_926667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926667 prefixEnd_926667 := by exact prefixLift 926667
  have htrace : WordTrace (prefixWord ++ tailWord_926667) baseStart_926667 baseEnd_926667 := by
    simpa [prefixWord, tailWord_926667, baseEnd_926667] using wordTrace_append hprefix tailTrace_926667
  have hstable : (prefixWord ++ tailWord_926667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926667).length < 2 ^ (prefixWord ++ tailWord_926667).sum := by decide
  have hdescent : baseEnd_926667 < baseStart_926667 := by decide
  rcases family_descends (prefixWord ++ tailWord_926667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926690 : List Nat := [3, 3, 3, 1, 1, 2, 3, 2, 3]
def baseStart_926690 : Nat := 118140960795 + 926690 * 2 ^ 59
def prefixEnd_926690 : Nat := 4983230072969 + 3 ^ 40 * 926690 * 2
def baseEnd_926690 : Nat := 211483283428926468805883

theorem tailTrace_926690 : CollatzResearch.WordTrace tailWord_926690 prefixEnd_926690 211483283428926468805883 := by
  unfold tailWord_926690
  simp only [CollatzResearch.WordTrace]
  refine ⟨8449790253191967724226381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22532774008511913931270349 8449790253191967724226381)
  ·
    refine ⟨3168671344946987896584893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8449790253191967724226381 3168671344946987896584893)
    ·
      refine ⟨1188251754355120461219335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3168671344946987896584893 1188251754355120461219335)
      ·
        refine ⟨1782377631532680691829003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188251754355120461219335 1782377631532680691829003)
        ·
          refine ⟨2673566447299021037743505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1782377631532680691829003 2673566447299021037743505)
          ·
            refine ⟨2005174835474265778307629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2673566447299021037743505 2005174835474265778307629)
            ·
              refine ⟨751940563302849666865361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2005174835474265778307629 751940563302849666865361)
              ·
                refine ⟨563955422477137250149021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751940563302849666865361 563955422477137250149021)
                ·
                  refine ⟨211483283428926468805883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 563955422477137250149021 211483283428926468805883)
                  ·
                    rfl

theorem cell21_926690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_926690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926690 prefixEnd_926690 := by exact prefixLift 926690
  have htrace : WordTrace (prefixWord ++ tailWord_926690) baseStart_926690 baseEnd_926690 := by
    simpa [prefixWord, tailWord_926690, baseEnd_926690] using wordTrace_append hprefix tailTrace_926690
  have hstable : (prefixWord ++ tailWord_926690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926690).length < 2 ^ (prefixWord ++ tailWord_926690).sum := by decide
  have hdescent : baseEnd_926690 < baseStart_926690 := by decide
  rcases family_descends (prefixWord ++ tailWord_926690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926743 : List Nat := [1, 1, 3, 5, 1, 10]
def baseStart_926743 : Nat := 118140960795 + 926743 * 2 ^ 59
def prefixEnd_926743 : Nat := 4983230072969 + 3 ^ 40 * 926743 * 2
def baseEnd_926743 : Nat := 7833162175963339052683

theorem tailTrace_926743 : CollatzResearch.WordTrace tailWord_926743 prefixEnd_926743 7833162175963339052683 := by
  unfold tailWord_926743
  simp only [CollatzResearch.WordTrace]
  refine ⟨33801094081575860948584883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22534062721050573965723255 33801094081575860948584883)
  ·
    refine ⟨50701641122363791422877325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33801094081575860948584883 50701641122363791422877325)
    ·
      refine ⟨19013115420886421783578997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50701641122363791422877325 19013115420886421783578997)
      ·
        refine ⟨1782479570708102042210531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19013115420886421783578997 1782479570708102042210531)
        ·
          refine ⟨2673719356062153063315797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1782479570708102042210531 2673719356062153063315797)
          ·
            refine ⟨7833162175963339052683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2673719356062153063315797 7833162175963339052683)
            ·
              rfl

theorem cell21_926743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 10].length) (baseStart_926743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926743 prefixEnd_926743 := by exact prefixLift 926743
  have htrace : WordTrace (prefixWord ++ tailWord_926743) baseStart_926743 baseEnd_926743 := by
    simpa [prefixWord, tailWord_926743, baseEnd_926743] using wordTrace_append hprefix tailTrace_926743
  have hstable : (prefixWord ++ tailWord_926743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926743).length < 2 ^ (prefixWord ++ tailWord_926743).sum := by decide
  have hdescent : baseEnd_926743 < baseStart_926743 := by decide
  rcases family_descends (prefixWord ++ tailWord_926743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926791 : List Nat := [1, 1, 4, 1, 3, 2, 1, 5, 3]
def baseStart_926791 : Nat := 118140960795 + 926791 * 2 ^ 59
def prefixEnd_926791 : Nat := 4983230072969 + 3 ^ 40 * 926791 * 2
def baseEnd_926791 : Nat := 211506333004972737622343

theorem tailTrace_926791 : CollatzResearch.WordTrace tailWord_926791 prefixEnd_926791 211506333004972737622343 := by
  unfold tailWord_926791
  simp only [CollatzResearch.WordTrace]
  refine ⟨33802844785401965146332227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22535229856934643430888151 33802844785401965146332227)
  ·
    refine ⟨50704267178102947719498341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33802844785401965146332227 50704267178102947719498341)
    ·
      refine ⟨9507050095894302697405939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50704267178102947719498341 9507050095894302697405939)
      ·
        refine ⟨14260575143841454046108909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9507050095894302697405939 14260575143841454046108909)
        ·
          refine ⟨5347715678940545267290841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14260575143841454046108909 5347715678940545267290841)
          ·
            refine ⟨4010786759205408950468131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5347715678940545267290841 4010786759205408950468131)
            ·
              refine ⟨6016180138808113425702197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4010786759205408950468131 6016180138808113425702197)
              ·
                refine ⟨564016888013260633659581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6016180138808113425702197 564016888013260633659581)
                ·
                  refine ⟨211506333004972737622343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 564016888013260633659581 211506333004972737622343)
                  ·
                    rfl

theorem cell21_926791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 3].length) (baseStart_926791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926791 prefixEnd_926791 := by exact prefixLift 926791
  have htrace : WordTrace (prefixWord ++ tailWord_926791) baseStart_926791 baseEnd_926791 := by
    simpa [prefixWord, tailWord_926791, baseEnd_926791] using wordTrace_append hprefix tailTrace_926791
  have hstable : (prefixWord ++ tailWord_926791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926791).length < 2 ^ (prefixWord ++ tailWord_926791).sum := by decide
  have hdescent : baseEnd_926791 < baseStart_926791 := by decide
  rcases family_descends (prefixWord ++ tailWord_926791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926833 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 7]
def baseStart_926833 : Nat := 118140960795 + 926833 * 2 ^ 59
def prefixEnd_926833 : Nat := 4983230072969 + 3 ^ 40 * 926833 * 2
def baseEnd_926833 : Nat := 211515917977189997922257

theorem tailTrace_926833 : CollatzResearch.WordTrace tailWord_926833 prefixEnd_926833 211515917977189997922257 := by
  unfold tailWord_926833
  simp only [CollatzResearch.WordTrace]
  refine ⟨33804376651249806319361153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22536251100833204212907435 33804376651249806319361153)
  ·
    refine ⟨25353282488437354739520865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33804376651249806319361153 25353282488437354739520865)
    ·
      refine ⟨19014961866328016054640649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25353282488437354739520865 19014961866328016054640649)
      ·
        refine ⟨14261221399746012040980487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19014961866328016054640649 14261221399746012040980487)
        ·
          refine ⟨21391832099619018061470731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14261221399746012040980487 21391832099619018061470731)
          ·
            refine ⟨32087748149428527092206097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21391832099619018061470731 32087748149428527092206097)
            ·
              refine ⟨24065811112071395319154573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32087748149428527092206097 24065811112071395319154573)
              ·
                refine ⟨9024679167026773244682965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24065811112071395319154573 9024679167026773244682965)
                ·
                  refine ⟨211515917977189997922257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9024679167026773244682965 211515917977189997922257)
                  ·
                    rfl

theorem cell21_926833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_926833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926833 prefixEnd_926833 := by exact prefixLift 926833
  have htrace : WordTrace (prefixWord ++ tailWord_926833) baseStart_926833 baseEnd_926833 := by
    simpa [prefixWord, tailWord_926833, baseEnd_926833] using wordTrace_append hprefix tailTrace_926833
  have hstable : (prefixWord ++ tailWord_926833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926833).length < 2 ^ (prefixWord ++ tailWord_926833).sum := by decide
  have hdescent : baseEnd_926833 < baseStart_926833 := by decide
  rcases family_descends (prefixWord ++ tailWord_926833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926881 : List Nat := [1, 2, 3, 3, 1, 1, 3, 3, 4]
def baseStart_926881 : Nat := 118140960795 + 926881 * 2 ^ 59
def prefixEnd_926881 : Nat := 4983230072969 + 3 ^ 40 * 926881 * 2
def baseEnd_926881 : Nat := 211526872231152581122159

theorem tailTrace_926881 : CollatzResearch.WordTrace tailWord_926881 prefixEnd_926881 211526872231152581122159 := by
  unfold tailWord_926881
  simp only [CollatzResearch.WordTrace]
  refine ⟨33806127355075910517108497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22537418236717273678072331 33806127355075910517108497)
  ·
    refine ⟨25354595516306932887831373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33806127355075910517108497 25354595516306932887831373)
    ·
      refine ⟨9507973318615099832936765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25354595516306932887831373 9507973318615099832936765)
      ·
        refine ⟨3565489994480662437351287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9507973318615099832936765 3565489994480662437351287)
        ·
          refine ⟨5348234991720993656026931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3565489994480662437351287 5348234991720993656026931)
          ·
            refine ⟨8022352487581490484040397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5348234991720993656026931 8022352487581490484040397)
            ·
              refine ⟨3008382182843058931515149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8022352487581490484040397 3008382182843058931515149)
              ·
                refine ⟨1128143318566147099318181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3008382182843058931515149 1128143318566147099318181)
                ·
                  refine ⟨211526872231152581122159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1128143318566147099318181 211526872231152581122159)
                  ·
                    rfl

theorem cell21_926881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_926881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926881 prefixEnd_926881 := by exact prefixLift 926881
  have htrace : WordTrace (prefixWord ++ tailWord_926881) baseStart_926881 baseEnd_926881 := by
    simpa [prefixWord, tailWord_926881, baseEnd_926881] using wordTrace_append hprefix tailTrace_926881
  have hstable : (prefixWord ++ tailWord_926881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926881).length < 2 ^ (prefixWord ++ tailWord_926881).sum := by decide
  have hdescent : baseEnd_926881 < baseStart_926881 := by decide
  rcases family_descends (prefixWord ++ tailWord_926881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926974 : List Nat := [4, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_926974 : Nat := 118140960795 + 926974 * 2 ^ 59
def prefixEnd_926974 : Nat := 4983230072969 + 3 ^ 40 * 926974 * 2
def baseEnd_926974 : Nat := 211548096098205086071969

theorem tailTrace_926974 : CollatzResearch.WordTrace tailWord_926974 prefixEnd_926974 211548096098205086071969 := by
  unfold tailWord_926974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4226189917967373425030497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22539679562492658266829317 4226189917967373425030497)
  ·
    refine ⟨3169642438475530068772873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4226189917967373425030497 3169642438475530068772873)
    ·
      refine ⟨2377231828856647551579655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3169642438475530068772873 2377231828856647551579655)
      ·
        refine ⟨3565847743284971327369483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2377231828856647551579655 3565847743284971327369483)
        ·
          refine ⟨5348771614927456991054225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3565847743284971327369483 5348771614927456991054225)
          ·
            refine ⟨4011578711195592743290669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5348771614927456991054225 4011578711195592743290669)
            ·
              refine ⟨1504342016698347278734001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4011578711195592743290669 1504342016698347278734001)
              ·
                refine ⟨1128256512523760459050501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1504342016698347278734001 1128256512523760459050501)
                ·
                  refine ⟨211548096098205086071969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1128256512523760459050501 211548096098205086071969)
                  ·
                    rfl

theorem cell21_926974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_926974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_926974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_926974 prefixEnd_926974 := by exact prefixLift 926974
  have htrace : WordTrace (prefixWord ++ tailWord_926974) baseStart_926974 baseEnd_926974 := by
    simpa [prefixWord, tailWord_926974, baseEnd_926974] using wordTrace_append hprefix tailTrace_926974
  have hstable : (prefixWord ++ tailWord_926974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926974).length < 2 ^ (prefixWord ++ tailWord_926974).sum := by decide
  have hdescent : baseEnd_926974 < baseStart_926974 := by decide
  rcases family_descends (prefixWord ++ tailWord_926974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927002 : List Nat := [3, 1, 1, 3, 3, 1, 2, 2, 5]
def baseStart_927002 : Nat := 118140960795 + 927002 * 2 ^ 59
def prefixEnd_927002 : Nat := 4983230072969 + 3 ^ 40 * 927002 * 2
def baseEnd_927002 : Nat := 211554486079683259605245

theorem tailTrace_927002 : CollatzResearch.WordTrace tailWord_927002 prefixEnd_927002 211554486079683259605245 := by
  unfold tailWord_927002
  simp only [CollatzResearch.WordTrace]
  refine ⟨8452635146909387045565815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22540360391758365454842173 8452635146909387045565815)
  ·
    refine ⟨12678952720364080568348723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8452635146909387045565815 12678952720364080568348723)
    ·
      refine ⟨19018429080546120852523085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12678952720364080568348723 19018429080546120852523085)
      ·
        refine ⟨7131910905204795319696157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19018429080546120852523085 7131910905204795319696157)
        ·
          refine ⟨2674466589451798244886059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7131910905204795319696157 2674466589451798244886059)
          ·
            refine ⟨4011699884177697367329089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2674466589451798244886059 4011699884177697367329089)
            ·
              refine ⟨3008774913133273025496817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4011699884177697367329089 3008774913133273025496817)
              ·
                refine ⟨2256581184849954769122613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3008774913133273025496817 2256581184849954769122613)
                ·
                  refine ⟨211554486079683259605245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2256581184849954769122613 211554486079683259605245)
                  ·
                    rfl

theorem cell21_927002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_927002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_927002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_927002 prefixEnd_927002 := by exact prefixLift 927002
  have htrace : WordTrace (prefixWord ++ tailWord_927002) baseStart_927002 baseEnd_927002 := by
    simpa [prefixWord, tailWord_927002, baseEnd_927002] using wordTrace_append hprefix tailTrace_927002
  have hstable : (prefixWord ++ tailWord_927002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927002).length < 2 ^ (prefixWord ++ tailWord_927002).sum := by decide
  have hdescent : baseEnd_927002 < baseStart_927002 := by decide
  rcases family_descends (prefixWord ++ tailWord_927002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927005 : List Nat := [1, 4, 2, 3, 1, 3, 2, 5]
def baseStart_927005 : Nat := 118140960795 + 927005 * 2 ^ 59
def prefixEnd_927005 : Nat := 4983230072969 + 3 ^ 40 * 927005 * 2
def baseEnd_927005 : Nat := 70518390240185307018413

theorem tailTrace_927005 : CollatzResearch.WordTrace tailWord_927005 prefixEnd_927005 70518390240185307018413 := by
  unfold tailWord_927005
  simp only [CollatzResearch.WordTrace]
  refine ⟨33810650006626679694622469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22540433337751119796414979 33810650006626679694622469)
  ·
    refine ⟨6339496876242502442741713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33810650006626679694622469 6339496876242502442741713)
    ·
      refine ⟨4754622657181876832056285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6339496876242502442741713 4754622657181876832056285)
      ·
        refine ⟨1782983496443203812021107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4754622657181876832056285 1782983496443203812021107)
        ·
          refine ⟨2674475244664805718031661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1782983496443203812021107 2674475244664805718031661)
          ·
            refine ⟨1002928216749302144261873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2674475244664805718031661 1002928216749302144261873)
            ·
              refine ⟨752196162561976608196405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1002928216749302144261873 752196162561976608196405)
              ·
                refine ⟨70518390240185307018413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 752196162561976608196405 70518390240185307018413)
                ·
                  rfl

theorem cell21_927005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 5].length) (baseStart_927005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_927005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_927005 prefixEnd_927005 := by exact prefixLift 927005
  have htrace : WordTrace (prefixWord ++ tailWord_927005) baseStart_927005 baseEnd_927005 := by
    simpa [prefixWord, tailWord_927005, baseEnd_927005] using wordTrace_append hprefix tailTrace_927005
  have hstable : (prefixWord ++ tailWord_927005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927005).length < 2 ^ (prefixWord ++ tailWord_927005).sum := by decide
  have hdescent : baseEnd_927005 < baseStart_927005 := by decide
  rcases family_descends (prefixWord ++ tailWord_927005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927036 : List Nat := [2, 2, 2, 2, 1, 4, 3, 2, 3]
def baseStart_927036 : Nat := 118140960795 + 927036 * 2 ^ 59
def prefixEnd_927036 : Nat := 4983230072969 + 3 ^ 40 * 927036 * 2
def baseEnd_927036 : Nat := 211562245342906756038509

theorem tailTrace_927036 : CollatzResearch.WordTrace tailWord_927036 prefixEnd_927036 211562245342906756038509 := by
  unfold tailWord_927036
  simp only [CollatzResearch.WordTrace]
  refine ⟨16905890334757185994500481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22541187113009581326000641 16905890334757185994500481)
  ·
    refine ⟨12679417751067889495875361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16905890334757185994500481 12679417751067889495875361)
    ·
      refine ⟨9509563313300917121906521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12679417751067889495875361 9509563313300917121906521)
      ·
        refine ⟨7132172484975687841429891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9509563313300917121906521 7132172484975687841429891)
        ·
          refine ⟨10698258727463531762144837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7132172484975687841429891 10698258727463531762144837)
          ·
            refine ⟨2005923511399412205402157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10698258727463531762144837 2005923511399412205402157)
            ·
              refine ⟨752221316774779577025809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2005923511399412205402157 752221316774779577025809)
              ·
                refine ⟨564165987581084682769357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 752221316774779577025809 564165987581084682769357)
                ·
                  refine ⟨211562245342906756038509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 564165987581084682769357 211562245342906756038509)
                  ·
                    rfl

theorem cell21_927036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_927036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_927036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_927036 prefixEnd_927036 := by exact prefixLift 927036
  have htrace : WordTrace (prefixWord ++ tailWord_927036) baseStart_927036 baseEnd_927036 := by
    simpa [prefixWord, tailWord_927036, baseEnd_927036] using wordTrace_append hprefix tailTrace_927036
  have hstable : (prefixWord ++ tailWord_927036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927036).length < 2 ^ (prefixWord ++ tailWord_927036).sum := by decide
  have hdescent : baseEnd_927036 < baseStart_927036 := by decide
  rcases family_descends (prefixWord ++ tailWord_927036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927047 : List Nat := [1, 1, 4, 1, 2, 4, 2, 6]
def baseStart_927047 : Nat := 118140960795 + 927047 * 2 ^ 59
def prefixEnd_927047 : Nat := 4983230072969 + 3 ^ 40 * 927047 * 2
def baseEnd_927047 : Nat := 70521585230924393785051

theorem tailTrace_927047 : CollatzResearch.WordTrace tailWord_927047 prefixEnd_927047 70521585230924393785051 := by
  unfold tailWord_927047
  simp only [CollatzResearch.WordTrace]
  refine ⟨33812181872474520867651395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22541454581649680578434263 33812181872474520867651395)
  ·
    refine ⟨50718272808711781301477093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33812181872474520867651395 50718272808711781301477093)
    ·
      refine ⟨9509676151633458994026955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50718272808711781301477093 9509676151633458994026955)
      ·
        refine ⟨14264514227450188491040433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9509676151633458994026955 14264514227450188491040433)
        ·
          refine ⟨10698385670587641368280325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14264514227450188491040433 10698385670587641368280325)
          ·
            refine ⟨2005947313235182756552561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10698385670587641368280325 2005947313235182756552561)
            ·
              refine ⟨1504460484926387067414421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2005947313235182756552561 1504460484926387067414421)
              ·
                refine ⟨70521585230924393785051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1504460484926387067414421 70521585230924393785051)
                ·
                  rfl

theorem cell21_927047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 6].length) (baseStart_927047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_927047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_927047 prefixEnd_927047 := by exact prefixLift 927047
  have htrace : WordTrace (prefixWord ++ tailWord_927047) baseStart_927047 baseEnd_927047 := by
    simpa [prefixWord, tailWord_927047, baseEnd_927047] using wordTrace_append hprefix tailTrace_927047
  have hstable : (prefixWord ++ tailWord_927047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927047).length < 2 ^ (prefixWord ++ tailWord_927047).sum := by decide
  have hdescent : baseEnd_927047 < baseStart_927047 := by decide
  rcases family_descends (prefixWord ++ tailWord_927047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927168 : List Nat := [2, 1, 1, 2, 3, 1, 2, 5, 4]
def baseStart_927168 : Nat := 118140960795 + 927168 * 2 ^ 59
def prefixEnd_927168 : Nat := 4983230072969 + 3 ^ 40 * 927168 * 2
def baseEnd_927168 : Nat := 211592369541303859838239

theorem tailTrace_927168 : CollatzResearch.WordTrace tailWord_927168 prefixEnd_927168 211592369541303859838239 := by
  unfold tailWord_927168
  simp only [CollatzResearch.WordTrace]
  refine ⟨16908297552518079266403079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22544396736690772355204105 16908297552518079266403079)
  ·
    refine ⟨25362446328777118899604619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16908297552518079266403079 25362446328777118899604619)
    ·
      refine ⟨38043669493165678349406929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25362446328777118899604619 38043669493165678349406929)
      ·
        refine ⟨28532752119874258762055197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38043669493165678349406929 28532752119874258762055197)
        ·
          refine ⟨10699782044952847035770699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28532752119874258762055197 10699782044952847035770699)
          ·
            refine ⟨16049673067429270553656049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10699782044952847035770699 16049673067429270553656049)
            ·
              refine ⟨12037254800571952915242037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16049673067429270553656049 12037254800571952915242037)
              ·
                refine ⟨1128492637553620585803941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12037254800571952915242037 1128492637553620585803941)
                ·
                  refine ⟨211592369541303859838239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1128492637553620585803941 211592369541303859838239)
                  ·
                    rfl

theorem cell21_927168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_927168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_927168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_927168 prefixEnd_927168 := by exact prefixLift 927168
  have htrace : WordTrace (prefixWord ++ tailWord_927168) baseStart_927168 baseEnd_927168 := by
    simpa [prefixWord, tailWord_927168, baseEnd_927168] using wordTrace_append hprefix tailTrace_927168
  have hstable : (prefixWord ++ tailWord_927168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927168).length < 2 ^ (prefixWord ++ tailWord_927168).sum := by decide
  have hdescent : baseEnd_927168 < baseStart_927168 := by decide
  rcases family_descends (prefixWord ++ tailWord_927168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927261 : List Nat := [1, 4, 2, 2, 1, 1, 4, 2, 4]
def baseStart_927261 : Nat := 118140960795 + 927261 * 2 ^ 59
def prefixEnd_927261 : Nat := 4983230072969 + 3 ^ 40 * 927261 * 2
def baseEnd_927261 : Nat := 211613593408356364788049

theorem tailTrace_927261 : CollatzResearch.WordTrace tailWord_927261 prefixEnd_927261 211613593408356364788049 := by
  unfold tailWord_927261
  simp only [CollatzResearch.WordTrace]
  refine ⟨33819987093699235415941637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22546658062466156943961091 33819987093699235415941637)
  ·
    refine ⟨6341247580068606640489057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33819987093699235415941637 6341247580068606640489057)
    ·
      refine ⟨4755935685051454980366793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6341247580068606640489057 4755935685051454980366793)
      ·
        refine ⟨3566951763788591235275095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4755935685051454980366793 3566951763788591235275095)
        ·
          refine ⟨5350427645682886852912643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3566951763788591235275095 5350427645682886852912643)
          ·
            refine ⟨8025641468524330279368965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5350427645682886852912643 8025641468524330279368965)
            ·
              refine ⟨1504807775348311927381681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8025641468524330279368965 1504807775348311927381681)
              ·
                refine ⟨1128605831511233945536261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1504807775348311927381681 1128605831511233945536261)
                ·
                  refine ⟨211613593408356364788049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1128605831511233945536261 211613593408356364788049)
                  ·
                    rfl

theorem cell21_927261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_927261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_927261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_927261 prefixEnd_927261 := by exact prefixLift 927261
  have htrace : WordTrace (prefixWord ++ tailWord_927261) baseStart_927261 baseEnd_927261 := by
    simpa [prefixWord, tailWord_927261, baseEnd_927261] using wordTrace_append hprefix tailTrace_927261
  have hstable : (prefixWord ++ tailWord_927261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927261).length < 2 ^ (prefixWord ++ tailWord_927261).sum := by decide
  have hdescent : baseEnd_927261 < baseStart_927261 := by decide
  rcases family_descends (prefixWord ++ tailWord_927261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927264 : List Nat := [2, 1, 1, 6, 1, 1, 4, 2, 3]
def baseStart_927264 : Nat := 118140960795 + 927264 * 2 ^ 59
def prefixEnd_927264 : Nat := 4983230072969 + 3 ^ 40 * 927264 * 2
def baseEnd_927264 : Nat := 211614278049229026238043

theorem tailTrace_927264 : CollatzResearch.WordTrace tailWord_927264 prefixEnd_927264 211614278049229026238043 := by
  unfold tailWord_927264
  simp only [CollatzResearch.WordTrace]
  refine ⟨16910048256344183464150423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22546731008458911285533897 16910048256344183464150423)
  ·
    refine ⟨25365072384516275196225635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16910048256344183464150423 25365072384516275196225635)
    ·
      refine ⟨38047608576774412794338453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25365072384516275196225635 38047608576774412794338453)
      ·
        refine ⟨1783481652036300599734615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38047608576774412794338453 1783481652036300599734615)
        ·
          refine ⟨2675222478054450899601923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1783481652036300599734615 2675222478054450899601923)
          ·
            refine ⟨4012833717081676349402885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675222478054450899601923 4012833717081676349402885)
            ·
              refine ⟨752406321952814315513041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4012833717081676349402885 752406321952814315513041)
              ·
                refine ⟨564304741464610736634781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 752406321952814315513041 564304741464610736634781)
                ·
                  refine ⟨211614278049229026238043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 564304741464610736634781 211614278049229026238043)
                  ·
                    rfl

theorem cell21_927264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 3].length) (baseStart_927264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_927264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_927264 prefixEnd_927264 := by exact prefixLift 927264
  have htrace : WordTrace (prefixWord ++ tailWord_927264) baseStart_927264 baseEnd_927264 := by
    simpa [prefixWord, tailWord_927264, baseEnd_927264] using wordTrace_append hprefix tailTrace_927264
  have hstable : (prefixWord ++ tailWord_927264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927264).length < 2 ^ (prefixWord ++ tailWord_927264).sum := by decide
  have hdescent : baseEnd_927264 < baseStart_927264 := by decide
  rcases family_descends (prefixWord ++ tailWord_927264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927289 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 7]
def baseStart_927289 : Nat := 118140960795 + 927289 * 2 ^ 59
def prefixEnd_927289 : Nat := 4983230072969 + 3 ^ 40 * 927289 * 2
def baseEnd_927289 : Nat := 211619983389834538321325

theorem tailTrace_927289 : CollatzResearch.WordTrace tailWord_927289 prefixEnd_927289 211619983389834538321325 := by
  unfold tailWord_927289
  simp only [CollatzResearch.WordTrace]
  refine ⟨33821008337597796197960921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22547338891731864131973947 33821008337597796197960921)
  ·
    refine ⟨25365756253198347148470691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33821008337597796197960921 25365756253198347148470691)
    ·
      refine ⟨38048634379797520722706037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25365756253198347148470691 38048634379797520722706037)
      ·
        refine ⟨3567059473106017567753691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38048634379797520722706037 3567059473106017567753691)
        ·
          refine ⟨5350589209659026351630537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3567059473106017567753691 5350589209659026351630537)
          ·
            refine ⟨4012941907244269763722903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5350589209659026351630537 4012941907244269763722903)
            ·
              refine ⟨6019412860866404645584355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012941907244269763722903 6019412860866404645584355)
              ·
                refine ⟨9029119291299606968376533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6019412860866404645584355 9029119291299606968376533)
                ·
                  refine ⟨211619983389834538321325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9029119291299606968376533 211619983389834538321325)
                  ·
                    rfl

theorem cell21_927289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_927289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_927289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_927289 prefixEnd_927289 := by exact prefixLift 927289
  have htrace : WordTrace (prefixWord ++ tailWord_927289) baseStart_927289 baseEnd_927289 := by
    simpa [prefixWord, tailWord_927289, baseEnd_927289] using wordTrace_append hprefix tailTrace_927289
  have hstable : (prefixWord ++ tailWord_927289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927289).length < 2 ^ (prefixWord ++ tailWord_927289).sum := by decide
  have hdescent : baseEnd_927289 < baseStart_927289 := by decide
  rcases family_descends (prefixWord ++ tailWord_927289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927292 : List Nat := [2, 2, 2, 2, 4, 1, 3, 5]
def baseStart_927292 : Nat := 118140960795 + 927292 * 2 ^ 59
def prefixEnd_927292 : Nat := 4983230072969 + 3 ^ 40 * 927292 * 2
def baseEnd_927292 : Nat := 70540222676902399923773

theorem tailTrace_927292 : CollatzResearch.WordTrace tailWord_927292 prefixEnd_927292 70540222676902399923773 := by
  unfold tailWord_927292
  simp only [CollatzResearch.WordTrace]
  refine ⟨16910558878293463855160065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22547411837724618473546753 16910558878293463855160065)
  ·
    refine ⟨12682919158720097891370049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16910558878293463855160065 12682919158720097891370049)
    ·
      refine ⟨9512189369040073418527537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12682919158720097891370049 9512189369040073418527537)
      ·
        refine ⟨7134142026780055063895653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9512189369040073418527537 7134142026780055063895653)
        ·
          refine ⟨1337651630021260324480435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7134142026780055063895653 1337651630021260324480435)
          ·
            refine ⟨2006477445031890486720653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337651630021260324480435 2006477445031890486720653)
            ·
              refine ⟨752429041886958932520245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2006477445031890486720653 752429041886958932520245)
              ·
                refine ⟨70540222676902399923773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 752429041886958932520245 70540222676902399923773)
                ·
                  rfl

theorem cell21_927292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 5].length) (baseStart_927292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_927292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_927292 prefixEnd_927292 := by exact prefixLift 927292
  have htrace : WordTrace (prefixWord ++ tailWord_927292) baseStart_927292 baseEnd_927292 := by
    simpa [prefixWord, tailWord_927292, baseEnd_927292] using wordTrace_append hprefix tailTrace_927292
  have hstable : (prefixWord ++ tailWord_927292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927292).length < 2 ^ (prefixWord ++ tailWord_927292).sum := by decide
  have hdescent : baseEnd_927292 < baseStart_927292 := by decide
  rcases family_descends (prefixWord ++ tailWord_927292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927368 : List Nat := [2, 1, 3, 5, 1, 2, 7]
def baseStart_927368 : Nat := 118140960795 + 927368 * 2 ^ 59
def prefixEnd_927368 : Nat := 4983230072969 + 3 ^ 40 * 927368 * 2
def baseEnd_927368 : Nat := 23515334696238661833833

theorem tailTrace_927368 : CollatzResearch.WordTrace tailWord_927368 prefixEnd_927368 23515334696238661833833 := by
  unfold tailWord_927368
  simp only [CollatzResearch.WordTrace]
  refine ⟨16911944852155796345043379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22549259802874395126724505 16911944852155796345043379)
  ·
    refine ⟨25367917278233694517565069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16911944852155796345043379 25367917278233694517565069)
    ·
      refine ⟨9512968979337635444086901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25367917278233694517565069 9512968979337635444086901)
      ·
        refine ⟨891840841812903322883147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9512968979337635444086901 891840841812903322883147)
        ·
          refine ⟨1337761262719354984324721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891840841812903322883147 1337761262719354984324721)
          ·
            refine ⟨1003320947039516238243541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1337761262719354984324721 1003320947039516238243541)
            ·
              refine ⟨23515334696238661833833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1003320947039516238243541 23515334696238661833833)
              ·
                rfl

theorem cell21_927368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 7].length) (baseStart_927368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_927368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_927368 prefixEnd_927368 := by exact prefixLift 927368
  have htrace : WordTrace (prefixWord ++ tailWord_927368) baseStart_927368 baseEnd_927368 := by
    simpa [prefixWord, tailWord_927368, baseEnd_927368] using wordTrace_append hprefix tailTrace_927368
  have hstable : (prefixWord ++ tailWord_927368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927368).length < 2 ^ (prefixWord ++ tailWord_927368).sum := by decide
  have hdescent : baseEnd_927368 < baseStart_927368 := by decide
  rcases family_descends (prefixWord ++ tailWord_927368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927410 : List Nat := [3, 2, 1, 1, 1, 2, 4, 7]
def baseStart_927410 : Nat := 118140960795 + 927410 * 2 ^ 59
def prefixEnd_927410 : Nat := 4983230072969 + 3 ^ 40 * 927410 * 2
def baseEnd_927410 : Nat := 70549199079455072268137

theorem tailTrace_927410 : CollatzResearch.WordTrace tailWord_927410 prefixEnd_927410 70549199079455072268137 := by
  unfold tailWord_927410
  simp only [CollatzResearch.WordTrace]
  refine ⟨8456355392539858465778921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22550281046772955908743789 8456355392539858465778921)
  ·
    refine ⟨6342266544404893849334191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8456355392539858465778921 6342266544404893849334191)
    ·
      refine ⟨9513399816607340774001287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6342266544404893849334191 9513399816607340774001287)
      ·
        refine ⟨14270099724911011161001931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9513399816607340774001287 14270099724911011161001931)
        ·
          refine ⟨21405149587366516741502897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14270099724911011161001931 21405149587366516741502897)
          ·
            refine ⟨16053862190524887556127173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21405149587366516741502897 16053862190524887556127173)
            ·
              refine ⟨3010099160723416416773845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16053862190524887556127173 3010099160723416416773845)
              ·
                refine ⟨70549199079455072268137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3010099160723416416773845 70549199079455072268137)
                ·
                  rfl

theorem cell21_927410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_927410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_927410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_927410 prefixEnd_927410 := by exact prefixLift 927410
  have htrace : WordTrace (prefixWord ++ tailWord_927410) baseStart_927410 baseEnd_927410 := by
    simpa [prefixWord, tailWord_927410, baseEnd_927410] using wordTrace_append hprefix tailTrace_927410
  have hstable : (prefixWord ++ tailWord_927410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927410).length < 2 ^ (prefixWord ++ tailWord_927410).sum := by decide
  have hdescent : baseEnd_927410 < baseStart_927410 := by decide
  rcases family_descends (prefixWord ++ tailWord_927410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927444 : List Nat := [2, 4, 1, 3, 1, 3, 1, 6]
def baseStart_927444 : Nat := 118140960795 + 927444 * 2 ^ 59
def prefixEnd_927444 : Nat := 4983230072969 + 3 ^ 40 * 927444 * 2
def baseEnd_927444 : Nat := 70551785500529571079225

theorem tailTrace_927444 : CollatzResearch.WordTrace tailWord_927444 prefixEnd_927444 70551785500529571079225 := by
  unfold tailWord_927444
  simp only [CollatzResearch.WordTrace]
  refine ⟨16913330826018128834926693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22551107768024171779902257 16913330826018128834926693)
  ·
    refine ⟨3171249529878399156548755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16913330826018128834926693 3171249529878399156548755)
    ·
      refine ⟨4756874294817598734823133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3171249529878399156548755 4756874294817598734823133)
      ·
        refine ⟨1783827860556599525558675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4756874294817598734823133 1783827860556599525558675)
        ·
          refine ⟨2675741790834899288338013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1783827860556599525558675 2675741790834899288338013)
          ·
            refine ⟨1003403171563087233126755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2675741790834899288338013 1003403171563087233126755)
            ·
              refine ⟨1505104757344630849690133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003403171563087233126755 1505104757344630849690133)
              ·
                refine ⟨70551785500529571079225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1505104757344630849690133 70551785500529571079225)
                ·
                  rfl

theorem cell21_927444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 6].length) (baseStart_927444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_927444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_927444 prefixEnd_927444 := by exact prefixLift 927444
  have htrace : WordTrace (prefixWord ++ tailWord_927444) baseStart_927444 baseEnd_927444 := by
    simpa [prefixWord, tailWord_927444, baseEnd_927444] using wordTrace_append hprefix tailTrace_927444
  have hstable : (prefixWord ++ tailWord_927444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927444).length < 2 ^ (prefixWord ++ tailWord_927444).sum := by decide
  have hdescent : baseEnd_927444 < baseStart_927444 := by decide
  rcases family_descends (prefixWord ++ tailWord_927444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927551 : List Nat := [1, 1, 2, 2, 7, 1, 1, 1, 5]
def baseStart_927551 : Nat := 118140960795 + 927551 * 2 ^ 59
def prefixEnd_927551 : Nat := 4983230072969 + 3 ^ 40 * 927551 * 2
def baseEnd_927551 : Nat := 211679775359380304954123

theorem tailTrace_927551 : CollatzResearch.WordTrace tailWord_927551 prefixEnd_927551 211679775359380304954123 := by
  unfold tailWord_927551
  simp only [CollatzResearch.WordTrace]
  refine ⟨33830564262648614943998507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22553709508432409962665671 33830564262648614943998507)
  ·
    refine ⟨50745846393972922415997761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33830564262648614943998507 50745846393972922415997761)
    ·
      refine ⟨38059384795479691811998321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50745846393972922415997761 38059384795479691811998321)
      ·
        refine ⟨28544538596609768858998741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38059384795479691811998321 28544538596609768858998741)
        ·
          refine ⟨669012623358041457632783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 28544538596609768858998741 669012623358041457632783)
          ·
            refine ⟨1003518935037062186449175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669012623358041457632783 1003518935037062186449175)
            ·
              refine ⟨1505278402555593279673763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003518935037062186449175 1505278402555593279673763)
              ·
                refine ⟨2257917603833389919510645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1505278402555593279673763 2257917603833389919510645)
                ·
                  refine ⟨211679775359380304954123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2257917603833389919510645 211679775359380304954123)
                  ·
                    rfl

theorem cell21_927551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 5].length) (baseStart_927551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_927551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_927551 prefixEnd_927551 := by exact prefixLift 927551
  have htrace : WordTrace (prefixWord ++ tailWord_927551) baseStart_927551 baseEnd_927551 := by
    simpa [prefixWord, tailWord_927551, baseEnd_927551] using wordTrace_append hprefix tailTrace_927551
  have hstable : (prefixWord ++ tailWord_927551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927551).length < 2 ^ (prefixWord ++ tailWord_927551).sum := by decide
  have hdescent : baseEnd_927551 < baseStart_927551 := by decide
  rcases family_descends (prefixWord ++ tailWord_927551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927562 : List Nat := [3, 1, 2, 1, 1, 1, 6, 6]
def baseStart_927562 : Nat := 118140960795 + 927562 * 2 ^ 59
def prefixEnd_927562 : Nat := 4983230072969 + 3 ^ 40 * 927562 * 2
def baseEnd_927562 : Nat := 70560761903082243423589

theorem tailTrace_927562 : CollatzResearch.WordTrace tailWord_927562 prefixEnd_927562 70560761903082243423589 := by
  unfold tailWord_927562
  simp only [CollatzResearch.WordTrace]
  refine ⟨8457741366402190955662235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22553976977072509215099293 8457741366402190955662235)
  ·
    refine ⟨12686612049603286433493353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8457741366402190955662235 12686612049603286433493353)
    ·
      refine ⟨9514959037202464825120015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12686612049603286433493353 9514959037202464825120015)
      ·
        refine ⟨14272438555803697237680023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9514959037202464825120015 14272438555803697237680023)
        ·
          refine ⟨21408657833705545856520035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14272438555803697237680023 21408657833705545856520035)
          ·
            refine ⟨32112986750558318784780053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21408657833705545856520035 32112986750558318784780053)
            ·
              refine ⟨1505296253932421193036565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32112986750558318784780053 1505296253932421193036565)
              ·
                refine ⟨70560761903082243423589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1505296253932421193036565 70560761903082243423589)
                ·
                  rfl

theorem cell21_927562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_927562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_927562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_927562 prefixEnd_927562 := by exact prefixLift 927562
  have htrace : WordTrace (prefixWord ++ tailWord_927562) baseStart_927562 baseEnd_927562 := by
    simpa [prefixWord, tailWord_927562, baseEnd_927562] using wordTrace_append hprefix tailTrace_927562
  have hstable : (prefixWord ++ tailWord_927562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927562).length < 2 ^ (prefixWord ++ tailWord_927562).sum := by decide
  have hdescent : baseEnd_927562 < baseStart_927562 := by decide
  rcases family_descends (prefixWord ++ tailWord_927562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927669 : List Nat := [1, 3, 3, 2, 1, 2, 1, 3, 5]
def baseStart_927669 : Nat := 118140960795 + 927669 * 2 ^ 59
def prefixEnd_927669 : Nat := 4983230072969 + 3 ^ 40 * 927669 * 2
def baseEnd_927669 : Nat := 211706704567038321987215

theorem tailTrace_927669 : CollatzResearch.WordTrace tailWord_927669 prefixEnd_927669 211706704567038321987215 := by
  unfold tailWord_927669
  simp only [CollatzResearch.WordTrace]
  refine ⟨33834868076221121096794061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22556578717480747397862707 33834868076221121096794061)
  ·
    refine ⟨12688075528582920411297773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33834868076221121096794061 12688075528582920411297773)
    ·
      refine ⟨4758028323218595154236665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12688075528582920411297773 4758028323218595154236665)
      ·
        refine ⟨3568521242413946365677499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4758028323218595154236665 3568521242413946365677499)
        ·
          refine ⟨5352781863620919548516249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3568521242413946365677499 5352781863620919548516249)
          ·
            refine ⟨4014586397715689661387187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5352781863620919548516249 4014586397715689661387187)
            ·
              refine ⟨6021879596573534492080781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4014586397715689661387187 6021879596573534492080781)
              ·
                refine ⟨2258204848715075434530293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6021879596573534492080781 2258204848715075434530293)
                ·
                  refine ⟨211706704567038321987215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2258204848715075434530293 211706704567038321987215)
                  ·
                    rfl

theorem cell21_927669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_927669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_927669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_927669 prefixEnd_927669 := by exact prefixLift 927669
  have htrace : WordTrace (prefixWord ++ tailWord_927669) baseStart_927669 baseEnd_927669 := by
    simpa [prefixWord, tailWord_927669, baseEnd_927669] using wordTrace_append hprefix tailTrace_927669
  have hstable : (prefixWord ++ tailWord_927669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927669).length < 2 ^ (prefixWord ++ tailWord_927669).sum := by decide
  have hdescent : baseEnd_927669 < baseStart_927669 := by decide
  rcases family_descends (prefixWord ++ tailWord_927669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927821 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 7]
def baseStart_927821 : Nat := 118140960795 + 927821 * 2 ^ 59
def prefixEnd_927821 : Nat := 4983230072969 + 3 ^ 40 * 927821 * 2
def baseEnd_927821 : Nat := 211741393037919835453571

theorem tailTrace_927821 : CollatzResearch.WordTrace tailWord_927821 prefixEnd_927821 211741393037919835453571 := by
  unfold tailWord_927821
  simp only [CollatzResearch.WordTrace]
  refine ⟨33840411971670451056327317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22560274647780300704218211 33840411971670451056327317)
  ·
    refine ⟨1586269311172052393265343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33840411971670451056327317 1586269311172052393265343)
    ·
      refine ⟨2379403966758078589898015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1586269311172052393265343 2379403966758078589898015)
      ·
        refine ⟨3569105950137117884847023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2379403966758078589898015 3569105950137117884847023)
        ·
          refine ⟨5353658925205676827270535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3569105950137117884847023 5353658925205676827270535)
          ·
            refine ⟨8030488387808515240905803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5353658925205676827270535 8030488387808515240905803)
            ·
              refine ⟨12045732581712772861358705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8030488387808515240905803 12045732581712772861358705)
              ·
                refine ⟨9034299436284579646019029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12045732581712772861358705 9034299436284579646019029)
                ·
                  refine ⟨211741393037919835453571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9034299436284579646019029 211741393037919835453571)
                  ·
                    rfl

theorem cell21_927821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_927821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_927821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_927821 prefixEnd_927821 := by exact prefixLift 927821
  have htrace : WordTrace (prefixWord ++ tailWord_927821) baseStart_927821 baseEnd_927821 := by
    simpa [prefixWord, tailWord_927821, baseEnd_927821] using wordTrace_append hprefix tailTrace_927821
  have hstable : (prefixWord ++ tailWord_927821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927821).length < 2 ^ (prefixWord ++ tailWord_927821).sum := by decide
  have hdescent : baseEnd_927821 < baseStart_927821 := by decide
  rcases family_descends (prefixWord ++ tailWord_927821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927849 : List Nat := [1, 2, 1, 1, 1, 5, 2, 8]
def baseStart_927849 : Nat := 118140960795 + 927849 * 2 ^ 59
def prefixEnd_927849 : Nat := 4983230072969 + 3 ^ 40 * 927849 * 2
def baseEnd_927849 : Nat := 70582594339799336328949

theorem tailTrace_927849 : CollatzResearch.WordTrace tailWord_927849 prefixEnd_927849 70582594339799336328949 := by
  unfold tailWord_927849
  simp only [CollatzResearch.WordTrace]
  refine ⟨33841433215569011838346601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22560955477046007892231067 33841433215569011838346601)
  ·
    refine ⟨25381074911676758878759951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33841433215569011838346601 25381074911676758878759951)
    ·
      refine ⟨38071612367515138318139927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25381074911676758878759951 38071612367515138318139927)
      ·
        refine ⟨57107418551272707477209891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38071612367515138318139927 57107418551272707477209891)
        ·
          refine ⟨85661127826909061215814837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57107418551272707477209891 85661127826909061215814837)
          ·
            refine ⟨8030730733772724488982641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85661127826909061215814837 8030730733772724488982641)
            ·
              refine ⟨6023048050329543366736981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8030730733772724488982641 6023048050329543366736981)
              ·
                refine ⟨70582594339799336328949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6023048050329543366736981 70582594339799336328949)
                ·
                  rfl

theorem cell21_927849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 8].length) (baseStart_927849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_927849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_927849 prefixEnd_927849 := by exact prefixLift 927849
  have htrace : WordTrace (prefixWord ++ tailWord_927849) baseStart_927849 baseEnd_927849 := by
    simpa [prefixWord, tailWord_927849, baseEnd_927849] using wordTrace_append hprefix tailTrace_927849
  have hstable : (prefixWord ++ tailWord_927849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927849).length < 2 ^ (prefixWord ++ tailWord_927849).sum := by decide
  have hdescent : baseEnd_927849 < baseStart_927849 := by decide
  rcases family_descends (prefixWord ++ tailWord_927849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927897 : List Nat := [1, 2, 1, 2, 1, 2, 1, 8, 3]
def baseStart_927897 : Nat := 118140960795 + 927897 * 2 ^ 59
def prefixEnd_927897 : Nat := 4983230072969 + 3 ^ 40 * 927897 * 2
def baseEnd_927897 : Nat := 211758737273360592186749

theorem tailTrace_927897 : CollatzResearch.WordTrace tailWord_927897 prefixEnd_927897 211758737273360592186749 := by
  unfold tailWord_927897
  simp only [CollatzResearch.WordTrace]
  refine ⟨33843183919395116036093945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22562122612930077357395963 33843183919395116036093945)
  ·
    refine ⟨25382387939546337027070459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33843183919395116036093945 25382387939546337027070459)
    ·
      refine ⟨38073581909319505540605689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25382387939546337027070459 38073581909319505540605689)
      ·
        refine ⟨28555186431989629155454267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38073581909319505540605689 28555186431989629155454267)
        ·
          refine ⟨42832779647984443733181401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28555186431989629155454267 42832779647984443733181401)
          ·
            refine ⟨32124584735988332799886051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42832779647984443733181401 32124584735988332799886051)
            ·
              refine ⟨48186877103982499199829077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32124584735988332799886051 48186877103982499199829077)
              ·
                refine ⟨564689966062294912497997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 48186877103982499199829077 564689966062294912497997)
                ·
                  refine ⟨211758737273360592186749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 564689966062294912497997 211758737273360592186749)
                  ·
                    rfl

theorem cell21_927897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 3].length) (baseStart_927897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_927897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_927897 prefixEnd_927897 := by exact prefixLift 927897
  have htrace : WordTrace (prefixWord ++ tailWord_927897) baseStart_927897 baseEnd_927897 := by
    simpa [prefixWord, tailWord_927897, baseEnd_927897] using wordTrace_append hprefix tailTrace_927897
  have hstable : (prefixWord ++ tailWord_927897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927897).length < 2 ^ (prefixWord ++ tailWord_927897).sum := by decide
  have hdescent : baseEnd_927897 < baseStart_927897 := by decide
  rcases family_descends (prefixWord ++ tailWord_927897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927973 : List Nat := [1, 3, 1, 4, 2, 2, 1, 2, 5]
def baseStart_927973 : Nat := 118140960795 + 927973 * 2 ^ 59
def prefixEnd_927973 : Nat := 4983230072969 + 3 ^ 40 * 927973 * 2
def baseEnd_927973 : Nat := 211776081508801348919927

theorem tailTrace_927973 : CollatzResearch.WordTrace tailWord_927973 prefixEnd_927973 211776081508801348919927 := by
  unfold tailWord_927973
  simp only [CollatzResearch.WordTrace]
  refine ⟨33845955867119781015860573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22563970578079854010573715 33845955867119781015860573)
  ·
    refine ⟨12692233450169917880947715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33845955867119781015860573 12692233450169917880947715)
    ·
      refine ⟨19038350175254876821421573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12692233450169917880947715 19038350175254876821421573)
      ·
        refine ⟨3569690657860289404016545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19038350175254876821421573 3569690657860289404016545)
        ·
          refine ⟨2677267993395217053012409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3569690657860289404016545 2677267993395217053012409)
          ·
            refine ⟨2007950995046412789759307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2677267993395217053012409 2007950995046412789759307)
            ·
              refine ⟨3011926492569619184638961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2007950995046412789759307 3011926492569619184638961)
              ·
                refine ⟨2258944869427214388479221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3011926492569619184638961 2258944869427214388479221)
                ·
                  refine ⟨211776081508801348919927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2258944869427214388479221 211776081508801348919927)
                  ·
                    rfl

theorem cell21_927973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_927973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_927973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_927973 prefixEnd_927973 := by exact prefixLift 927973
  have htrace : WordTrace (prefixWord ++ tailWord_927973) baseStart_927973 baseEnd_927973 := by
    simpa [prefixWord, tailWord_927973, baseEnd_927973] using wordTrace_append hprefix tailTrace_927973
  have hstable : (prefixWord ++ tailWord_927973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927973).length < 2 ^ (prefixWord ++ tailWord_927973).sum := by decide
  have hdescent : baseEnd_927973 < baseStart_927973 := by decide
  rcases family_descends (prefixWord ++ tailWord_927973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927990 : List Nat := [5, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_927990 : Nat := 118140960795 + 927990 * 2 ^ 59
def prefixEnd_927990 : Nat := 4983230072969 + 3 ^ 40 * 927990 * 2
def baseEnd_927990 : Nat := 211779961140413097136559

theorem tailTrace_927990 : CollatzResearch.WordTrace tailWord_927990 prefixEnd_927990 211779961140413097136559 := by
  unfold tailWord_927990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2115410994253637057451839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22564383938705461946152949 2115410994253637057451839)
  ·
    refine ⟨3173116491380455586177759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2115410994253637057451839 3173116491380455586177759)
    ·
      refine ⟨4759674737070683379266639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3173116491380455586177759 4759674737070683379266639)
      ·
        refine ⟨7139512105606025068899959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4759674737070683379266639 7139512105606025068899959)
        ·
          refine ⟨10709268158409037603349939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7139512105606025068899959 10709268158409037603349939)
          ·
            refine ⟨16063902237613556405024909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10709268158409037603349939 16063902237613556405024909)
            ·
              refine ⟨6023963339105083651884341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16063902237613556405024909 6023963339105083651884341)
              ·
                refine ⟨564746563041101592364157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6023963339105083651884341 564746563041101592364157)
                ·
                  refine ⟨211779961140413097136559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 564746563041101592364157 211779961140413097136559)
                  ·
                    rfl

theorem cell21_927990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_927990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_927990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_927990 prefixEnd_927990 := by exact prefixLift 927990
  have htrace : WordTrace (prefixWord ++ tailWord_927990) baseStart_927990 baseEnd_927990 := by
    simpa [prefixWord, tailWord_927990, baseEnd_927990] using wordTrace_append hprefix tailTrace_927990
  have hstable : (prefixWord ++ tailWord_927990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927990).length < 2 ^ (prefixWord ++ tailWord_927990).sum := by decide
  have hdescent : baseEnd_927990 < baseStart_927990 := by decide
  rcases family_descends (prefixWord ++ tailWord_927990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928001 : List Nat := [1, 2, 4, 1, 1, 2, 10]
def baseStart_928001 : Nat := 118140960795 + 928001 * 2 ^ 59
def prefixEnd_928001 : Nat := 4983230072969 + 3 ^ 40 * 928001 * 2
def baseEnd_928001 : Nat := 23531385721142169161467

theorem tailTrace_928001 : CollatzResearch.WordTrace tailWord_928001 prefixEnd_928001 23531385721142169161467 := by
  unfold tailWord_928001
  simp only [CollatzResearch.WordTrace]
  refine ⟨33846977111018341797879857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22564651407345561198586571 33846977111018341797879857)
  ·
    refine ⟨25385232833263756348409893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33846977111018341797879857 25385232833263756348409893)
    ·
      refine ⟨4759731156236954315326855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25385232833263756348409893 4759731156236954315326855)
      ·
        refine ⟨7139596734355431472990283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4759731156236954315326855 7139596734355431472990283)
        ·
          refine ⟨10709395101533147209485425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7139596734355431472990283 10709395101533147209485425)
          ·
            refine ⟨8032046326149860407114069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10709395101533147209485425 8032046326149860407114069)
            ·
              refine ⟨23531385721142169161467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8032046326149860407114069 23531385721142169161467)
              ·
                rfl

theorem cell21_928001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 10].length) (baseStart_928001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928001 prefixEnd_928001 := by exact prefixLift 928001
  have htrace : WordTrace (prefixWord ++ tailWord_928001) baseStart_928001 baseEnd_928001 := by
    simpa [prefixWord, tailWord_928001, baseEnd_928001] using wordTrace_append hprefix tailTrace_928001
  have hstable : (prefixWord ++ tailWord_928001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928001).length < 2 ^ (prefixWord ++ tailWord_928001).sum := by decide
  have hdescent : baseEnd_928001 < baseStart_928001 := by decide
  rcases family_descends (prefixWord ++ tailWord_928001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928004 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 6]
def baseStart_928004 : Nat := 118140960795 + 928004 * 2 ^ 59
def prefixEnd_928004 : Nat := 4983230072969 + 3 ^ 40 * 928004 * 2
def baseEnd_928004 : Nat := 211783156131152183903197

theorem tailTrace_928004 : CollatzResearch.WordTrace tailWord_928004 prefixEnd_928004 211783156131152183903197 := by
  unfold tailWord_928004
  simp only [CollatzResearch.WordTrace]
  refine ⟨16923543265003736655119533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22564724353338315540159377 16923543265003736655119533)
  ·
    refine ⟨6346328724376401245669825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16923543265003736655119533 6346328724376401245669825)
    ·
      refine ⟨4759746543282300934252369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6346328724376401245669825 4759746543282300934252369)
      ·
        refine ⟨3569809907461725700689277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4759746543282300934252369 3569809907461725700689277)
        ·
          refine ⟨1338678715298147137758479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3569809907461725700689277 1338678715298147137758479)
          ·
            refine ⟨2008018072947220706637719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338678715298147137758479 2008018072947220706637719)
            ·
              refine ⟨3012027109420831059956579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008018072947220706637719 3012027109420831059956579)
              ·
                refine ⟨4518040664131246589934869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012027109420831059956579 4518040664131246589934869)
                ·
                  refine ⟨211783156131152183903197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4518040664131246589934869 211783156131152183903197)
                  ·
                    rfl

theorem cell21_928004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_928004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928004 prefixEnd_928004 := by exact prefixLift 928004
  have htrace : WordTrace (prefixWord ++ tailWord_928004) baseStart_928004 baseEnd_928004 := by
    simpa [prefixWord, tailWord_928004, baseEnd_928004] using wordTrace_append hprefix tailTrace_928004
  have hstable : (prefixWord ++ tailWord_928004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928004).length < 2 ^ (prefixWord ++ tailWord_928004).sum := by decide
  have hdescent : baseEnd_928004 < baseStart_928004 := by decide
  rcases family_descends (prefixWord ++ tailWord_928004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928063 : List Nat := [1, 1, 2, 2, 4, 1, 2, 4, 4]
def baseStart_928063 : Nat := 118140960795 + 928063 * 2 ^ 59
def prefixEnd_928063 : Nat := 4983230072969 + 3 ^ 40 * 928063 * 2
def baseEnd_928063 : Nat := 211796620734981192419743

theorem tailTrace_928063 : CollatzResearch.WordTrace tailWord_928063 prefixEnd_928063 211796620734981192419743 := by
  unfold tailWord_928063
  simp only [CollatzResearch.WordTrace]
  refine ⟨33849238436793726386636843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22566158957862484257757895 33849238436793726386636843)
  ·
    refine ⟨50773857655190589579955265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33849238436793726386636843 50773857655190589579955265)
    ·
      refine ⟨38080393241392942184966449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50773857655190589579955265 38080393241392942184966449)
      ·
        refine ⟨28560294931044706638724837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38080393241392942184966449 28560294931044706638724837)
        ·
          refine ⟨5355055299570882494760907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28560294931044706638724837 5355055299570882494760907)
          ·
            refine ⟨8032582949356323742141361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5355055299570882494760907 8032582949356323742141361)
            ·
              refine ⟨6024437212017242806606021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8032582949356323742141361 6024437212017242806606021)
              ·
                refine ⟨1129581977253233026238629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6024437212017242806606021 1129581977253233026238629)
                ·
                  refine ⟨211796620734981192419743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1129581977253233026238629 211796620734981192419743)
                  ·
                    rfl

theorem cell21_928063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 4].length) (baseStart_928063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928063 prefixEnd_928063 := by exact prefixLift 928063
  have htrace : WordTrace (prefixWord ++ tailWord_928063) baseStart_928063 baseEnd_928063 := by
    simpa [prefixWord, tailWord_928063, baseEnd_928063] using wordTrace_append hprefix tailTrace_928063
  have hstable : (prefixWord ++ tailWord_928063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928063).length < 2 ^ (prefixWord ++ tailWord_928063).sum := by decide
  have hdescent : baseEnd_928063 < baseStart_928063 := by decide
  rcases family_descends (prefixWord ++ tailWord_928063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928080 : List Nat := [2, 1, 1, 1, 1, 6, 4, 1, 4]
def baseStart_928080 : Nat := 118140960795 + 928080 * 2 ^ 59
def prefixEnd_928080 : Nat := 4983230072969 + 3 ^ 40 * 928080 * 2
def baseEnd_928080 : Nat := 211800500366592940636375

theorem tailTrace_928080 : CollatzResearch.WordTrace tailWord_928080 prefixEnd_928080 211800500366592940636375 := by
  unfold tailWord_928080
  simp only [CollatzResearch.WordTrace]
  refine ⟨16924929238866069145002847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22566572318488092193337129 16924929238866069145002847)
  ·
    refine ⟨25387393858299103717504271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16924929238866069145002847 25387393858299103717504271)
    ·
      refine ⟨38081090787448655576256407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25387393858299103717504271 38081090787448655576256407)
      ·
        refine ⟨57121636181172983364384611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38081090787448655576256407 57121636181172983364384611)
        ·
          refine ⟨85682454271759475046576917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57121636181172983364384611 85682454271759475046576917)
          ·
            refine ⟨4016365043988725392808293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85682454271759475046576917 4016365043988725392808293)
            ·
              refine ⟨753068445747886011151555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4016365043988725392808293 753068445747886011151555)
              ·
                refine ⟨1129602668621829016727333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753068445747886011151555 1129602668621829016727333)
                ·
                  refine ⟨211800500366592940636375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1129602668621829016727333 211800500366592940636375)
                  ·
                    rfl

theorem cell21_928080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 4].length) (baseStart_928080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928080 prefixEnd_928080 := by exact prefixLift 928080
  have htrace : WordTrace (prefixWord ++ tailWord_928080) baseStart_928080 baseEnd_928080 := by
    simpa [prefixWord, tailWord_928080, baseEnd_928080] using wordTrace_append hprefix tailTrace_928080
  have hstable : (prefixWord ++ tailWord_928080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928080).length < 2 ^ (prefixWord ++ tailWord_928080).sum := by decide
  have hdescent : baseEnd_928080 < baseStart_928080 := by decide
  rcases family_descends (prefixWord ++ tailWord_928080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928139 : List Nat := [1, 1, 1, 1, 4, 4, 2, 3, 4]
def baseStart_928139 : Nat := 118140960795 + 928139 * 2 ^ 59
def prefixEnd_928139 : Nat := 4983230072969 + 3 ^ 40 * 928139 * 2
def baseEnd_928139 : Nat := 211813964970421949152921

theorem tailTrace_928139 : CollatzResearch.WordTrace tailWord_928139 prefixEnd_928139 211813964970421949152921 := by
  unfold tailWord_928139
  simp only [CollatzResearch.WordTrace]
  refine ⟨33852010384518391366403471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22568006923012260910935647 33852010384518391366403471)
  ·
    refine ⟨50778015576777587049605207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33852010384518391366403471 50778015576777587049605207)
    ·
      refine ⟨76167023365166380574407811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50778015576777587049605207 76167023365166380574407811)
      ·
        refine ⟨114250535047749570861611717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76167023365166380574407811 114250535047749570861611717)
        ·
          refine ⟨21421975321453044536552197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114250535047749570861611717 21421975321453044536552197)
          ·
            refine ⟨4016620372772445850603537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21421975321453044536552197 4016620372772445850603537)
            ·
              refine ⟨3012465279579334387952653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4016620372772445850603537 3012465279579334387952653)
              ·
                refine ⟨1129674479842250395482245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3012465279579334387952653 1129674479842250395482245)
                ·
                  refine ⟨211813964970421949152921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1129674479842250395482245 211813964970421949152921)
                  ·
                    rfl

theorem cell21_928139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 4].length) (baseStart_928139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928139 prefixEnd_928139 := by exact prefixLift 928139
  have htrace : WordTrace (prefixWord ++ tailWord_928139) baseStart_928139 baseEnd_928139 := by
    simpa [prefixWord, tailWord_928139, baseEnd_928139] using wordTrace_append hprefix tailTrace_928139
  have hstable : (prefixWord ++ tailWord_928139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928139).length < 2 ^ (prefixWord ++ tailWord_928139).sum := by decide
  have hdescent : baseEnd_928139 < baseStart_928139 := by decide
  rcases family_descends (prefixWord ++ tailWord_928139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928204 : List Nat := [2, 2, 1, 4, 4, 1, 2, 5]
def baseStart_928204 : Nat := 118140960795 + 928204 * 2 ^ 59
def prefixEnd_928204 : Nat := 4983230072969 + 3 ^ 40 * 928204 * 2
def baseEnd_928204 : Nat := 70609599618665426856485

theorem tailTrace_928204 : CollatzResearch.WordTrace tailWord_928204 prefixEnd_928204 70609599618665426856485 := by
  unfold tailWord_928204
  simp only [CollatzResearch.WordTrace]
  refine ⟨16927190564641453733759833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22569587419521938311679777 16927190564641453733759833)
  ·
    refine ⟨12695392923481090300319875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16927190564641453733759833 12695392923481090300319875)
    ·
      refine ⟨19043089385221635450479813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12695392923481090300319875 19043089385221635450479813)
      ·
        refine ⟨3570579259729056646964965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19043089385221635450479813 3570579259729056646964965)
        ·
          refine ⟨669483611199198121305931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3570579259729056646964965 669483611199198121305931)
          ·
            refine ⟨1004225416798797181958897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669483611199198121305931 1004225416798797181958897)
            ·
              refine ⟨753169062599097886469173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1004225416798797181958897 753169062599097886469173)
              ·
                refine ⟨70609599618665426856485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 753169062599097886469173 70609599618665426856485)
                ·
                  rfl

theorem cell21_928204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 5].length) (baseStart_928204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928204 prefixEnd_928204 := by exact prefixLift 928204
  have htrace : WordTrace (prefixWord ++ tailWord_928204) baseStart_928204 baseEnd_928204 := by
    simpa [prefixWord, tailWord_928204, baseEnd_928204] using wordTrace_append hprefix tailTrace_928204
  have hstable : (prefixWord ++ tailWord_928204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928204).length < 2 ^ (prefixWord ++ tailWord_928204).sum := by decide
  have hdescent : baseEnd_928204 < baseStart_928204 := by decide
  rcases family_descends (prefixWord ++ tailWord_928204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928246 : List Nat := [5, 1, 1, 1, 2, 1, 4, 6]
def baseStart_928246 : Nat := 118140960795 + 928246 * 2 ^ 59
def prefixEnd_928246 : Nat := 4983230072969 + 3 ^ 40 * 928246 * 2
def baseEnd_928246 : Nat := 70612794609404513623123

theorem tailTrace_928246 : CollatzResearch.WordTrace tailWord_928246 prefixEnd_928246 70612794609404513623123 := by
  unfold tailWord_928246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2115994562195671790034287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22570608663420499093699061 2115994562195671790034287)
  ·
    refine ⟨3173991843293507685051431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2115994562195671790034287 3173991843293507685051431)
    ·
      refine ⟨4760987764940261527577147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3173991843293507685051431 4760987764940261527577147)
      ·
        refine ⟨7141481647410392291365721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4760987764940261527577147 7141481647410392291365721)
        ·
          refine ⟨5356111235557794218524291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7141481647410392291365721 5356111235557794218524291)
          ·
            refine ⟨8034166853336691327786437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5356111235557794218524291 8034166853336691327786437)
            ·
              refine ⟨1506406285000629623959957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8034166853336691327786437 1506406285000629623959957)
              ·
                refine ⟨70612794609404513623123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1506406285000629623959957 70612794609404513623123)
                ·
                  rfl

theorem cell21_928246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_928246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928246 prefixEnd_928246 := by exact prefixLift 928246
  have htrace : WordTrace (prefixWord ++ tailWord_928246) baseStart_928246 baseEnd_928246 := by
    simpa [prefixWord, tailWord_928246, baseEnd_928246] using wordTrace_append hprefix tailTrace_928246
  have hstable : (prefixWord ++ tailWord_928246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928246).length < 2 ^ (prefixWord ++ tailWord_928246).sum := by decide
  have hdescent : baseEnd_928246 < baseStart_928246 := by decide
  rcases family_descends (prefixWord ++ tailWord_928246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928277 : List Nat := [1, 3, 2, 1, 3, 1, 2, 5, 3]
def baseStart_928277 : Nat := 118140960795 + 928277 * 2 ^ 59
def prefixEnd_928277 : Nat := 4983230072969 + 3 ^ 40 * 928277 * 2
def baseEnd_928277 : Nat := 211845458450564375852639

theorem tailTrace_928277 : CollatzResearch.WordTrace tailWord_928277 prefixEnd_928277 211845458450564375852639 := by
  unfold tailWord_928277
  simp only [CollatzResearch.WordTrace]
  refine ⟨33857043658018440934927085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22571362438678960623284723 33857043658018440934927085)
  ·
    refine ⟨12696391371756915350597657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33857043658018440934927085 12696391371756915350597657)
    ·
      refine ⟨9522293528817686512948243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12696391371756915350597657 9522293528817686512948243)
      ·
        refine ⟨14283440293226529769422365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9522293528817686512948243 14283440293226529769422365)
        ·
          refine ⟨5356290109959948663533387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14283440293226529769422365 5356290109959948663533387)
          ·
            refine ⟨8034435164939922995300081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5356290109959948663533387 8034435164939922995300081)
            ·
              refine ⟨6025826373704942246475061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8034435164939922995300081 6025826373704942246475061)
              ·
                refine ⟨564921222534838335607037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6025826373704942246475061 564921222534838335607037)
                ·
                  refine ⟨211845458450564375852639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 564921222534838335607037 211845458450564375852639)
                  ·
                    rfl

theorem cell21_928277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_928277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928277 prefixEnd_928277 := by exact prefixLift 928277
  have htrace : WordTrace (prefixWord ++ tailWord_928277) baseStart_928277 baseEnd_928277 := by
    simpa [prefixWord, tailWord_928277, baseEnd_928277] using wordTrace_append hprefix tailTrace_928277
  have hstable : (prefixWord ++ tailWord_928277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928277).length < 2 ^ (prefixWord ++ tailWord_928277).sum := by decide
  have hdescent : baseEnd_928277 < baseStart_928277 := by decide
  rcases family_descends (prefixWord ++ tailWord_928277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928291 : List Nat := [1, 1, 1, 4, 4, 1, 1, 4, 4]
def baseStart_928291 : Nat := 118140960795 + 928291 * 2 ^ 59
def prefixEnd_928291 : Nat := 4983230072969 + 3 ^ 40 * 928291 * 2
def baseEnd_928291 : Nat := 211848653441303462619277

theorem tailTrace_928291 : CollatzResearch.WordTrace tailWord_928291 prefixEnd_928291 211848653441303462619277 := by
  unfold tailWord_928291
  simp only [CollatzResearch.WordTrace]
  refine ⟨33857554279967721325936727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22571702853311814217291151 33857554279967721325936727)
  ·
    refine ⟨50786331419951581988905091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33857554279967721325936727 50786331419951581988905091)
    ·
      refine ⟨76179497129927372983357637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50786331419951581988905091 76179497129927372983357637)
      ·
        refine ⟨14283655711861382434379557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76179497129927372983357637 14283655711861382434379557)
        ·
          refine ⟨2678185445974009206446167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14283655711861382434379557 2678185445974009206446167)
          ·
            refine ⟨4017278168961013809669251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2678185445974009206446167 4017278168961013809669251)
            ·
              refine ⟨6025917253441520714503877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4017278168961013809669251 6025917253441520714503877)
              ·
                refine ⟨1129859485020285133969477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6025917253441520714503877 1129859485020285133969477)
                ·
                  refine ⟨211848653441303462619277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1129859485020285133969477 211848653441303462619277)
                  ·
                    rfl

theorem cell21_928291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 4].length) (baseStart_928291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928291 prefixEnd_928291 := by exact prefixLift 928291
  have htrace : WordTrace (prefixWord ++ tailWord_928291) baseStart_928291 baseEnd_928291 := by
    simpa [prefixWord, tailWord_928291, baseEnd_928291] using wordTrace_append hprefix tailTrace_928291
  have hstable : (prefixWord ++ tailWord_928291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928291).length < 2 ^ (prefixWord ++ tailWord_928291).sum := by decide
  have hdescent : baseEnd_928291 < baseStart_928291 := by decide
  rcases family_descends (prefixWord ++ tailWord_928291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928305 : List Nat := [1, 2, 2, 3, 1, 1, 5, 6]
def baseStart_928305 : Nat := 118140960795 + 928305 * 2 ^ 59
def prefixEnd_928305 : Nat := 4983230072969 + 3 ^ 40 * 928305 * 2
def baseEnd_928305 : Nat := 70617282810680849795305

theorem tailTrace_928305 : CollatzResearch.WordTrace tailWord_928305 prefixEnd_928305 70617282810680849795305 := by
  unfold tailWord_928305
  simp only [CollatzResearch.WordTrace]
  refine ⟨33858064901917001716946369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22572043267944667811297579 33858064901917001716946369)
  ·
    refine ⟨25393548676437751287709777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33858064901917001716946369 25393548676437751287709777)
    ·
      refine ⟨19045161507328313465782333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25393548676437751287709777 19045161507328313465782333)
      ·
        refine ⟨7141935565248117549668375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19045161507328313465782333 7141935565248117549668375)
        ·
          refine ⟨10712903347872176324502563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7141935565248117549668375 10712903347872176324502563)
          ·
            refine ⟨16069355021808264486753845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10712903347872176324502563 16069355021808264486753845)
            ·
              refine ⟨1506502033294524795633173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16069355021808264486753845 1506502033294524795633173)
              ·
                refine ⟨70617282810680849795305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1506502033294524795633173 70617282810680849795305)
                ·
                  rfl

theorem cell21_928305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 6].length) (baseStart_928305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928305 prefixEnd_928305 := by exact prefixLift 928305
  have htrace : WordTrace (prefixWord ++ tailWord_928305) baseStart_928305 baseEnd_928305 := by
    simpa [prefixWord, tailWord_928305, baseEnd_928305] using wordTrace_append hprefix tailTrace_928305
  have hstable : (prefixWord ++ tailWord_928305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928305).length < 2 ^ (prefixWord ++ tailWord_928305).sum := by decide
  have hdescent : baseEnd_928305 < baseStart_928305 := by decide
  rcases family_descends (prefixWord ++ tailWord_928305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928353 : List Nat := [1, 2, 3, 1, 1, 4, 2, 4, 3]
def baseStart_928353 : Nat := 118140960795 + 928353 * 2 ^ 59
def prefixEnd_928353 : Nat := 4983230072969 + 3 ^ 40 * 928353 * 2
def baseEnd_928353 : Nat := 211862802686005132585817

theorem tailTrace_928353 : CollatzResearch.WordTrace tailWord_928353 prefixEnd_928353 211862802686005132585817 := by
  unfold tailWord_928353
  simp only [CollatzResearch.WordTrace]
  refine ⟨33859815605743105914693713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22573210403828737276462475 33859815605743105914693713)
  ·
    refine ⟨25394861704307329436020285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33859815605743105914693713 25394861704307329436020285)
    ·
      refine ⟨9523073139115248538507607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25394861704307329436020285 9523073139115248538507607)
      ·
        refine ⟨14284609708672872807761411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9523073139115248538507607 14284609708672872807761411)
        ·
          refine ⟨21426914563009309211642117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14284609708672872807761411 21426914563009309211642117)
          ·
            refine ⟨4017546480564245477182897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21426914563009309211642117 4017546480564245477182897)
            ·
              refine ⟨3013159860423184107887173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4017546480564245477182897 3013159860423184107887173)
              ·
                refine ⟨564967473829347020228845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3013159860423184107887173 564967473829347020228845)
                ·
                  refine ⟨211862802686005132585817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 564967473829347020228845 211862802686005132585817)
                  ·
                    rfl

theorem cell21_928353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 3].length) (baseStart_928353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928353 prefixEnd_928353 := by exact prefixLift 928353
  have htrace : WordTrace (prefixWord ++ tailWord_928353) baseStart_928353 baseEnd_928353 := by
    simpa [prefixWord, tailWord_928353, baseEnd_928353] using wordTrace_append hprefix tailTrace_928353
  have hstable : (prefixWord ++ tailWord_928353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928353).length < 2 ^ (prefixWord ++ tailWord_928353).sum := by decide
  have hdescent : baseEnd_928353 < baseStart_928353 := by decide
  rcases family_descends (prefixWord ++ tailWord_928353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928460 : List Nat := [2, 2, 1, 5, 1, 2, 2, 2, 4]
def baseStart_928460 : Nat := 118140960795 + 928460 * 2 ^ 59
def prefixEnd_928460 : Nat := 4983230072969 + 3 ^ 40 * 928460 * 2
def baseEnd_928460 : Nat := 211887221543796724302265

theorem tailTrace_928460 : CollatzResearch.WordTrace tailWord_928460 prefixEnd_928460 211887221543796724302265 := by
  unfold tailWord_928460
  simp only [CollatzResearch.WordTrace]
  refine ⟨16931859108177731594419417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22575812144236975459225889 16931859108177731594419417)
  ·
    refine ⟨12698894331133298695814563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16931859108177731594419417 12698894331133298695814563)
    ·
      refine ⟨19048341496699948043721845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12698894331133298695814563 19048341496699948043721845)
      ·
        refine ⟨1785782015315620129098923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19048341496699948043721845 1785782015315620129098923)
        ·
          refine ⟨2678673022973430193648385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1785782015315620129098923 2678673022973430193648385)
          ·
            refine ⟨2009004767230072645236289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2678673022973430193648385 2009004767230072645236289)
            ·
              refine ⟨1506753575422554483927217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2009004767230072645236289 1506753575422554483927217)
              ·
                refine ⟨1130065181566915862945413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1506753575422554483927217 1130065181566915862945413)
                ·
                  refine ⟨211887221543796724302265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1130065181566915862945413 211887221543796724302265)
                  ·
                    rfl

theorem cell21_928460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_928460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928460 prefixEnd_928460 := by exact prefixLift 928460
  have htrace : WordTrace (prefixWord ++ tailWord_928460) baseStart_928460 baseEnd_928460 := by
    simpa [prefixWord, tailWord_928460, baseEnd_928460] using wordTrace_append hprefix tailTrace_928460
  have hstable : (prefixWord ++ tailWord_928460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928460).length < 2 ^ (prefixWord ++ tailWord_928460).sum := by decide
  have hdescent : baseEnd_928460 < baseStart_928460 := by decide
  rcases family_descends (prefixWord ++ tailWord_928460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928519 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 6]
def baseStart_928519 : Nat := 118140960795 + 928519 * 2 ^ 59
def prefixEnd_928519 : Nat := 4983230072969 + 3 ^ 40 * 928519 * 2
def baseEnd_928519 : Nat := 211900686147625732818811

theorem tailTrace_928519 : CollatzResearch.WordTrace tailWord_928519 prefixEnd_928519 211900686147625732818811 := by
  unfold tailWord_928519
  simp only [CollatzResearch.WordTrace]
  refine ⟨33865870123141716265236611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22577246748761144176824407 33865870123141716265236611)
  ·
    refine ⟨50798805184712574397854917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33865870123141716265236611 50798805184712574397854917)
    ·
      refine ⟨9524775972133607699597797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50798805184712574397854917 9524775972133607699597797)
      ·
        refine ⟨1785895494775051443674587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9524775972133607699597797 1785895494775051443674587)
        ·
          refine ⟨2678843242162577165511881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1785895494775051443674587 2678843242162577165511881)
          ·
            refine ⟨2009132431621932874133911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2678843242162577165511881 2009132431621932874133911)
            ·
              refine ⟨3013698647432899311200867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2009132431621932874133911 3013698647432899311200867)
              ·
                refine ⟨4520547971149348966801301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3013698647432899311200867 4520547971149348966801301)
                ·
                  refine ⟨211900686147625732818811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4520547971149348966801301 211900686147625732818811)
                  ·
                    rfl

theorem cell21_928519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 6].length) (baseStart_928519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928519 prefixEnd_928519 := by exact prefixLift 928519
  have htrace : WordTrace (prefixWord ++ tailWord_928519) baseStart_928519 baseEnd_928519 := by
    simpa [prefixWord, tailWord_928519, baseEnd_928519] using wordTrace_append hprefix tailTrace_928519
  have hstable : (prefixWord ++ tailWord_928519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928519).length < 2 ^ (prefixWord ++ tailWord_928519).sum := by decide
  have hdescent : baseEnd_928519 < baseStart_928519 := by decide
  rcases family_descends (prefixWord ++ tailWord_928519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928592 : List Nat := [2, 1, 1, 1, 1, 4, 3, 8]
def baseStart_928592 : Nat := 118140960795 + 928592 * 2 ^ 59
def prefixEnd_928592 : Nat := 4983230072969 + 3 ^ 40 * 928592 * 2
def baseEnd_928592 : Nat := 70639115247397942700665

theorem tailTrace_928592 : CollatzResearch.WordTrace tailWord_928592 prefixEnd_928592 70639115247397942700665 := by
  unfold tailWord_928592
  simp only [CollatzResearch.WordTrace]
  refine ⟨16934266325938624866322015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22579021767918166488429353 16934266325938624866322015)
  ·
    refine ⟨25401399488907937299483023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16934266325938624866322015 25401399488907937299483023)
    ·
      refine ⟨38102099233361905949224535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25401399488907937299483023 38102099233361905949224535)
      ·
        refine ⟨57153148850042858923836803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38102099233361905949224535 57153148850042858923836803)
        ·
          refine ⟨85729723275064288385755205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57153148850042858923836803 85729723275064288385755205)
          ·
            refine ⟨16074323114074554072329101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85729723275064288385755205 16074323114074554072329101)
            ·
              refine ⟨6027871167777957777123413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16074323114074554072329101 6027871167777957777123413)
              ·
                refine ⟨70639115247397942700665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6027871167777957777123413 70639115247397942700665)
                ·
                  rfl

theorem cell21_928592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 8].length) (baseStart_928592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928592 prefixEnd_928592 := by exact prefixLift 928592
  have htrace : WordTrace (prefixWord ++ tailWord_928592) baseStart_928592 baseEnd_928592 := by
    simpa [prefixWord, tailWord_928592, baseEnd_928592] using wordTrace_append hprefix tailTrace_928592
  have hstable : (prefixWord ++ tailWord_928592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928592).length < 2 ^ (prefixWord ++ tailWord_928592).sum := by decide
  have hdescent : baseEnd_928592 < baseStart_928592 := by decide
  rcases family_descends (prefixWord ++ tailWord_928592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928674 : List Nat := [3, 3, 1, 2, 2, 2, 2, 3, 3]
def baseStart_928674 : Nat := 118140960795 + 928674 * 2 ^ 59
def prefixEnd_928674 : Nat := 4983230072969 + 3 ^ 40 * 928674 * 2
def baseEnd_928674 : Nat := 211936059259379907735161

theorem tailTrace_928674 : CollatzResearch.WordTrace tailWord_928674 prefixEnd_928674 211936059259379907735161 := by
  unfold tailWord_928674
  simp only [CollatzResearch.WordTrace]
  refine ⟨8467880859395044434282269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22581015625053451824752717 8467880859395044434282269)
  ·
    refine ⟨3175455322273141662855851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8467880859395044434282269 3175455322273141662855851)
    ·
      refine ⟨4763182983409712494283777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3175455322273141662855851 4763182983409712494283777)
      ·
        refine ⟨3572387237557284370712833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4763182983409712494283777 3572387237557284370712833)
        ·
          refine ⟨2679290428167963278034625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3572387237557284370712833 2679290428167963278034625)
          ·
            refine ⟨2009467821125972458525969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2679290428167963278034625 2009467821125972458525969)
            ·
              refine ⟨1507100865844479343894477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2009467821125972458525969 1507100865844479343894477)
              ·
                refine ⟨565162824691679753960429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1507100865844479343894477 565162824691679753960429)
                ·
                  refine ⟨211936059259379907735161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565162824691679753960429 211936059259379907735161)
                  ·
                    rfl

theorem cell21_928674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_928674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928674 prefixEnd_928674 := by exact prefixLift 928674
  have htrace : WordTrace (prefixWord ++ tailWord_928674) baseStart_928674 baseEnd_928674 := by
    simpa [prefixWord, tailWord_928674, baseEnd_928674] using wordTrace_append hprefix tailTrace_928674
  have hstable : (prefixWord ++ tailWord_928674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928674).length < 2 ^ (prefixWord ++ tailWord_928674).sum := by decide
  have hdescent : baseEnd_928674 < baseStart_928674 := by decide
  rcases family_descends (prefixWord ++ tailWord_928674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928713 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 10]
def baseStart_928713 : Nat := 118140960795 + 928713 * 2 ^ 59
def prefixEnd_928713 : Nat := 4983230072969 + 3 ^ 40 * 928713 * 2
def baseEnd_928713 : Nat := 211944959590724506585081

theorem tailTrace_928713 : CollatzResearch.WordTrace tailWord_928713 prefixEnd_928713 211944959590724506585081 := by
  unfold tailWord_928713
  simp only [CollatzResearch.WordTrace]
  refine ⟨33872945884438887397798793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22581963922959258265199195 33872945884438887397798793)
  ·
    refine ⟨25404709413329165548349095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33872945884438887397798793 25404709413329165548349095)
    ·
      refine ⟨38107064119993748322523643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25404709413329165548349095 38107064119993748322523643)
      ·
        refine ⟨57160596179990622483785465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38107064119993748322523643 57160596179990622483785465)
        ·
          refine ⟨42870447134992966862839099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57160596179990622483785465 42870447134992966862839099)
          ·
            refine ⟨64305670702489450294258649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42870447134992966862839099 64305670702489450294258649)
            ·
              refine ⟨48229253026867087720693987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64305670702489450294258649 48229253026867087720693987)
              ·
                refine ⟨72343879540300631581040981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48229253026867087720693987 72343879540300631581040981)
                ·
                  refine ⟨211944959590724506585081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 72343879540300631581040981 211944959590724506585081)
                  ·
                    rfl

theorem cell21_928713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_928713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928713 prefixEnd_928713 := by exact prefixLift 928713
  have htrace : WordTrace (prefixWord ++ tailWord_928713) baseStart_928713 baseEnd_928713 := by
    simpa [prefixWord, tailWord_928713, baseEnd_928713] using wordTrace_append hprefix tailTrace_928713
  have hstable : (prefixWord ++ tailWord_928713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928713).length < 2 ^ (prefixWord ++ tailWord_928713).sum := by decide
  have hdescent : baseEnd_928713 < baseStart_928713 := by decide
  rcases family_descends (prefixWord ++ tailWord_928713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928730 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 6]
def baseStart_928730 : Nat := 118140960795 + 928730 * 2 ^ 59
def prefixEnd_928730 : Nat := 4983230072969 + 3 ^ 40 * 928730 * 2
def baseEnd_928730 : Nat := 211948839222336254801713

theorem tailTrace_928730 : CollatzResearch.WordTrace tailWord_928730 prefixEnd_928730 211948839222336254801713 := by
  unfold tailWord_928730
  simp only [CollatzResearch.WordTrace]
  refine ⟨8468391481344324825291911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22582377283584866200778429 8468391481344324825291911)
  ·
    refine ⟨12702587222016487237937867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8468391481344324825291911 12702587222016487237937867)
    ·
      refine ⟨19053880833024730856906801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12702587222016487237937867 19053880833024730856906801)
      ·
        refine ⟨14290410624768548142680101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19053880833024730856906801 14290410624768548142680101)
        ·
          refine ⟨2679451992144102776752519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14290410624768548142680101 2679451992144102776752519)
          ·
            refine ⟨4019177988216154165128779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2679451992144102776752519 4019177988216154165128779)
            ·
              refine ⟨6028766982324231247693169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4019177988216154165128779 6028766982324231247693169)
              ·
                refine ⟨4521575236743173435769877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6028766982324231247693169 4521575236743173435769877)
                ·
                  refine ⟨211948839222336254801713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4521575236743173435769877 211948839222336254801713)
                  ·
                    rfl

theorem cell21_928730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_928730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928730 prefixEnd_928730 := by exact prefixLift 928730
  have htrace : WordTrace (prefixWord ++ tailWord_928730) baseStart_928730 baseEnd_928730 := by
    simpa [prefixWord, tailWord_928730, baseEnd_928730] using wordTrace_append hprefix tailTrace_928730
  have hstable : (prefixWord ++ tailWord_928730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928730).length < 2 ^ (prefixWord ++ tailWord_928730).sum := by decide
  have hdescent : baseEnd_928730 < baseStart_928730 := by decide
  rcases family_descends (prefixWord ++ tailWord_928730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928744 : List Nat := [2, 1, 4, 1, 1, 1, 11]
def baseStart_928744 : Nat := 118140960795 + 928744 * 2 ^ 59
def prefixEnd_928744 : Nat := 4983230072969 + 3 ^ 40 * 928744 * 2
def baseEnd_928744 : Nat := 23550226023675037952039

theorem tailTrace_928744 : CollatzResearch.WordTrace tailWord_928744 prefixEnd_928744 23550226023675037952039 := by
  unfold tailWord_928744
  simp only [CollatzResearch.WordTrace]
  refine ⟨16937038273663289846088643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22582717698217719794784857 16937038273663289846088643)
  ·
    refine ⟨25405557410494934769132965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16937038273663289846088643 25405557410494934769132965)
    ·
      refine ⟨4763542014467800269212431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25405557410494934769132965 4763542014467800269212431)
      ·
        refine ⟨7145313021701700403818647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4763542014467800269212431 7145313021701700403818647)
        ·
          refine ⟨10717969532552550605727971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7145313021701700403818647 10717969532552550605727971)
          ·
            refine ⟨16076954298828825908591957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10717969532552550605727971 16076954298828825908591957)
            ·
              refine ⟨23550226023675037952039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16076954298828825908591957 23550226023675037952039)
              ·
                rfl

theorem cell21_928744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 11].length) (baseStart_928744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928744 prefixEnd_928744 := by exact prefixLift 928744
  have htrace : WordTrace (prefixWord ++ tailWord_928744) baseStart_928744 baseEnd_928744 := by
    simpa [prefixWord, tailWord_928744, baseEnd_928744] using wordTrace_append hprefix tailTrace_928744
  have hstable : (prefixWord ++ tailWord_928744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928744).length < 2 ^ (prefixWord ++ tailWord_928744).sum := by decide
  have hdescent : baseEnd_928744 < baseStart_928744 := by decide
  rcases family_descends (prefixWord ++ tailWord_928744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928750 : List Nat := [4, 1, 2, 1, 5, 1, 1, 1, 5]
def baseStart_928750 : Nat := 118140960795 + 928750 * 2 ^ 59
def prefixEnd_928750 : Nat := 4983230072969 + 3 ^ 40 * 928750 * 2
def baseEnd_928750 : Nat := 211953403494820664468339

theorem tailTrace_928750 : CollatzResearch.WordTrace tailWord_928750 prefixEnd_928750 211953403494820664468339 := by
  unfold tailWord_928750
  simp only [CollatzResearch.WordTrace]
  refine ⟨4234286923163105339611963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22582863590203228477930469 4234286923163105339611963)
  ·
    refine ⟨6351430384744658009417945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4234286923163105339611963 6351430384744658009417945)
    ·
      refine ⟨4763572788558493507063459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6351430384744658009417945 4763572788558493507063459)
      ·
        refine ⟨7145359182837740260595189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4763572788558493507063459 7145359182837740260595189)
        ·
          refine ⟨669877423391038149430799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7145359182837740260595189 669877423391038149430799)
          ·
            refine ⟨1004816135086557224146199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669877423391038149430799 1004816135086557224146199)
            ·
              refine ⟨1507224202629835836219299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1004816135086557224146199 1507224202629835836219299)
              ·
                refine ⟨2260836303944753754328949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1507224202629835836219299 2260836303944753754328949)
                ·
                  refine ⟨211953403494820664468339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2260836303944753754328949 211953403494820664468339)
                  ·
                    rfl

theorem cell21_928750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_928750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928750 prefixEnd_928750 := by exact prefixLift 928750
  have htrace : WordTrace (prefixWord ++ tailWord_928750) baseStart_928750 baseEnd_928750 := by
    simpa [prefixWord, tailWord_928750, baseEnd_928750] using wordTrace_append hprefix tailTrace_928750
  have hstable : (prefixWord ++ tailWord_928750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928750).length < 2 ^ (prefixWord ++ tailWord_928750).sum := by decide
  have hdescent : baseEnd_928750 < baseStart_928750 := by decide
  rcases family_descends (prefixWord ++ tailWord_928750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928756 : List Nat := [2, 6, 2, 1, 1, 2, 2, 1, 4]
def baseStart_928756 : Nat := 118140960795 + 928756 * 2 ^ 59
def prefixEnd_928756 : Nat := 4983230072969 + 3 ^ 40 * 928756 * 2
def baseEnd_928756 : Nat := 211954772776565987368327

theorem tailTrace_928756 : CollatzResearch.WordTrace tailWord_928756 prefixEnd_928756 211954772776565987368327 := by
  unfold tailWord_928756
  simp only [CollatzResearch.WordTrace]
  refine ⟨16937257111641552870807061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22583009482188737161076081 16937257111641552870807061)
  ·
    refine ⟨793933927108197790819081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16937257111641552870807061 793933927108197790819081)
    ·
      refine ⟨595450445331148343114311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 793933927108197790819081 595450445331148343114311)
      ·
        refine ⟨893175667996722514671467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595450445331148343114311 893175667996722514671467)
        ·
          refine ⟨1339763501995083772007201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893175667996722514671467 1339763501995083772007201)
          ·
            refine ⟨1004822626496312829005401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1339763501995083772007201 1004822626496312829005401)
            ·
              refine ⟨753616969872234621754051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1004822626496312829005401 753616969872234621754051)
              ·
                refine ⟨1130425454808351932631077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753616969872234621754051 1130425454808351932631077)
                ·
                  refine ⟨211954772776565987368327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1130425454808351932631077 211954772776565987368327)
                  ·
                    rfl

theorem cell21_928756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_928756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928756 prefixEnd_928756 := by exact prefixLift 928756
  have htrace : WordTrace (prefixWord ++ tailWord_928756) baseStart_928756 baseEnd_928756 := by
    simpa [prefixWord, tailWord_928756, baseEnd_928756] using wordTrace_append hprefix tailTrace_928756
  have hstable : (prefixWord ++ tailWord_928756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928756).length < 2 ^ (prefixWord ++ tailWord_928756).sum := by decide
  have hdescent : baseEnd_928756 < baseStart_928756 := by decide
  rcases family_descends (prefixWord ++ tailWord_928756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928764 : List Nat := [2, 2, 2, 1, 2, 5, 2, 1, 4]
def baseStart_928764 : Nat := 118140960795 + 928764 * 2 ^ 59
def prefixEnd_928764 : Nat := 4983230072969 + 3 ^ 40 * 928764 * 2
def baseEnd_928764 : Nat := 211956598485559751234977

theorem tailTrace_928764 : CollatzResearch.WordTrace tailWord_928764 prefixEnd_928764 211956598485559751234977 := by
  unfold tailWord_928764
  simp only [CollatzResearch.WordTrace]
  refine ⟨16937403003627061553952673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22583204004836082071936897 16937403003627061553952673)
  ·
    refine ⟨12703052252720296165464505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16937403003627061553952673 12703052252720296165464505)
    ·
      refine ⟨9527289189540222124098379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12703052252720296165464505 9527289189540222124098379)
      ·
        refine ⟨14290933784310333186147569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9527289189540222124098379 14290933784310333186147569)
        ·
          refine ⟨10718200338232749889610677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14290933784310333186147569 10718200338232749889610677)
          ·
            refine ⟨1004831281709320302151001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10718200338232749889610677 1004831281709320302151001)
            ·
              refine ⟨753623461281990226613251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1004831281709320302151001 753623461281990226613251)
              ·
                refine ⟨1130435191922985339919877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753623461281990226613251 1130435191922985339919877)
                ·
                  refine ⟨211956598485559751234977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1130435191922985339919877 211956598485559751234977)
                  ·
                    rfl

theorem cell21_928764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_928764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928764 prefixEnd_928764 := by exact prefixLift 928764
  have htrace : WordTrace (prefixWord ++ tailWord_928764) baseStart_928764 baseEnd_928764 := by
    simpa [prefixWord, tailWord_928764, baseEnd_928764] using wordTrace_append hprefix tailTrace_928764
  have hstable : (prefixWord ++ tailWord_928764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928764).length < 2 ^ (prefixWord ++ tailWord_928764).sum := by decide
  have hdescent : baseEnd_928764 < baseStart_928764 := by decide
  rcases family_descends (prefixWord ++ tailWord_928764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928775 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 7]
def baseStart_928775 : Nat := 118140960795 + 928775 * 2 ^ 59
def prefixEnd_928775 : Nat := 4983230072969 + 3 ^ 40 * 928775 * 2
def baseEnd_928775 : Nat := 211959108835426176551621

theorem tailTrace_928775 : CollatzResearch.WordTrace tailWord_928775 prefixEnd_928775 211959108835426176551621 := by
  unfold tailWord_928775
  simp only [CollatzResearch.WordTrace]
  refine ⟨33875207210214271986555779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22583471473476181324370519 33875207210214271986555779)
  ·
    refine ⟨50812810815321407979833669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33875207210214271986555779 50812810815321407979833669)
    ·
      refine ⟨9527402027872763996218813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50812810815321407979833669 9527402027872763996218813)
      ·
        refine ⟨3572775760452286498582055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9527402027872763996218813 3572775760452286498582055)
        ·
          refine ⟨5359163640678429747873083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3572775760452286498582055 5359163640678429747873083)
          ·
            refine ⟨8038745461017644621809625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5359163640678429747873083 8038745461017644621809625)
            ·
              refine ⟨6029059095763233466357219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8038745461017644621809625 6029059095763233466357219)
              ·
                refine ⟨9043588643644850199535829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6029059095763233466357219 9043588643644850199535829)
                ·
                  refine ⟨211959108835426176551621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9043588643644850199535829 211959108835426176551621)
                  ·
                    rfl

theorem cell21_928775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 7].length) (baseStart_928775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928775 prefixEnd_928775 := by exact prefixLift 928775
  have htrace : WordTrace (prefixWord ++ tailWord_928775) baseStart_928775 baseEnd_928775 := by
    simpa [prefixWord, tailWord_928775, baseEnd_928775] using wordTrace_append hprefix tailTrace_928775
  have hstable : (prefixWord ++ tailWord_928775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928775).length < 2 ^ (prefixWord ++ tailWord_928775).sum := by decide
  have hdescent : baseEnd_928775 < baseStart_928775 := by decide
  rcases family_descends (prefixWord ++ tailWord_928775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928930 : List Nat := [3, 3, 1, 3, 2, 1, 2, 6]
def baseStart_928930 : Nat := 118140960795 + 928930 * 2 ^ 59
def prefixEnd_928930 : Nat := 4983230072969 + 3 ^ 40 * 928930 * 2
def baseEnd_928930 : Nat := 70664827315726783822657

theorem tailTrace_928930 : CollatzResearch.WordTrace tailWord_928930 prefixEnd_928930 70664827315726783822657 := by
  unfold tailWord_928930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8470215131163183364612061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22587240349768488972298829 8470215131163183364612061)
  ·
    refine ⟨3176330674186193761729523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8470215131163183364612061 3176330674186193761729523)
    ·
      refine ⟨4764496011279290642594285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3176330674186193761729523 4764496011279290642594285)
      ·
        refine ⟨1786686004229733990972857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4764496011279290642594285 1786686004229733990972857)
        ·
          refine ⟨1340014503172300493229643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1786686004229733990972857 1340014503172300493229643)
          ·
            refine ⟨2010021754758450739844465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340014503172300493229643 2010021754758450739844465)
            ·
              refine ⟨1507516316068838054883349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2010021754758450739844465 1507516316068838054883349)
              ·
                refine ⟨70664827315726783822657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1507516316068838054883349 70664827315726783822657)
                ·
                  rfl

theorem cell21_928930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_928930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_928930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_928930 prefixEnd_928930 := by exact prefixLift 928930
  have htrace : WordTrace (prefixWord ++ tailWord_928930) baseStart_928930 baseEnd_928930 := by
    simpa [prefixWord, tailWord_928930, baseEnd_928930] using wordTrace_append hprefix tailTrace_928930
  have hstable : (prefixWord ++ tailWord_928930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928930).length < 2 ^ (prefixWord ++ tailWord_928930).sum := by decide
  have hdescent : baseEnd_928930 < baseStart_928930 := by decide
  rcases family_descends (prefixWord ++ tailWord_928930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929003 : List Nat := [1, 1, 1, 1, 2, 7, 1, 2, 5]
def baseStart_929003 : Nat := 118140960795 + 929003 * 2 ^ 59
def prefixEnd_929003 : Nat := 4983230072969 + 3 ^ 40 * 929003 * 2
def baseEnd_929003 : Nat := 212011141541748446751155

theorem tailTrace_929003 : CollatzResearch.WordTrace tailWord_929003 prefixEnd_929003 212011141541748446751155 := by
  unfold tailWord_929003
  simp only [CollatzResearch.WordTrace]
  refine ⟨33883523053388266925855663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22589015368925511283903775 33883523053388266925855663)
  ·
    refine ⟨50825284580082400388783495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33883523053388266925855663 50825284580082400388783495)
    ·
      refine ⟨76237926870123600583175243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50825284580082400388783495 76237926870123600583175243)
      ·
        refine ⟨114356890305185400874762865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76237926870123600583175243 114356890305185400874762865)
        ·
          refine ⟨85767667728889050656072149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114356890305185400874762865 85767667728889050656072149)
          ·
            refine ⟨2010179712395837124751691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 85767667728889050656072149 2010179712395837124751691)
            ·
              refine ⟨3015269568593755687127537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2010179712395837124751691 3015269568593755687127537)
              ·
                refine ⟨2261452176445316765345653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3015269568593755687127537 2261452176445316765345653)
                ·
                  refine ⟨212011141541748446751155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2261452176445316765345653 212011141541748446751155)
                  ·
                    rfl

theorem cell21_929003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 5].length) (baseStart_929003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929003 prefixEnd_929003 := by exact prefixLift 929003
  have htrace : WordTrace (prefixWord ++ tailWord_929003) baseStart_929003 baseEnd_929003 := by
    simpa [prefixWord, tailWord_929003, baseEnd_929003] using wordTrace_append hprefix tailTrace_929003
  have hstable : (prefixWord ++ tailWord_929003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929003).length < 2 ^ (prefixWord ++ tailWord_929003).sum := by decide
  have hdescent : baseEnd_929003 < baseStart_929003 := by decide
  rcases family_descends (prefixWord ++ tailWord_929003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929012 : List Nat := [2, 6, 1, 2, 1, 1, 2, 3, 3]
def baseStart_929012 : Nat := 118140960795 + 929012 * 2 ^ 59
def prefixEnd_929012 : Nat := 4983230072969 + 3 ^ 40 * 929012 * 2
def baseEnd_929012 : Nat := 212013195464366431101137

theorem tailTrace_929012 : CollatzResearch.WordTrace tailWord_929012 prefixEnd_929012 212013195464366431101137 := by
  unfold tailWord_929012
  simp only [CollatzResearch.WordTrace]
  refine ⟨16941925655177830731466645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22589234206903774308622193 16941925655177830731466645)
  ·
    refine ⟨794152765086460815537499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16941925655177830731466645 794152765086460815537499)
    ·
      refine ⟨1191229147629691223306249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 794152765086460815537499 1191229147629691223306249)
      ·
        refine ⟨893421860722268417479687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1191229147629691223306249 893421860722268417479687)
        ·
          refine ⟨1340132791083402626219531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893421860722268417479687 1340132791083402626219531)
          ·
            refine ⟨2010199186625103939329297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340132791083402626219531 2010199186625103939329297)
            ·
              refine ⟨1507649389968827954496973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2010199186625103939329297 1507649389968827954496973)
              ·
                refine ⟨565368521238310482936365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1507649389968827954496973 565368521238310482936365)
                ·
                  refine ⟨212013195464366431101137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565368521238310482936365 212013195464366431101137)
                  ·
                    rfl

theorem cell21_929012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_929012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929012 prefixEnd_929012 := by exact prefixLift 929012
  have htrace : WordTrace (prefixWord ++ tailWord_929012) baseStart_929012 baseEnd_929012 := by
    simpa [prefixWord, tailWord_929012, baseEnd_929012] using wordTrace_append hprefix tailTrace_929012
  have hstable : (prefixWord ++ tailWord_929012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929012).length < 2 ^ (prefixWord ++ tailWord_929012).sum := by decide
  have hdescent : baseEnd_929012 < baseStart_929012 := by decide
  rcases family_descends (prefixWord ++ tailWord_929012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929017 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 6]
def baseStart_929017 : Nat := 118140960795 + 929017 * 2 ^ 59
def prefixEnd_929017 : Nat := 4983230072969 + 3 ^ 40 * 929017 * 2
def baseEnd_929017 : Nat := 212014336532487533517793

theorem tailTrace_929017 : CollatzResearch.WordTrace tailWord_929017 prefixEnd_929017 212014336532487533517793 := by
  unfold tailWord_929017
  simp only [CollatzResearch.WordTrace]
  refine ⟨33884033675337547316865305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22589355783558364877910203 33884033675337547316865305)
  ·
    refine ⟨25413025256503160487648979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33884033675337547316865305 25413025256503160487648979)
    ·
      refine ⟨38119537884754740731473469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25413025256503160487648979 38119537884754740731473469)
      ·
        refine ⟨14294826706783027774302551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38119537884754740731473469 14294826706783027774302551)
        ·
          refine ⟨21442240060174541661453827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14294826706783027774302551 21442240060174541661453827)
          ·
            refine ⟨32163360090261812492180741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21442240060174541661453827 32163360090261812492180741)
            ·
              refine ⟨6030630016924089842283889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32163360090261812492180741 6030630016924089842283889)
              ·
                refine ⟨4522972512693067381712917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6030630016924089842283889 4522972512693067381712917)
                ·
                  refine ⟨212014336532487533517793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4522972512693067381712917 212014336532487533517793)
                  ·
                    rfl

theorem cell21_929017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_929017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929017 prefixEnd_929017 := by exact prefixLift 929017
  have htrace : WordTrace (prefixWord ++ tailWord_929017) baseStart_929017 baseEnd_929017 := by
    simpa [prefixWord, tailWord_929017, baseEnd_929017] using wordTrace_append hprefix tailTrace_929017
  have hstable : (prefixWord ++ tailWord_929017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929017).length < 2 ^ (prefixWord ++ tailWord_929017).sum := by decide
  have hdescent : baseEnd_929017 < baseStart_929017 := by decide
  rcases family_descends (prefixWord ++ tailWord_929017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929124 : List Nat := [2, 3, 1, 1, 3, 2, 2, 7]
def baseStart_929124 : Nat := 118140960795 + 929124 * 2 ^ 59
def prefixEnd_929124 : Nat := 4983230072969 + 3 ^ 40 * 929124 * 2
def baseEnd_929124 : Nat := 70679585130093041744747

theorem tailTrace_929124 : CollatzResearch.WordTrace tailWord_929124 prefixEnd_929124 70679585130093041744747 := by
  unfold tailWord_929124
  simp only [CollatzResearch.WordTrace]
  refine ⟨16943968142974952295505213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22591957523966603060673617 16943968142974952295505213)
  ·
    refine ⟨6353988053615607110814455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16943968142974952295505213 6353988053615607110814455)
    ·
      refine ⟨9530982080423410666221683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6353988053615607110814455 9530982080423410666221683)
      ·
        refine ⟨14296473120635115999332525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9530982080423410666221683 14296473120635115999332525)
        ·
          refine ⟨5361177420238168499749697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14296473120635115999332525 5361177420238168499749697)
          ·
            refine ⟨4020883065178626374812273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5361177420238168499749697 4020883065178626374812273)
            ·
              refine ⟨3015662298883969781109205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4020883065178626374812273 3015662298883969781109205)
              ·
                refine ⟨70679585130093041744747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3015662298883969781109205 70679585130093041744747)
                ·
                  rfl

theorem cell21_929124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 7].length) (baseStart_929124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929124 prefixEnd_929124 := by exact prefixLift 929124
  have htrace : WordTrace (prefixWord ++ tailWord_929124) baseStart_929124 baseEnd_929124 := by
    simpa [prefixWord, tailWord_929124, baseEnd_929124] using wordTrace_append hprefix tailTrace_929124
  have hstable : (prefixWord ++ tailWord_929124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929124).length < 2 ^ (prefixWord ++ tailWord_929124).sum := by decide
  have hdescent : baseEnd_929124 < baseStart_929124 := by decide
  rcases family_descends (prefixWord ++ tailWord_929124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929141 : List Nat := [1, 3, 4, 1, 4, 8]
def baseStart_929141 : Nat := 118140960795 + 929141 * 2 ^ 59
def prefixEnd_929141 : Nat := 4983230072969 + 3 ^ 40 * 929141 * 2
def baseEnd_929141 : Nat := 7853430926736699016699

theorem tailTrace_929141 : CollatzResearch.WordTrace tailWord_929141 prefixEnd_929141 7853430926736699016699 := by
  unfold tailWord_929141
  simp only [CollatzResearch.WordTrace]
  refine ⟨33888556326888316494379277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22592370884592210996252851 33888556326888316494379277)
  ·
    refine ⟨12708208622583118685392229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33888556326888316494379277 12708208622583118685392229)
    ·
      refine ⟨2382789116734334753511043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12708208622583118685392229 2382789116734334753511043)
      ·
        refine ⟨3574183675101502130266565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2382789116734334753511043 3574183675101502130266565)
        ·
          refine ⟨670159439081531649424981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3574183675101502130266565 670159439081531649424981)
          ·
            refine ⟨7853430926736699016699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 670159439081531649424981 7853430926736699016699)
            ·
              rfl

theorem cell21_929141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 8].length) (baseStart_929141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929141 prefixEnd_929141 := by exact prefixLift 929141
  have htrace : WordTrace (prefixWord ++ tailWord_929141) baseStart_929141 baseEnd_929141 := by
    simpa [prefixWord, tailWord_929141, baseEnd_929141] using wordTrace_append hprefix tailTrace_929141
  have hstable : (prefixWord ++ tailWord_929141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929141).length < 2 ^ (prefixWord ++ tailWord_929141).sum := by decide
  have hdescent : baseEnd_929141 < baseStart_929141 := by decide
  rcases family_descends (prefixWord ++ tailWord_929141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929172 : List Nat := [2, 4, 2, 1, 2, 2, 1, 2, 5]
def baseStart_929172 : Nat := 118140960795 + 929172 * 2 ^ 59
def prefixEnd_929172 : Nat := 4983230072969 + 3 ^ 40 * 929172 * 2
def baseEnd_929172 : Nat := 212049709644241708434143

theorem tailTrace_929172 : CollatzResearch.WordTrace tailWord_929172 prefixEnd_929172 212049709644241708434143 := by
  unfold tailWord_929172
  simp only [CollatzResearch.WordTrace]
  refine ⟨16944843494888004394378885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22593124659850672525838513 16944843494888004394378885)
  ·
    refine ⟨3177158155291500823946041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16944843494888004394378885 3177158155291500823946041)
    ·
      refine ⟨2382868616468625617959531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3177158155291500823946041 2382868616468625617959531)
      ·
        refine ⟨3574302924702938426939297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2382868616468625617959531 3574302924702938426939297)
        ·
          refine ⟨2680727193527203820204473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3574302924702938426939297 2680727193527203820204473)
          ·
            refine ⟨2010545395145402865153355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2680727193527203820204473 2010545395145402865153355)
            ·
              refine ⟨3015818092718104297730033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2010545395145402865153355 3015818092718104297730033)
              ·
                refine ⟨2261863569538578223297525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3015818092718104297730033 2261863569538578223297525)
                ·
                  refine ⟨212049709644241708434143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2261863569538578223297525 212049709644241708434143)
                  ·
                    rfl

theorem cell21_929172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_929172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929172 prefixEnd_929172 := by exact prefixLift 929172
  have htrace : WordTrace (prefixWord ++ tailWord_929172) baseStart_929172 baseEnd_929172 := by
    simpa [prefixWord, tailWord_929172, baseEnd_929172] using wordTrace_append hprefix tailTrace_929172
  have hstable : (prefixWord ++ tailWord_929172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929172).length < 2 ^ (prefixWord ++ tailWord_929172).sum := by decide
  have hdescent : baseEnd_929172 < baseStart_929172 := by decide
  rcases family_descends (prefixWord ++ tailWord_929172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929220 : List Nat := [2, 3, 3, 2, 1, 2, 3, 1, 4]
def baseStart_929220 : Nat := 118140960795 + 929220 * 2 ^ 59
def prefixEnd_929220 : Nat := 4983230072969 + 3 ^ 40 * 929220 * 2
def baseEnd_929220 : Nat := 212060663898204291634045

theorem tailTrace_929220 : CollatzResearch.WordTrace tailWord_929220 prefixEnd_929220 212060663898204291634045 := by
  unfold tailWord_929220
  simp only [CollatzResearch.WordTrace]
  refine ⟨16945718846801056493252557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22594291795734741991003409 16945718846801056493252557)
  ·
    refine ⟨6354644567550396184969709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16945718846801056493252557 6354644567550396184969709)
    ·
      refine ⟨2382991712831398569363641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6354644567550396184969709 2382991712831398569363641)
      ·
        refine ⟨1787243784623548927022731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2382991712831398569363641 1787243784623548927022731)
        ·
          refine ⟨2680865676935323390534097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1787243784623548927022731 2680865676935323390534097)
          ·
            refine ⟨2010649257701492542900573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2680865676935323390534097 2010649257701492542900573)
            ·
              refine ⟨753993471638059703587715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2010649257701492542900573 753993471638059703587715)
              ·
                refine ⟨1130990207457089555381573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753993471638059703587715 1130990207457089555381573)
                ·
                  refine ⟨212060663898204291634045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1130990207457089555381573 212060663898204291634045)
                  ·
                    rfl

theorem cell21_929220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_929220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929220 prefixEnd_929220 := by exact prefixLift 929220
  have htrace : WordTrace (prefixWord ++ tailWord_929220) baseStart_929220 baseEnd_929220 := by
    simpa [prefixWord, tailWord_929220, baseEnd_929220] using wordTrace_append hprefix tailTrace_929220
  have hstable : (prefixWord ++ tailWord_929220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929220).length < 2 ^ (prefixWord ++ tailWord_929220).sum := by decide
  have hdescent : baseEnd_929220 < baseStart_929220 := by decide
  rcases family_descends (prefixWord ++ tailWord_929220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929262 : List Nat := [4, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_929262 : Nat := 118140960795 + 929262 * 2 ^ 59
def prefixEnd_929262 : Nat := 4983230072969 + 3 ^ 40 * 929262 * 2
def baseEnd_929262 : Nat := 212070248870421551933959

theorem tailTrace_929262 : CollatzResearch.WordTrace tailWord_929262 prefixEnd_929262 212070248870421551933959 := by
  unfold tailWord_929262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4236621194931244269941755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22595313039633302773022693 4236621194931244269941755)
  ·
    refine ⟨6354931792396866404912633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4236621194931244269941755 6354931792396866404912633)
    ·
      refine ⟨4766198844297649803684475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6354931792396866404912633 4766198844297649803684475)
      ·
        refine ⟨7149298266446474705526713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4766198844297649803684475 7149298266446474705526713)
        ·
          refine ⟨5361973699834856029145035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7149298266446474705526713 5361973699834856029145035)
          ·
            refine ⟨8042960549752284043717553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5361973699834856029145035 8042960549752284043717553)
            ·
              refine ⟨6032220412314213032788165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8042960549752284043717553 6032220412314213032788165)
              ·
                refine ⟨1131041327308914943647781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6032220412314213032788165 1131041327308914943647781)
                ·
                  refine ⟨212070248870421551933959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1131041327308914943647781 212070248870421551933959)
                  ·
                    rfl

theorem cell21_929262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_929262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929262 prefixEnd_929262 := by exact prefixLift 929262
  have htrace : WordTrace (prefixWord ++ tailWord_929262) baseStart_929262 baseEnd_929262 := by
    simpa [prefixWord, tailWord_929262, baseEnd_929262] using wordTrace_append hprefix tailTrace_929262
  have hstable : (prefixWord ++ tailWord_929262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929262).length < 2 ^ (prefixWord ++ tailWord_929262).sum := by decide
  have hdescent : baseEnd_929262 < baseStart_929262 := by decide
  rcases family_descends (prefixWord ++ tailWord_929262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929265 : List Nat := [1, 2, 2, 2, 3, 3, 3, 2, 3]
def baseStart_929265 : Nat := 118140960795 + 929265 * 2 ^ 59
def prefixEnd_929265 : Nat := 4983230072969 + 3 ^ 40 * 929265 * 2
def baseEnd_929265 : Nat := 212070933511294213383953

theorem tailTrace_929265 : CollatzResearch.WordTrace tailWord_929265 prefixEnd_929265 212070933511294213383953 := by
  unfold tailWord_929265
  simp only [CollatzResearch.WordTrace]
  refine ⟨33893078978439085671893249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22595385985626057114595499 33893078978439085671893249)
  ·
    refine ⟨25419809233829314253919937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33893078978439085671893249 25419809233829314253919937)
    ·
      refine ⟨19064856925371985690439953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25419809233829314253919937 19064856925371985690439953)
      ·
        refine ⟨14298642694028989267829965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19064856925371985690439953 14298642694028989267829965)
        ·
          refine ⟨5361991010260870975436237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14298642694028989267829965 5361991010260870975436237)
          ·
            refine ⟨2010746628847826615788589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5361991010260870975436237 2010746628847826615788589)
            ·
              refine ⟨754029985817934980920721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2010746628847826615788589 754029985817934980920721)
              ·
                refine ⟨565522489363451235690541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754029985817934980920721 565522489363451235690541)
                ·
                  refine ⟨212070933511294213383953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565522489363451235690541 212070933511294213383953)
                  ·
                    rfl

theorem cell21_929265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 3].length) (baseStart_929265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929265 prefixEnd_929265 := by exact prefixLift 929265
  have htrace : WordTrace (prefixWord ++ tailWord_929265) baseStart_929265 baseEnd_929265 := by
    simpa [prefixWord, tailWord_929265, baseEnd_929265] using wordTrace_append hprefix tailTrace_929265
  have hstable : (prefixWord ++ tailWord_929265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929265).length < 2 ^ (prefixWord ++ tailWord_929265).sum := by decide
  have hdescent : baseEnd_929265 < baseStart_929265 := by decide
  rcases family_descends (prefixWord ++ tailWord_929265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929310 : List Nat := [4, 3, 3, 1, 10]
def baseStart_929310 : Nat := 118140960795 + 929310 * 2 ^ 59
def prefixEnd_929310 : Nat := 4983230072969 + 3 ^ 40 * 929310 * 2
def baseEnd_929310 : Nat := 2618286458325730063381

theorem tailTrace_929310 : CollatzResearch.WordTrace tailWord_929310 prefixEnd_929310 2618286458325730063381 := by
  unfold tailWord_929310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4236840032909507294660173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22596480175517372238187589 4236840032909507294660173)
  ·
    refine ⟨1588815012341065235497565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4236840032909507294660173 1588815012341065235497565)
    ·
      refine ⟨595805629627899463311587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1588815012341065235497565 595805629627899463311587)
      ·
        refine ⟨893708444441849194967381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595805629627899463311587 893708444441849194967381)
        ·
          refine ⟨2618286458325730063381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 893708444441849194967381 2618286458325730063381)
          ·
            rfl

theorem cell21_929310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 10].length) (baseStart_929310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929310 prefixEnd_929310 := by exact prefixLift 929310
  have htrace : WordTrace (prefixWord ++ tailWord_929310) baseStart_929310 baseEnd_929310 := by
    simpa [prefixWord, tailWord_929310, baseEnd_929310] using wordTrace_append hprefix tailTrace_929310
  have hstable : (prefixWord ++ tailWord_929310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929310).length < 2 ^ (prefixWord ++ tailWord_929310).sum := by decide
  have hdescent : baseEnd_929310 < baseStart_929310 := by decide
  rcases family_descends (prefixWord ++ tailWord_929310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929476 : List Nat := [2, 3, 3, 1, 1, 1, 2, 5, 3]
def baseStart_929476 : Nat := 118140960795 + 929476 * 2 ^ 59
def prefixEnd_929476 : Nat := 4983230072969 + 3 ^ 40 * 929476 * 2
def baseEnd_929476 : Nat := 212119086586004735366855

theorem tailTrace_929476 : CollatzResearch.WordTrace tailWord_929476 prefixEnd_929476 212119086586004735366855 := by
  unfold tailWord_929476
  simp only [CollatzResearch.WordTrace]
  refine ⟨16950387390337334353912141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22600516520449779138549521 16950387390337334353912141)
  ·
    refine ⟨6356395271376500382717053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16950387390337334353912141 6356395271376500382717053)
    ·
      refine ⟨2383648226766187643518895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6356395271376500382717053 2383648226766187643518895)
      ·
        refine ⟨3575472340149281465278343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2383648226766187643518895 3575472340149281465278343)
        ·
          refine ⟨5363208510223922197917515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3575472340149281465278343 5363208510223922197917515)
          ·
            refine ⟨8044812765335883296876273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5363208510223922197917515 8044812765335883296876273)
            ·
              refine ⟨6033609574001912472657205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8044812765335883296876273 6033609574001912472657205)
              ·
                refine ⟨565650897562679294311613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6033609574001912472657205 565650897562679294311613)
                ·
                  refine ⟨212119086586004735366855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565650897562679294311613 212119086586004735366855)
                  ·
                    rfl

theorem cell21_929476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_929476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929476 prefixEnd_929476 := by exact prefixLift 929476
  have htrace : WordTrace (prefixWord ++ tailWord_929476) baseStart_929476 baseEnd_929476 := by
    simpa [prefixWord, tailWord_929476, baseEnd_929476] using wordTrace_append hprefix tailTrace_929476
  have hstable : (prefixWord ++ tailWord_929476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929476).length < 2 ^ (prefixWord ++ tailWord_929476).sum := by decide
  have hdescent : baseEnd_929476 < baseStart_929476 := by decide
  rcases family_descends (prefixWord ++ tailWord_929476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929490 : List Nat := [3, 2, 2, 2, 2, 1, 1, 4, 4]
def baseStart_929490 : Nat := 118140960795 + 929490 * 2 ^ 59
def prefixEnd_929490 : Nat := 4983230072969 + 3 ^ 40 * 929490 * 2
def baseEnd_929490 : Nat := 212122281576743822133493

theorem tailTrace_929490 : CollatzResearch.WordTrace tailWord_929490 prefixEnd_929490 212122281576743822133493 := by
  unfold tailWord_929490
  simp only [CollatzResearch.WordTrace]
  refine ⟨8475321350655987274708481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22600856935082632732555949 8475321350655987274708481)
  ·
    refine ⟨6356491012991990456031361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8475321350655987274708481 6356491012991990456031361)
    ·
      refine ⟨4767368259743992842023521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6356491012991990456031361 4767368259743992842023521)
      ·
        refine ⟨3575526194807994631517641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4767368259743992842023521 3575526194807994631517641)
        ·
          refine ⟨2681644646105995973638231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3575526194807994631517641 2681644646105995973638231)
          ·
            refine ⟨4022466969158993960457347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2681644646105995973638231 4022466969158993960457347)
            ·
              refine ⟨6033700453738490940686021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4022466969158993960457347 6033700453738490940686021)
              ·
                refine ⟨1131318835075967051378629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6033700453738490940686021 1131318835075967051378629)
                ·
                  refine ⟨212122281576743822133493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1131318835075967051378629 212122281576743822133493)
                  ·
                    rfl

theorem cell21_929490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_929490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929490 prefixEnd_929490 := by exact prefixLift 929490
  have htrace : WordTrace (prefixWord ++ tailWord_929490) baseStart_929490 baseEnd_929490 := by
    simpa [prefixWord, tailWord_929490, baseEnd_929490] using wordTrace_append hprefix tailTrace_929490
  have hstable : (prefixWord ++ tailWord_929490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929490).length < 2 ^ (prefixWord ++ tailWord_929490).sum := by decide
  have hdescent : baseEnd_929490 < baseStart_929490 := by decide
  rcases family_descends (prefixWord ++ tailWord_929490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929535 : List Nat := [1, 1, 2, 2, 1, 3, 3, 5, 3]
def baseStart_929535 : Nat := 118140960795 + 929535 * 2 ^ 59
def prefixEnd_929535 : Nat := 4983230072969 + 3 ^ 40 * 929535 * 2
def baseEnd_929535 : Nat := 212132551189833743883401

theorem tailTrace_929535 : CollatzResearch.WordTrace tailWord_929535 prefixEnd_929535 212132551189833743883401 := by
  unfold tailWord_929535
  simp only [CollatzResearch.WordTrace]
  refine ⟨33902926687460921784222059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22601951124973947856148039 33902926687460921784222059)
  ·
    refine ⟨50854390031191382676333089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33902926687460921784222059 50854390031191382676333089)
    ·
      refine ⟨38140792523393537007249817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50854390031191382676333089 38140792523393537007249817)
      ·
        refine ⟨28605594392545152755437363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38140792523393537007249817 28605594392545152755437363)
        ·
          refine ⟨42908391588817729133156045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28605594392545152755437363 42908391588817729133156045)
          ·
            refine ⟨16090646845806648424933517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42908391588817729133156045 16090646845806648424933517)
            ·
              refine ⟨6033992567177493159350069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16090646845806648424933517 6033992567177493159350069)
              ·
                refine ⟨565686803172889983689069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6033992567177493159350069 565686803172889983689069)
                ·
                  refine ⟨212132551189833743883401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565686803172889983689069 212132551189833743883401)
                  ·
                    rfl

theorem cell21_929535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 3].length) (baseStart_929535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929535 prefixEnd_929535 := by exact prefixLift 929535
  have htrace : WordTrace (prefixWord ++ tailWord_929535) baseStart_929535 baseEnd_929535 := by
    simpa [prefixWord, tailWord_929535, baseEnd_929535] using wordTrace_append hprefix tailTrace_929535
  have hstable : (prefixWord ++ tailWord_929535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929535).length < 2 ^ (prefixWord ++ tailWord_929535).sum := by decide
  have hdescent : baseEnd_929535 < baseStart_929535 := by decide
  rcases family_descends (prefixWord ++ tailWord_929535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929580 : List Nat := [2, 2, 1, 1, 1, 5, 4, 5]
def baseStart_929580 : Nat := 118140960795 + 929580 * 2 ^ 59
def prefixEnd_929580 : Nat := 4983230072969 + 3 ^ 40 * 929580 * 2
def baseEnd_929580 : Nat := 70714273600974555211103

theorem tailTrace_929580 : CollatzResearch.WordTrace tailWord_929580 prefixEnd_929580 70714273600974555211103 := by
  unfold tailWord_929580
  simp only [CollatzResearch.WordTrace]
  refine ⟨16952283986148947234805097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22603045314865262979740129 16952283986148947234805097)
  ·
    refine ⟨12714212989611710426103823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16952283986148947234805097 12714212989611710426103823)
    ·
      refine ⟨19071319484417565639155735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12714212989611710426103823 19071319484417565639155735)
      ·
        refine ⟨28606979226626348458733603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19071319484417565639155735 28606979226626348458733603)
        ·
          refine ⟨42910468839939522688100405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28606979226626348458733603 42910468839939522688100405)
          ·
            refine ⟨4022856453744330252009413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42910468839939522688100405 4022856453744330252009413)
            ·
              refine ⟨754285585077061922251765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4022856453744330252009413 754285585077061922251765)
              ·
                refine ⟨70714273600974555211103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 754285585077061922251765 70714273600974555211103)
                ·
                  rfl

theorem cell21_929580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 5].length) (baseStart_929580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929580 prefixEnd_929580 := by exact prefixLift 929580
  have htrace : WordTrace (prefixWord ++ tailWord_929580) baseStart_929580 baseEnd_929580 := by
    simpa [prefixWord, tailWord_929580, baseEnd_929580] using wordTrace_append hprefix tailTrace_929580
  have hstable : (prefixWord ++ tailWord_929580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929580).length < 2 ^ (prefixWord ++ tailWord_929580).sum := by decide
  have hdescent : baseEnd_929580 < baseStart_929580 := by decide
  rcases family_descends (prefixWord ++ tailWord_929580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929625 : List Nat := [1, 2, 1, 2, 2, 3, 3, 3, 4]
def baseStart_929625 : Nat := 118140960795 + 929625 * 2 ^ 59
def prefixEnd_929625 : Nat := 4983230072969 + 3 ^ 40 * 929625 * 2
def baseEnd_929625 : Nat := 212153090416013587383217

theorem tailTrace_929625 : CollatzResearch.WordTrace tailWord_929625 prefixEnd_929625 212153090416013587383217 := by
  unfold tailWord_929625
  simp only [CollatzResearch.WordTrace]
  refine ⟨33906209257134867154998329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22604139504756578103332219 33906209257134867154998329)
  ·
    refine ⟨25429656942851150366248747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33906209257134867154998329 25429656942851150366248747)
    ·
      refine ⟨38144485414276725549373121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25429656942851150366248747 38144485414276725549373121)
      ·
        refine ⟨28608364060707544162029841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38144485414276725549373121 28608364060707544162029841)
        ·
          refine ⟨21456273045530658121522381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28608364060707544162029841 21456273045530658121522381)
          ·
            refine ⟨8046102392073996795570893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21456273045530658121522381 8046102392073996795570893)
            ·
              refine ⟨3017288397027748798339085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8046102392073996795570893 3017288397027748798339085)
              ·
                refine ⟨1131483148885405799377157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3017288397027748798339085 1131483148885405799377157)
                ·
                  refine ⟨212153090416013587383217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1131483148885405799377157 212153090416013587383217)
                  ·
                    rfl

theorem cell21_929625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_929625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929625 prefixEnd_929625 := by exact prefixLift 929625
  have htrace : WordTrace (prefixWord ++ tailWord_929625) baseStart_929625 baseEnd_929625 := by
    simpa [prefixWord, tailWord_929625, baseEnd_929625] using wordTrace_append hprefix tailTrace_929625
  have hstable : (prefixWord ++ tailWord_929625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929625).length < 2 ^ (prefixWord ++ tailWord_929625).sum := by decide
  have hdescent : baseEnd_929625 < baseStart_929625 := by decide
  rcases family_descends (prefixWord ++ tailWord_929625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929639 : List Nat := [1, 1, 5, 1, 2, 1, 1, 9]
def baseStart_929639 : Nat := 118140960795 + 929639 * 2 ^ 59
def prefixEnd_929639 : Nat := 4983230072969 + 3 ^ 40 * 929639 * 2
def baseEnd_929639 : Nat := 70718761802250891383285

theorem tailTrace_929639 : CollatzResearch.WordTrace tailWord_929639 prefixEnd_929639 70718761802250891383285 := by
  unfold tailWord_929639
  simp only [CollatzResearch.WordTrace]
  refine ⟨33906719879084147546007971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22604479919389431697338647 33906719879084147546007971)
  ·
    refine ⟨50860079818626221319011957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33906719879084147546007971 50860079818626221319011957)
    ·
      refine ⟨4768132482996208248657371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50860079818626221319011957 4768132482996208248657371)
      ·
        refine ⟨7152198724494312372986057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4768132482996208248657371 7152198724494312372986057)
        ·
          refine ⟨5364149043370734279739543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7152198724494312372986057 5364149043370734279739543)
          ·
            refine ⟨8046223565056101419609315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5364149043370734279739543 8046223565056101419609315)
            ·
              refine ⟨12069335347584152129413973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8046223565056101419609315 12069335347584152129413973)
              ·
                refine ⟨70718761802250891383285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12069335347584152129413973 70718761802250891383285)
                ·
                  rfl

theorem cell21_929639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 9].length) (baseStart_929639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929639 prefixEnd_929639 := by exact prefixLift 929639
  have htrace : WordTrace (prefixWord ++ tailWord_929639) baseStart_929639 baseEnd_929639 := by
    simpa [prefixWord, tailWord_929639, baseEnd_929639] using wordTrace_append hprefix tailTrace_929639
  have hstable : (prefixWord ++ tailWord_929639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929639).length < 2 ^ (prefixWord ++ tailWord_929639).sum := by decide
  have hdescent : baseEnd_929639 < baseStart_929639 := by decide
  rcases family_descends (prefixWord ++ tailWord_929639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929662 : List Nat := [4, 2, 3, 1, 1, 1, 4, 2, 3]
def baseStart_929662 : Nat := 118140960795 + 929662 * 2 ^ 59
def prefixEnd_929662 : Nat := 4983230072969 + 3 ^ 40 * 929662 * 2
def baseEnd_929662 : Nat := 212161534320109745266475

theorem tailTrace_929662 : CollatzResearch.WordTrace tailWord_929662 prefixEnd_929662 212161534320109745266475 := by
  unfold tailWord_929662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4238444844750102809261905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22605039172000548316063493 4238444844750102809261905)
  ·
    refine ⟨3178833633562577106946429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4238444844750102809261905 3178833633562577106946429)
    ·
      refine ⟨1192062612585966415104911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3178833633562577106946429 1192062612585966415104911)
      ·
        refine ⟨1788093918878949622657367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1192062612585966415104911 1788093918878949622657367)
        ·
          refine ⟨2682140878318424433986051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1788093918878949622657367 2682140878318424433986051)
          ·
            refine ⟨4023211317477636650979077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2682140878318424433986051 4023211317477636650979077)
            ·
              refine ⟨754352122027056872058577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4023211317477636650979077 754352122027056872058577)
              ·
                refine ⟨565764091520292654043933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754352122027056872058577 565764091520292654043933)
                ·
                  refine ⟨212161534320109745266475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565764091520292654043933 212161534320109745266475)
                  ·
                    rfl

theorem cell21_929662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_929662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929662 prefixEnd_929662 := by exact prefixLift 929662
  have htrace : WordTrace (prefixWord ++ tailWord_929662) baseStart_929662 baseEnd_929662 := by
    simpa [prefixWord, tailWord_929662, baseEnd_929662] using wordTrace_append hprefix tailTrace_929662
  have hstable : (prefixWord ++ tailWord_929662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929662).length < 2 ^ (prefixWord ++ tailWord_929662).sum := by decide
  have hdescent : baseEnd_929662 < baseStart_929662 := by decide
  rcases family_descends (prefixWord ++ tailWord_929662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929710 : List Nat := [4, 1, 5, 1, 2, 1, 1, 2, 4]
def baseStart_929710 : Nat := 118140960795 + 929710 * 2 ^ 59
def prefixEnd_929710 : Nat := 4983230072969 + 3 ^ 40 * 929710 * 2
def baseEnd_929710 : Nat := 212172488574072328466377

theorem tailTrace_929710 : CollatzResearch.WordTrace tailWord_929710 prefixEnd_929710 212172488574072328466377 := by
  unfold tailWord_929710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4238663682728365833980323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22606206307884617781228389 4238663682728365833980323)
  ·
    refine ⟨6357995524092548750970485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4238663682728365833980323 6357995524092548750970485)
    ·
      refine ⟨596062080383676445403483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6357995524092548750970485 596062080383676445403483)
      ·
        refine ⟨894093120575514668105225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596062080383676445403483 894093120575514668105225)
        ·
          refine ⟨670569840431636001078919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 894093120575514668105225 670569840431636001078919)
          ·
            refine ⟨1005854760647454001618379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670569840431636001078919 1005854760647454001618379)
            ·
              refine ⟨1508782140971181002427569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005854760647454001618379 1508782140971181002427569)
              ·
                refine ⟨1131586605728385751820677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1508782140971181002427569 1131586605728385751820677)
                ·
                  refine ⟨212172488574072328466377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1131586605728385751820677 212172488574072328466377)
                  ·
                    rfl

theorem cell21_929710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_929710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929710 prefixEnd_929710 := by exact prefixLift 929710
  have htrace : WordTrace (prefixWord ++ tailWord_929710) baseStart_929710 baseEnd_929710 := by
    simpa [prefixWord, tailWord_929710, baseEnd_929710] using wordTrace_append hprefix tailTrace_929710
  have hstable : (prefixWord ++ tailWord_929710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929710).length < 2 ^ (prefixWord ++ tailWord_929710).sum := by decide
  have hdescent : baseEnd_929710 < baseStart_929710 := by decide
  rcases family_descends (prefixWord ++ tailWord_929710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929749 : List Nat := [1, 3, 2, 3, 2, 3, 2, 5]
def baseStart_929749 : Nat := 118140960795 + 929749 * 2 ^ 59
def prefixEnd_929749 : Nat := 4983230072969 + 3 ^ 40 * 929749 * 2
def baseEnd_929749 : Nat := 70727129635138975772099

theorem tailTrace_929749 : CollatzResearch.WordTrace tailWord_929749 prefixEnd_929749 70727129635138975772099 := by
  unfold tailWord_929749
  simp only [CollatzResearch.WordTrace]
  refine ⟨33910731908685636332512301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22607154605790424221674867 33910731908685636332512301)
  ·
    refine ⟨12716524465757113624692113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33910731908685636332512301 12716524465757113624692113)
    ·
      refine ⟨9537393349317835218519085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12716524465757113624692113 9537393349317835218519085)
      ·
        refine ⟨3576522505994188206944657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9537393349317835218519085 3576522505994188206944657)
        ·
          refine ⟨2682391879495641155208493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3576522505994188206944657 2682391879495641155208493)
          ·
            refine ⟨1005896954810865433203185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2682391879495641155208493 1005896954810865433203185)
            ·
              refine ⟨754422716108149074902389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1005896954810865433203185 754422716108149074902389)
              ·
                refine ⟨70727129635138975772099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 754422716108149074902389 70727129635138975772099)
                ·
                  rfl

theorem cell21_929749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 5].length) (baseStart_929749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929749 prefixEnd_929749 := by exact prefixLift 929749
  have htrace : WordTrace (prefixWord ++ tailWord_929749) baseStart_929749 baseEnd_929749 := by
    simpa [prefixWord, tailWord_929749, baseEnd_929749] using wordTrace_append hprefix tailTrace_929749
  have hstable : (prefixWord ++ tailWord_929749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929749).length < 2 ^ (prefixWord ++ tailWord_929749).sum := by decide
  have hdescent : baseEnd_929749 < baseStart_929749 := by decide
  rcases family_descends (prefixWord ++ tailWord_929749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929831 : List Nat := [1, 1, 7, 1, 3, 1, 2, 2, 3]
def baseStart_929831 : Nat := 118140960795 + 929831 * 2 ^ 59
def prefixEnd_929831 : Nat := 4983230072969 + 3 ^ 40 * 929831 * 2
def baseEnd_929831 : Nat := 212200102422603006949463

theorem tailTrace_929831 : CollatzResearch.WordTrace tailWord_929831 prefixEnd_929831 212200102422603006949463 := by
  unfold tailWord_929831
  simp only [CollatzResearch.WordTrace]
  refine ⟨33913722694388564336997347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22609148462925709557998231 33913722694388564336997347)
  ·
    refine ⟨50870584041582846505496021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33913722694388564336997347 50870584041582846505496021)
    ·
      refine ⟨1192279313474597964972563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 50870584041582846505496021 1192279313474597964972563)
      ·
        refine ⟨1788418970211896947458845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1192279313474597964972563 1788418970211896947458845)
        ·
          refine ⟨670657113829461355297067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1788418970211896947458845 670657113829461355297067)
          ·
            refine ⟨1005985670744192032945601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670657113829461355297067 1005985670744192032945601)
            ·
              refine ⟨754489253058144024709201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1005985670744192032945601 754489253058144024709201)
              ·
                refine ⟨565866939793608018531901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754489253058144024709201 565866939793608018531901)
                ·
                  refine ⟨212200102422603006949463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565866939793608018531901 212200102422603006949463)
                  ·
                    rfl

theorem cell21_929831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 3].length) (baseStart_929831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929831 prefixEnd_929831 := by exact prefixLift 929831
  have htrace : WordTrace (prefixWord ++ tailWord_929831) baseStart_929831 baseEnd_929831 := by
    simpa [prefixWord, tailWord_929831, baseEnd_929831] using wordTrace_append hprefix tailTrace_929831
  have hstable : (prefixWord ++ tailWord_929831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929831).length < 2 ^ (prefixWord ++ tailWord_929831).sum := by decide
  have hdescent : baseEnd_929831 < baseStart_929831 := by decide
  rcases family_descends (prefixWord ++ tailWord_929831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929853 : List Nat := [1, 4, 1, 3, 1, 1, 1, 5, 4]
def baseStart_929853 : Nat := 118140960795 + 929853 * 2 ^ 59
def prefixEnd_929853 : Nat := 4983230072969 + 3 ^ 40 * 929853 * 2
def baseEnd_929853 : Nat := 212205123122335857582751

theorem tailTrace_929853 : CollatzResearch.WordTrace tailWord_929853 prefixEnd_929853 212205123122335857582751 := by
  unfold tailWord_929853
  simp only [CollatzResearch.WordTrace]
  refine ⟨33914525100308862094298213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22609683400205908062865475 33914525100308862094298213)
  ·
    refine ⟨6358973456307911642680915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33914525100308862094298213 6358973456307911642680915)
    ·
      refine ⟨9538460184461867464021373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6358973456307911642680915 9538460184461867464021373)
      ·
        refine ⟨3576922569173200299008015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9538460184461867464021373 3576922569173200299008015)
        ·
          refine ⟨5365383853759800448512023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3576922569173200299008015 5365383853759800448512023)
          ·
            refine ⟨8048075780639700672768035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5365383853759800448512023 8048075780639700672768035)
            ·
              refine ⟨12072113670959551009152053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8048075780639700672768035 12072113670959551009152053)
              ·
                refine ⟨1131760656652457907108005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12072113670959551009152053 1131760656652457907108005)
                ·
                  refine ⟨212205123122335857582751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1131760656652457907108005 212205123122335857582751)
                  ·
                    rfl

theorem cell21_929853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_929853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929853 prefixEnd_929853 := by exact prefixLift 929853
  have htrace : WordTrace (prefixWord ++ tailWord_929853) baseStart_929853 baseEnd_929853 := by
    simpa [prefixWord, tailWord_929853, baseEnd_929853] using wordTrace_append hprefix tailTrace_929853
  have hstable : (prefixWord ++ tailWord_929853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929853).length < 2 ^ (prefixWord ++ tailWord_929853).sum := by decide
  have hdescent : baseEnd_929853 < baseStart_929853 := by decide
  rcases family_descends (prefixWord ++ tailWord_929853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929881 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 7]
def baseStart_929881 : Nat := 118140960795 + 929881 * 2 ^ 59
def prefixEnd_929881 : Nat := 4983230072969 + 3 ^ 40 * 929881 * 2
def baseEnd_929881 : Nat := 212211513103814031116027

theorem tailTrace_929881 : CollatzResearch.WordTrace tailWord_929881 prefixEnd_929881 212211513103814031116027 := by
  unfold tailWord_929881
  simp only [CollatzResearch.WordTrace]
  refine ⟨33915546344207422876317497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22610364229471615250878331 33915546344207422876317497)
  ·
    refine ⟨25436659758155567157238123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33915546344207422876317497 25436659758155567157238123)
    ·
      refine ⟨38154989637233350735857185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25436659758155567157238123 38154989637233350735857185)
      ·
        refine ⟨28616242227925013051892889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38154989637233350735857185 28616242227925013051892889)
        ·
          refine ⟨21462181670943759788919667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28616242227925013051892889 21462181670943759788919667)
          ·
            refine ⟨32193272506415639683379501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21462181670943759788919667 32193272506415639683379501)
            ·
              refine ⟨12072477189905864881267313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32193272506415639683379501 12072477189905864881267313)
              ·
                refine ⟨9054357892429398660950485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12072477189905864881267313 9054357892429398660950485)
                ·
                  refine ⟨212211513103814031116027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9054357892429398660950485 212211513103814031116027)
                  ·
                    rfl

theorem cell21_929881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_929881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_929881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_929881 prefixEnd_929881 := by exact prefixLift 929881
  have htrace : WordTrace (prefixWord ++ tailWord_929881) baseStart_929881 baseEnd_929881 := by
    simpa [prefixWord, tailWord_929881, baseEnd_929881] using wordTrace_append hprefix tailTrace_929881
  have hstable : (prefixWord ++ tailWord_929881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929881).length < 2 ^ (prefixWord ++ tailWord_929881).sum := by decide
  have hdescent : baseEnd_929881 < baseStart_929881 := by decide
  rcases family_descends (prefixWord ++ tailWord_929881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930008 : List Nat := [2, 1, 2, 2, 4, 1, 4, 2, 3]
def baseStart_930008 : Nat := 118140960795 + 930008 * 2 ^ 59
def prefixEnd_930008 : Nat := 4983230072969 + 3 ^ 40 * 930008 * 2
def baseEnd_930008 : Nat := 212240496234090032499101

theorem tailTrace_930008 : CollatzResearch.WordTrace tailWord_930008 prefixEnd_930008 212240496234090032499101 := by
  unfold tailWord_930008
  simp only [CollatzResearch.WordTrace]
  refine ⟨16960089207373661783095339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22613452276498215710793785 16960089207373661783095339)
  ·
    refine ⟨25440133811060492674643009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16960089207373661783095339 25440133811060492674643009)
    ·
      refine ⟨19080100358295369505982257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25440133811060492674643009 19080100358295369505982257)
      ·
        refine ⟨14310075268721527129486693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19080100358295369505982257 14310075268721527129486693)
        ·
          refine ⟨2683139112885286336778755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14310075268721527129486693 2683139112885286336778755)
          ·
            refine ⟨4024708669327929505168133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2683139112885286336778755 4024708669327929505168133)
            ·
              refine ⟨754632875498986782219025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4024708669327929505168133 754632875498986782219025)
              ·
                refine ⟨565974656624240086664269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754632875498986782219025 565974656624240086664269)
                ·
                  refine ⟨212240496234090032499101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565974656624240086664269 212240496234090032499101)
                  ·
                    rfl

theorem cell21_930008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 3].length) (baseStart_930008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930008 prefixEnd_930008 := by exact prefixLift 930008
  have htrace : WordTrace (prefixWord ++ tailWord_930008) baseStart_930008 baseEnd_930008 := by
    simpa [prefixWord, tailWord_930008, baseEnd_930008] using wordTrace_append hprefix tailTrace_930008
  have hstable : (prefixWord ++ tailWord_930008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930008).length < 2 ^ (prefixWord ++ tailWord_930008).sum := by decide
  have hdescent : baseEnd_930008 < baseStart_930008 := by decide
  rcases family_descends (prefixWord ++ tailWord_930008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930033 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 7]
def baseStart_930033 : Nat := 118140960795 + 930033 * 2 ^ 59
def prefixEnd_930033 : Nat := 4983230072969 + 3 ^ 40 * 930033 * 2
def baseEnd_930033 : Nat := 212246201574695544582383

theorem tailTrace_930033 : CollatzResearch.WordTrace tailWord_930033 prefixEnd_930033 212246201574695544582383 := by
  unfold tailWord_930033
  simp only [CollatzResearch.WordTrace]
  refine ⟨33921090239656752835850753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22614060159771168557233835 33921090239656752835850753)
  ·
    refine ⟨25440817679742564626888065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33921090239656752835850753 25440817679742564626888065)
    ·
      refine ⟨19080613259806923470166049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25440817679742564626888065 19080613259806923470166049)
      ·
        refine ⟨14310459944855192602624537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19080613259806923470166049 14310459944855192602624537)
        ·
          refine ⟨10732844958641394451968403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14310459944855192602624537 10732844958641394451968403)
          ·
            refine ⟨16099267437962091677952605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10732844958641394451968403 16099267437962091677952605)
            ·
              refine ⟨6037225289235784379232227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16099267437962091677952605 6037225289235784379232227)
              ·
                refine ⟨9055837933853676568848341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6037225289235784379232227 9055837933853676568848341)
                ·
                  refine ⟨212246201574695544582383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9055837933853676568848341 212246201574695544582383)
                  ·
                    rfl

theorem cell21_930033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_930033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930033 prefixEnd_930033 := by exact prefixLift 930033
  have htrace : WordTrace (prefixWord ++ tailWord_930033) baseStart_930033 baseEnd_930033 := by
    simpa [prefixWord, tailWord_930033, baseEnd_930033] using wordTrace_append hprefix tailTrace_930033
  have hstable : (prefixWord ++ tailWord_930033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930033).length < 2 ^ (prefixWord ++ tailWord_930033).sum := by decide
  have hdescent : baseEnd_930033 < baseStart_930033 := by decide
  rcases family_descends (prefixWord ++ tailWord_930033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930087 : List Nat := [1, 1, 8, 1, 1, 2, 2, 5]
def baseStart_930087 : Nat := 118140960795 + 930087 * 2 ^ 59
def prefixEnd_930087 : Nat := 4983230072969 + 3 ^ 40 * 930087 * 2
def baseEnd_930087 : Nat := 70752841703467816894091

theorem tailTrace_930087 : CollatzResearch.WordTrace tailWord_930087 prefixEnd_930087 70752841703467816894091 := by
  unfold tailWord_930087
  simp only [CollatzResearch.WordTrace]
  refine ⟨33923059781461120058316515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22615373187640746705544343 33923059781461120058316515)
  ·
    refine ⟨50884589672191680087474773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33923059781461120058316515 50884589672191680087474773)
    ·
      refine ⟨596303785220996251025095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 50884589672191680087474773 596303785220996251025095)
      ·
        refine ⟨894455677831494376537643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596303785220996251025095 894455677831494376537643)
        ·
          refine ⟨1341683516747241564806465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894455677831494376537643 1341683516747241564806465)
          ·
            refine ⟨1006262637560431173604849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1341683516747241564806465 1006262637560431173604849)
            ·
              refine ⟨754696978170323380203637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1006262637560431173604849 754696978170323380203637)
              ·
                refine ⟨70752841703467816894091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 754696978170323380203637 70752841703467816894091)
                ·
                  rfl

theorem cell21_930087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 5].length) (baseStart_930087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930087 prefixEnd_930087 := by exact prefixLift 930087
  have htrace : WordTrace (prefixWord ++ tailWord_930087) baseStart_930087 baseEnd_930087 := by
    simpa [prefixWord, tailWord_930087, baseEnd_930087] using wordTrace_append hprefix tailTrace_930087
  have hstable : (prefixWord ++ tailWord_930087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930087).length < 2 ^ (prefixWord ++ tailWord_930087).sum := by decide
  have hdescent : baseEnd_930087 < baseStart_930087 := by decide
  rcases family_descends (prefixWord ++ tailWord_930087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930095 : List Nat := [1, 1, 2, 1, 2, 1, 8, 5]
def baseStart_930095 : Nat := 118140960795 + 930095 * 2 ^ 59
def prefixEnd_930095 : Nat := 4983230072969 + 3 ^ 40 * 930095 * 2
def baseEnd_930095 : Nat := 70753450273132404849641

theorem tailTrace_930095 : CollatzResearch.WordTrace tailWord_930095 prefixEnd_930095 70753450273132404849641 := by
  unfold tailWord_930095
  simp only [CollatzResearch.WordTrace]
  refine ⟨33923351565432137424607739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22615567710288091616405159 33923351565432137424607739)
  ·
    refine ⟨50885027348148206136911609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33923351565432137424607739 50885027348148206136911609)
    ·
      refine ⟨38163770511111154602683707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50885027348148206136911609 38163770511111154602683707)
      ·
        refine ⟨57245655766666731904025561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38163770511111154602683707 57245655766666731904025561)
        ·
          refine ⟨42934241825000048928019171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57245655766666731904025561 42934241825000048928019171)
          ·
            refine ⟨64401362737500073392028757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42934241825000048928019171 64401362737500073392028757)
            ·
              refine ⟨754703469580078985062837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 64401362737500073392028757 754703469580078985062837)
              ·
                refine ⟨70753450273132404849641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 754703469580078985062837 70753450273132404849641)
                ·
                  rfl

theorem cell21_930095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 5].length) (baseStart_930095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930095 prefixEnd_930095 := by exact prefixLift 930095
  have htrace : WordTrace (prefixWord ++ tailWord_930095) baseStart_930095 baseEnd_930095 := by
    simpa [prefixWord, tailWord_930095, baseEnd_930095] using wordTrace_append hprefix tailTrace_930095
  have hstable : (prefixWord ++ tailWord_930095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930095).length < 2 ^ (prefixWord ++ tailWord_930095).sum := by decide
  have hdescent : baseEnd_930095 < baseStart_930095 := by decide
  rcases family_descends (prefixWord ++ tailWord_930095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930177 : List Nat := [1, 2, 4, 3, 1, 3, 2, 2, 3]
def baseStart_930177 : Nat := 118140960795 + 930177 * 2 ^ 59
def prefixEnd_930177 : Nat := 4983230072969 + 3 ^ 40 * 930177 * 2
def baseEnd_930177 : Nat := 212279064336583294182089

theorem tailTrace_930177 : CollatzResearch.WordTrace tailWord_930177 prefixEnd_930177 212279064336583294182089 := by
  unfold tailWord_930177
  simp only [CollatzResearch.WordTrace]
  refine ⟨33926342351135065429092785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22617561567423376952728523 33926342351135065429092785)
  ·
    refine ⟨25444756763351299071819589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33926342351135065429092785 25444756763351299071819589)
    ·
      refine ⟨4770891893128368575966173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25444756763351299071819589 4770891893128368575966173)
      ·
        refine ⟨1789084459923138215987315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4770891893128368575966173 1789084459923138215987315)
        ·
          refine ⟨2683626689884707323980973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1789084459923138215987315 2683626689884707323980973)
          ·
            refine ⟨1006360008706765246492865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2683626689884707323980973 1006360008706765246492865)
            ·
              refine ⟨754770006530073934869649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1006360008706765246492865 754770006530073934869649)
              ·
                refine ⟨566077504897555451152237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754770006530073934869649 566077504897555451152237)
                ·
                  refine ⟨212279064336583294182089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 566077504897555451152237 212279064336583294182089)
                  ·
                    rfl

theorem cell21_930177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 3].length) (baseStart_930177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930177 prefixEnd_930177 := by exact prefixLift 930177
  have htrace : WordTrace (prefixWord ++ tailWord_930177) baseStart_930177 baseEnd_930177 := by
    simpa [prefixWord, tailWord_930177, baseEnd_930177] using wordTrace_append hprefix tailTrace_930177
  have hstable : (prefixWord ++ tailWord_930177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930177).length < 2 ^ (prefixWord ++ tailWord_930177).sum := by decide
  have hdescent : baseEnd_930177 < baseStart_930177 := by decide
  rcases family_descends (prefixWord ++ tailWord_930177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930202 : List Nat := [3, 1, 1, 4, 1, 3, 1, 2, 5]
def baseStart_930202 : Nat := 118140960795 + 930202 * 2 ^ 59
def prefixEnd_930202 : Nat := 4983230072969 + 3 ^ 40 * 930202 * 2
def baseEnd_930202 : Nat := 212284769677188806265371

theorem tailTrace_930202 : CollatzResearch.WordTrace tailWord_930202 prefixEnd_930202 212284769677188806265371 := by
  unfold tailWord_930202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8481813544011123674688215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22618169450696329799168573 8481813544011123674688215)
  ·
    refine ⟨12722720316016685512032323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8481813544011123674688215 12722720316016685512032323)
    ·
      refine ⟨19084080474025028268048485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12722720316016685512032323 19084080474025028268048485)
      ·
        refine ⟨3578265088879692800259091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19084080474025028268048485 3578265088879692800259091)
        ·
          refine ⟨5367397633319539200388637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3578265088879692800259091 5367397633319539200388637)
          ·
            refine ⟨2012774112494827200145739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5367397633319539200388637 2012774112494827200145739)
            ·
              refine ⟨3019161168742240800218609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012774112494827200145739 3019161168742240800218609)
              ·
                refine ⟨2264370876556680600163957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3019161168742240800218609 2264370876556680600163957)
                ·
                  refine ⟨212284769677188806265371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2264370876556680600163957 212284769677188806265371)
                  ·
                    rfl

theorem cell21_930202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_930202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930202 prefixEnd_930202 := by exact prefixLift 930202
  have htrace : WordTrace (prefixWord ++ tailWord_930202) baseStart_930202 baseEnd_930202 := by
    simpa [prefixWord, tailWord_930202, baseEnd_930202] using wordTrace_append hprefix tailTrace_930202
  have hstable : (prefixWord ++ tailWord_930202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930202).length < 2 ^ (prefixWord ++ tailWord_930202).sum := by decide
  have hdescent : baseEnd_930202 < baseStart_930202 := by decide
  rcases family_descends (prefixWord ++ tailWord_930202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930233 : List Nat := [1, 2, 1, 4, 3, 1, 3, 2, 4]
def baseStart_930233 : Nat := 118140960795 + 930233 * 2 ^ 59
def prefixEnd_930233 : Nat := 4983230072969 + 3 ^ 40 * 930233 * 2
def baseEnd_930233 : Nat := 212291844299539641248641

theorem tailTrace_930233 : CollatzResearch.WordTrace tailWord_930233 prefixEnd_930233 212291844299539641248641 := by
  unfold tailWord_930233
  simp only [CollatzResearch.WordTrace]
  refine ⟨33928384838932186993131353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22618923225954791328754235 33928384838932186993131353)
  ·
    refine ⟨25446288629199140244848515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33928384838932186993131353 25446288629199140244848515)
    ·
      refine ⟨38169432943798710367272773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25446288629199140244848515 38169432943798710367272773)
      ·
        refine ⟨7156768676962258193863645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38169432943798710367272773 7156768676962258193863645)
        ·
          refine ⟨2683788253860846822698867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7156768676962258193863645 2683788253860846822698867)
          ·
            refine ⟨4025682380791270234048301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2683788253860846822698867 4025682380791270234048301)
            ·
              refine ⟨1509630892796726337768113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4025682380791270234048301 1509630892796726337768113)
              ·
                refine ⟨1132223169597544753326085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1509630892796726337768113 1132223169597544753326085)
                ·
                  refine ⟨212291844299539641248641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1132223169597544753326085 212291844299539641248641)
                  ·
                    rfl

theorem cell21_930233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_930233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930233 prefixEnd_930233 := by exact prefixLift 930233
  have htrace : WordTrace (prefixWord ++ tailWord_930233) baseStart_930233 baseEnd_930233 := by
    simpa [prefixWord, tailWord_930233, baseEnd_930233] using wordTrace_append hprefix tailTrace_930233
  have hstable : (prefixWord ++ tailWord_930233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930233).length < 2 ^ (prefixWord ++ tailWord_930233).sum := by decide
  have hdescent : baseEnd_930233 < baseStart_930233 := by decide
  rcases family_descends (prefixWord ++ tailWord_930233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930309 : List Nat := [1, 3, 1, 1, 2, 2, 6, 1, 4]
def baseStart_930309 : Nat := 118140960795 + 930309 * 2 ^ 59
def prefixEnd_930309 : Nat := 4983230072969 + 3 ^ 40 * 930309 * 2
def baseEnd_930309 : Nat := 212309188534980397981819

theorem tailTrace_930309 : CollatzResearch.WordTrace tailWord_930309 prefixEnd_930309 212309188534980397981819 := by
  unfold tailWord_930309
  simp only [CollatzResearch.WordTrace]
  refine ⟨33931156786656851972897981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22620771191104567981931987 33931156786656851972897981)
  ·
    refine ⟨12724183794996319489836743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33931156786656851972897981 12724183794996319489836743)
    ·
      refine ⟨19086275692494479234755115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12724183794996319489836743 19086275692494479234755115)
      ·
        refine ⟨28629413538741718852132673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19086275692494479234755115 28629413538741718852132673)
        ·
          refine ⟨21472060154056289139099505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28629413538741718852132673 21472060154056289139099505)
          ·
            refine ⟨16104045115542216854324629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21472060154056289139099505 16104045115542216854324629)
            ·
              refine ⟨754877114791041415046467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16104045115542216854324629 754877114791041415046467)
              ·
                refine ⟨1132315672186562122569701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 754877114791041415046467 1132315672186562122569701)
                ·
                  refine ⟨212309188534980397981819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1132315672186562122569701 212309188534980397981819)
                  ·
                    rfl

theorem cell21_930309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_930309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930309 prefixEnd_930309 := by exact prefixLift 930309
  have htrace : WordTrace (prefixWord ++ tailWord_930309) baseStart_930309 baseEnd_930309 := by
    simpa [prefixWord, tailWord_930309, baseEnd_930309] using wordTrace_append hprefix tailTrace_930309
  have hstable : (prefixWord ++ tailWord_930309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930309).length < 2 ^ (prefixWord ++ tailWord_930309).sum := by decide
  have hdescent : baseEnd_930309 < baseStart_930309 := by decide
  rcases family_descends (prefixWord ++ tailWord_930309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930340 : List Nat := [2, 3, 1, 5, 2, 8]
def baseStart_930340 : Nat := 118140960795 + 930340 * 2 ^ 59
def prefixEnd_930340 : Nat := 4983230072969 + 3 ^ 40 * 930340 * 2
def baseEnd_930340 : Nat := 7863565302123378998707

theorem tailTrace_930340 : CollatzResearch.WordTrace tailWord_930340 prefixEnd_930340 7863565302123378998707 := by
  unfold tailWord_930340
  simp only [CollatzResearch.WordTrace]
  refine ⟨16966143724772272133638237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22621524966363029511517649 16966143724772272133638237)
  ·
    refine ⟨6362303896789602050114339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16966143724772272133638237 6362303896789602050114339)
    ·
      refine ⟨9543455845184403075171509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6362303896789602050114339 9543455845184403075171509)
      ·
        refine ⟨894698985486037788297329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9543455845184403075171509 894698985486037788297329)
        ·
          refine ⟨671024239114528341222997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 894698985486037788297329 671024239114528341222997)
          ·
            refine ⟨7863565302123378998707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 671024239114528341222997 7863565302123378998707)
            ·
              rfl

theorem cell21_930340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 8].length) (baseStart_930340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930340 prefixEnd_930340 := by exact prefixLift 930340
  have htrace : WordTrace (prefixWord ++ tailWord_930340) baseStart_930340 baseEnd_930340 := by
    simpa [prefixWord, tailWord_930340, baseEnd_930340] using wordTrace_append hprefix tailTrace_930340
  have hstable : (prefixWord ++ tailWord_930340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930340).length < 2 ^ (prefixWord ++ tailWord_930340).sum := by decide
  have hdescent : baseEnd_930340 < baseStart_930340 := by decide
  rcases family_descends (prefixWord ++ tailWord_930340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930343 : List Nat := [1, 1, 7, 2, 1, 1, 2, 2, 4]
def baseStart_930343 : Nat := 118140960795 + 930343 * 2 ^ 59
def prefixEnd_930343 : Nat := 4983230072969 + 3 ^ 40 * 930343 * 2
def baseEnd_930343 : Nat := 212316947798203894415083

theorem tailTrace_930343 : CollatzResearch.WordTrace tailWord_930343 prefixEnd_930343 212316947798203894415083 := by
  unfold tailWord_930343
  simp only [CollatzResearch.WordTrace]
  refine ⟨33932396868533675779635683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22621597912355783853090455 33932396868533675779635683)
  ·
    refine ⟨50898595302800513669453525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33932396868533675779635683 50898595302800513669453525)
    ·
      refine ⟨1192935827409387039127817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 50898595302800513669453525 1192935827409387039127817)
      ·
        refine ⟨894701870557040279345863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1192935827409387039127817 894701870557040279345863)
        ·
          refine ⟨1342052805835560419018795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894701870557040279345863 1342052805835560419018795)
          ·
            refine ⟨2013079208753340628528193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1342052805835560419018795 2013079208753340628528193)
            ·
              refine ⟨1509809406565005471396145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2013079208753340628528193 1509809406565005471396145)
              ·
                refine ⟨1132357054923754103547109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1509809406565005471396145 1132357054923754103547109)
                ·
                  refine ⟨212316947798203894415083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1132357054923754103547109 212316947798203894415083)
                  ·
                    rfl

theorem cell21_930343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 4].length) (baseStart_930343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930343 prefixEnd_930343 := by exact prefixLift 930343
  have htrace : WordTrace (prefixWord ++ tailWord_930343) baseStart_930343 baseEnd_930343 := by
    simpa [prefixWord, tailWord_930343, baseEnd_930343] using wordTrace_append hprefix tailTrace_930343
  have hstable : (prefixWord ++ tailWord_930343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930343).length < 2 ^ (prefixWord ++ tailWord_930343).sum := by decide
  have hdescent : baseEnd_930343 < baseStart_930343 := by decide
  rcases family_descends (prefixWord ++ tailWord_930343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930368 : List Nat := [2, 1, 1, 2, 2, 2, 4, 3, 4]
def baseStart_930368 : Nat := 118140960795 + 930368 * 2 ^ 59
def prefixEnd_930368 : Nat := 4983230072969 + 3 ^ 40 * 930368 * 2
def baseEnd_930368 : Nat := 212322653138809406498365

theorem tailTrace_930368 : CollatzResearch.WordTrace tailWord_930368 prefixEnd_930368 212322653138809406498365 := by
  unfold tailWord_930368
  simp only [CollatzResearch.WordTrace]
  refine ⟨16966654346721552524647879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22622205795628736699530505 16966654346721552524647879)
  ·
    refine ⟨25449981520082328786971819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16966654346721552524647879 25449981520082328786971819)
    ·
      refine ⟨38174972280123493180457729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25449981520082328786971819 38174972280123493180457729)
      ·
        refine ⟨28631229210092619885343297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38174972280123493180457729 28631229210092619885343297)
        ·
          refine ⟨21473421907569464914007473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28631229210092619885343297 21473421907569464914007473)
          ·
            refine ⟨16105066430677098685505605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21473421907569464914007473 16105066430677098685505605)
            ·
              refine ⟨3019699955751956003532301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16105066430677098685505605 3019699955751956003532301)
              ·
                refine ⟨1132387483406983501324613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3019699955751956003532301 1132387483406983501324613)
                ·
                  refine ⟨212322653138809406498365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1132387483406983501324613 212322653138809406498365)
                  ·
                    rfl

theorem cell21_930368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_930368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930368 prefixEnd_930368 := by exact prefixLift 930368
  have htrace : WordTrace (prefixWord ++ tailWord_930368) baseStart_930368 baseEnd_930368 := by
    simpa [prefixWord, tailWord_930368, baseEnd_930368] using wordTrace_append hprefix tailTrace_930368
  have hstable : (prefixWord ++ tailWord_930368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930368).length < 2 ^ (prefixWord ++ tailWord_930368).sum := by decide
  have hdescent : baseEnd_930368 < baseStart_930368 := by decide
  rcases family_descends (prefixWord ++ tailWord_930368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930382 : List Nat := [4, 1, 1, 1, 1, 2, 2, 9]
def baseStart_930382 : Nat := 118140960795 + 930382 * 2 ^ 59
def prefixEnd_930382 : Nat := 4983230072969 + 3 ^ 40 * 930382 * 2
def baseEnd_930382 : Nat := 70775282709849497755001

theorem tailTrace_930382 : CollatzResearch.WordTrace tailWord_930382 prefixEnd_930382 70775282709849497755001 := by
  unfold tailWord_930382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4241727414424048180038175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22622546210261590293536933 4241727414424048180038175)
  ·
    refine ⟨6362591121636072270057263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4241727414424048180038175 6362591121636072270057263)
    ·
      refine ⟨9543886682454108405085895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6362591121636072270057263 9543886682454108405085895)
      ·
        refine ⟨14315830023681162607628843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9543886682454108405085895 14315830023681162607628843)
        ·
          refine ⟨21473745035521743911443265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14315830023681162607628843 21473745035521743911443265)
          ·
            refine ⟨16105308776641307933582449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21473745035521743911443265 16105308776641307933582449)
            ·
              refine ⟨12078981582480980950186837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16105308776641307933582449 12078981582480980950186837)
              ·
                refine ⟨70775282709849497755001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12078981582480980950186837 70775282709849497755001)
                ·
                  rfl

theorem cell21_930382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_930382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930382 prefixEnd_930382 := by exact prefixLift 930382
  have htrace : WordTrace (prefixWord ++ tailWord_930382) baseStart_930382 baseEnd_930382 := by
    simpa [prefixWord, tailWord_930382, baseEnd_930382] using wordTrace_append hprefix tailTrace_930382
  have hstable : (prefixWord ++ tailWord_930382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930382).length < 2 ^ (prefixWord ++ tailWord_930382).sum := by decide
  have hdescent : baseEnd_930382 < baseStart_930382 := by decide
  rcases family_descends (prefixWord ++ tailWord_930382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930402 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 6]
def baseStart_930402 : Nat := 118140960795 + 930402 * 2 ^ 59
def prefixEnd_930402 : Nat := 4983230072969 + 3 ^ 40 * 930402 * 2
def baseEnd_930402 : Nat := 212330412402032902931629

theorem tailTrace_930402 : CollatzResearch.WordTrace tailWord_930402 prefixEnd_930402 212330412402032902931629 := by
  unfold tailWord_930402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8483637193829982214008365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22623032516879952570688973 8483637193829982214008365)
  ·
    refine ⟨3181363947686243330253137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8483637193829982214008365 3181363947686243330253137)
    ·
      refine ⟨2386022960764682497689853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3181363947686243330253137 2386022960764682497689853)
      ·
        refine ⟨894758610286755936633695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2386022960764682497689853 894758610286755936633695)
        ·
          refine ⟨1342137915430133904950543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894758610286755936633695 1342137915430133904950543)
          ·
            refine ⟨2013206873145200857425815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1342137915430133904950543 2013206873145200857425815)
            ·
              refine ⟨3019810309717801286138723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2013206873145200857425815 3019810309717801286138723)
              ·
                refine ⟨4529715464576701929208085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3019810309717801286138723 4529715464576701929208085)
                ·
                  refine ⟨212330412402032902931629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4529715464576701929208085 212330412402032902931629)
                  ·
                    rfl

theorem cell21_930402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_930402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930402 prefixEnd_930402 := by exact prefixLift 930402
  have htrace : WordTrace (prefixWord ++ tailWord_930402) baseStart_930402 baseEnd_930402 := by
    simpa [prefixWord, tailWord_930402, baseEnd_930402] using wordTrace_append hprefix tailTrace_930402
  have hstable : (prefixWord ++ tailWord_930402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930402).length < 2 ^ (prefixWord ++ tailWord_930402).sum := by decide
  have hdescent : baseEnd_930402 < baseStart_930402 := by decide
  rcases family_descends (prefixWord ++ tailWord_930402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930464 : List Nat := [2, 1, 1, 4, 4, 1, 3, 2, 3]
def baseStart_930464 : Nat := 118140960795 + 930464 * 2 ^ 59
def prefixEnd_930464 : Nat := 4983230072969 + 3 ^ 40 * 930464 * 2
def baseEnd_930464 : Nat := 212344561646734572898169

theorem tailTrace_930464 : CollatzResearch.WordTrace tailWord_930464 prefixEnd_930464 212344561646734572898169 := by
  unfold tailWord_930464
  simp only [CollatzResearch.WordTrace]
  refine ⟨16968405050547656722395223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22624540067396875629860297 16968405050547656722395223)
  ·
    refine ⟨25452607575821485083592835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16968405050547656722395223 25452607575821485083592835)
    ·
      refine ⟨38178911363732227625389253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25452607575821485083592835 38178911363732227625389253)
      ·
        refine ⟨7158545880699792679760485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38178911363732227625389253 7158545880699792679760485)
        ·
          refine ⟨1342227352631211127455091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7158545880699792679760485 1342227352631211127455091)
          ·
            refine ⟨2013341028946816691182637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1342227352631211127455091 2013341028946816691182637)
            ·
              refine ⟨755002885855056259193489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2013341028946816691182637 755002885855056259193489)
              ·
                refine ⟨566252164391292194395117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 755002885855056259193489 566252164391292194395117)
                ·
                  refine ⟨212344561646734572898169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 566252164391292194395117 212344561646734572898169)
                  ·
                    rfl

theorem cell21_930464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 3].length) (baseStart_930464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930464 prefixEnd_930464 := by exact prefixLift 930464
  have htrace : WordTrace (prefixWord ++ tailWord_930464) baseStart_930464 baseEnd_930464 := by
    simpa [prefixWord, tailWord_930464, baseEnd_930464] using wordTrace_append hprefix tailTrace_930464
  have hstable : (prefixWord ++ tailWord_930464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930464).length < 2 ^ (prefixWord ++ tailWord_930464).sum := by decide
  have hdescent : baseEnd_930464 < baseStart_930464 := by decide
  rcases family_descends (prefixWord ++ tailWord_930464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930478 : List Nat := [4, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_930478 : Nat := 118140960795 + 930478 * 2 ^ 59
def prefixEnd_930478 : Nat := 4983230072969 + 3 ^ 40 * 930478 * 2
def baseEnd_930478 : Nat := 212347756637473659664807

theorem tailTrace_930478 : CollatzResearch.WordTrace tailWord_930478 prefixEnd_930478 212347756637473659664807 := by
  unfold tailWord_930478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4242165090380574229475011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22624880482029729223866725 4242165090380574229475011)
  ·
    refine ⟨6363247635570861344212517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4242165090380574229475011 6363247635570861344212517)
    ·
      refine ⟨1193108931669536502039847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6363247635570861344212517 1193108931669536502039847)
      ·
        refine ⟨1789663397504304753059771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1193108931669536502039847 1789663397504304753059771)
        ·
          refine ⟨2684495096256457129589657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1789663397504304753059771 2684495096256457129589657)
          ·
            refine ⟨2013371322192342847192243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2684495096256457129589657 2013371322192342847192243)
            ·
              refine ⟨3020056983288514270788365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2013371322192342847192243 3020056983288514270788365)
              ·
                refine ⟨1132521368733192851545637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3020056983288514270788365 1132521368733192851545637)
                ·
                  refine ⟨212347756637473659664807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1132521368733192851545637 212347756637473659664807)
                  ·
                    rfl

theorem cell21_930478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_930478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930478 prefixEnd_930478 := by exact prefixLift 930478
  have htrace : WordTrace (prefixWord ++ tailWord_930478) baseStart_930478 baseEnd_930478 := by
    simpa [prefixWord, tailWord_930478, baseEnd_930478] using wordTrace_append hprefix tailTrace_930478
  have hstable : (prefixWord ++ tailWord_930478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930478).length < 2 ^ (prefixWord ++ tailWord_930478).sum := by decide
  have hdescent : baseEnd_930478 < baseStart_930478 := by decide
  rcases family_descends (prefixWord ++ tailWord_930478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930503 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 6]
def baseStart_930503 : Nat := 118140960795 + 930503 * 2 ^ 59
def prefixEnd_930503 : Nat := 4983230072969 + 3 ^ 40 * 930503 * 2
def baseEnd_930503 : Nat := 212353461978079171748089

theorem tailTrace_930503 : CollatzResearch.WordTrace tailWord_930503 prefixEnd_930503 212353461978079171748089 := by
  unfold tailWord_930503
  simp only [CollatzResearch.WordTrace]
  refine ⟨33938232547954023105460163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22625488365302682070306775 33938232547954023105460163)
  ·
    refine ⟨50907348821931034658190245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33938232547954023105460163 50907348821931034658190245)
    ·
      refine ⟨9545127904112068998410671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50907348821931034658190245 9545127904112068998410671)
      ·
        refine ⟨14317691856168103497616007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9545127904112068998410671 14317691856168103497616007)
        ·
          refine ⟨21476537784252155246424011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14317691856168103497616007 21476537784252155246424011)
          ·
            refine ⟨32214806676378232869636017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21476537784252155246424011 32214806676378232869636017)
            ·
              refine ⟨24161105007283674652227013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32214806676378232869636017 24161105007283674652227013)
              ·
                refine ⟨4530207188865688997292565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24161105007283674652227013 4530207188865688997292565)
                ·
                  refine ⟨212353461978079171748089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4530207188865688997292565 212353461978079171748089)
                  ·
                    rfl

theorem cell21_930503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 6].length) (baseStart_930503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930503 prefixEnd_930503 := by exact prefixLift 930503
  have htrace : WordTrace (prefixWord ++ tailWord_930503) baseStart_930503 baseEnd_930503 := by
    simpa [prefixWord, tailWord_930503, baseEnd_930503] using wordTrace_append hprefix tailTrace_930503
  have hstable : (prefixWord ++ tailWord_930503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930503).length < 2 ^ (prefixWord ++ tailWord_930503).sum := by decide
  have hdescent : baseEnd_930503 < baseStart_930503 := by decide
  rcases family_descends (prefixWord ++ tailWord_930503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930520 : List Nat := [2, 1, 2, 2, 3, 2, 1, 4, 4]
def baseStart_930520 : Nat := 118140960795 + 930520 * 2 ^ 59
def prefixEnd_930520 : Nat := 4983230072969 + 3 ^ 40 * 930520 * 2
def baseEnd_930520 : Nat := 212357341609690919964721

theorem tailTrace_930520 : CollatzResearch.WordTrace tailWord_930520 prefixEnd_930520 212357341609690919964721 := by
  unfold tailWord_930520
  simp only [CollatzResearch.WordTrace]
  refine ⟨16969426294446217504414507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22625901725928290005886009 16969426294446217504414507)
  ·
    refine ⟨25454139441669326256621761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16969426294446217504414507 25454139441669326256621761)
    ·
      refine ⟨19090604581251994692466321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25454139441669326256621761 19090604581251994692466321)
      ·
        refine ⟨14317953435938996019349741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19090604581251994692466321 14317953435938996019349741)
        ·
          refine ⟨5369232538477123507256153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14317953435938996019349741 5369232538477123507256153)
          ·
            refine ⟨4026924403857842630442115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5369232538477123507256153 4026924403857842630442115)
            ·
              refine ⟨6040386605786763945663173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4026924403857842630442115 6040386605786763945663173)
              ·
                refine ⟨1132572488585018239811845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6040386605786763945663173 1132572488585018239811845)
                ·
                  refine ⟨212357341609690919964721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1132572488585018239811845 212357341609690919964721)
                  ·
                    rfl

theorem cell21_930520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_930520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930520 prefixEnd_930520 := by exact prefixLift 930520
  have htrace : WordTrace (prefixWord ++ tailWord_930520) baseStart_930520 baseEnd_930520 := by
    simpa [prefixWord, tailWord_930520, baseEnd_930520] using wordTrace_append hprefix tailTrace_930520
  have hstable : (prefixWord ++ tailWord_930520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930520).length < 2 ^ (prefixWord ++ tailWord_930520).sum := by decide
  have hdescent : baseEnd_930520 < baseStart_930520 := by decide
  rcases family_descends (prefixWord ++ tailWord_930520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930579 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 6]
def baseStart_930579 : Nat := 118140960795 + 930579 * 2 ^ 59
def prefixEnd_930579 : Nat := 4983230072969 + 3 ^ 40 * 930579 * 2
def baseEnd_930579 : Nat := 212370806213519928481267

theorem tailTrace_930579 : CollatzResearch.WordTrace tailWord_930579 prefixEnd_930579 212370806213519928481267 := by
  unfold tailWord_930579
  simp only [CollatzResearch.WordTrace]
  refine ⟨33941004495678688085226791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22627336330452458723484527 33941004495678688085226791)
  ·
    refine ⟨50911506743518032127840187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33941004495678688085226791 50911506743518032127840187)
    ·
      refine ⟨76367260115277048191760281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50911506743518032127840187 76367260115277048191760281)
      ·
        refine ⟨57275445086457786143820211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76367260115277048191760281 57275445086457786143820211)
        ·
          refine ⟨85913167629686679215730317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57275445086457786143820211 85913167629686679215730317)
          ·
            refine ⟨32217437861132504705898869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85913167629686679215730317 32217437861132504705898869)
            ·
              refine ⟨3020384799481172316178019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32217437861132504705898869 3020384799481172316178019)
              ·
                refine ⟨4530577199221758474267029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3020384799481172316178019 4530577199221758474267029)
                ·
                  refine ⟨212370806213519928481267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4530577199221758474267029 212370806213519928481267)
                  ·
                    rfl

theorem cell21_930579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 6].length) (baseStart_930579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930579 prefixEnd_930579 := by exact prefixLift 930579
  have htrace : WordTrace (prefixWord ++ tailWord_930579) baseStart_930579 baseEnd_930579 := by
    simpa [prefixWord, tailWord_930579, baseEnd_930579] using wordTrace_append hprefix tailTrace_930579
  have hstable : (prefixWord ++ tailWord_930579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930579).length < 2 ^ (prefixWord ++ tailWord_930579).sum := by decide
  have hdescent : baseEnd_930579 < baseStart_930579 := by decide
  rcases family_descends (prefixWord ++ tailWord_930579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930602 : List Nat := [3, 1, 4, 3, 2, 1, 2, 5]
def baseStart_930602 : Nat := 118140960795 + 930602 * 2 ^ 59
def prefixEnd_930602 : Nat := 4983230072969 + 3 ^ 40 * 930602 * 2
def baseEnd_930602 : Nat := 70792018375625666532629

theorem tailTrace_930602 : CollatzResearch.WordTrace tailWord_930602 prefixEnd_930602 70792018375625666532629 := by
  unfold tailWord_930602
  simp only [CollatzResearch.WordTrace]
  refine ⟨8485460843648840753328515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22627895583063575342209373 8485460843648840753328515)
  ·
    refine ⟨12728191265473261129992773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8485460843648840753328515 12728191265473261129992773)
    ·
      refine ⟨2386535862276236461873645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12728191265473261129992773 2386535862276236461873645)
      ·
        refine ⟨894950948353588673202617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2386535862276236461873645 894950948353588673202617)
        ·
          refine ⟨671213211265191504901963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 894950948353588673202617 671213211265191504901963)
          ·
            refine ⟨1006819816897787257352945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671213211265191504901963 1006819816897787257352945)
            ·
              refine ⟨755114862673340443014709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1006819816897787257352945 755114862673340443014709)
              ·
                refine ⟨70792018375625666532629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 755114862673340443014709 70792018375625666532629)
                ·
                  rfl

theorem cell21_930602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_930602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930602 prefixEnd_930602 := by exact prefixLift 930602
  have htrace : WordTrace (prefixWord ++ tailWord_930602) baseStart_930602 baseEnd_930602 := by
    simpa [prefixWord, tailWord_930602, baseEnd_930602] using wordTrace_append hprefix tailTrace_930602
  have hstable : (prefixWord ++ tailWord_930602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930602).length < 2 ^ (prefixWord ++ tailWord_930602).sum := by decide
  have hdescent : baseEnd_930602 < baseStart_930602 := by decide
  rcases family_descends (prefixWord ++ tailWord_930602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930610 : List Nat := [3, 2, 1, 1, 3, 1, 3, 7]
def baseStart_930610 : Nat := 118140960795 + 930610 * 2 ^ 59
def prefixEnd_930610 : Nat := 4983230072969 + 3 ^ 40 * 930610 * 2
def baseEnd_930610 : Nat := 70792626945290254488179

theorem tailTrace_930610 : CollatzResearch.WordTrace tailWord_930610 prefixEnd_930610 70792626945290254488179 := by
  unfold tailWord_930610
  simp only [CollatzResearch.WordTrace]
  refine ⟨8485533789641595094901321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22628090105710920253070189 8485533789641595094901321)
  ·
    refine ⟨6364150342231196321175991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8485533789641595094901321 6364150342231196321175991)
    ·
      refine ⟨9546225513346794481763987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6364150342231196321175991 9546225513346794481763987)
      ·
        refine ⟨14319338270020191722645981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9546225513346794481763987 14319338270020191722645981)
        ·
          refine ⟨5369751851257571895992243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14319338270020191722645981 5369751851257571895992243)
          ·
            refine ⟨8054627776886357843988365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5369751851257571895992243 8054627776886357843988365)
            ·
              refine ⟨3020485416332384191495637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8054627776886357843988365 3020485416332384191495637)
              ·
                refine ⟨70792626945290254488179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3020485416332384191495637 70792626945290254488179)
                ·
                  rfl

theorem cell21_930610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_930610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930610 prefixEnd_930610 := by exact prefixLift 930610
  have htrace : WordTrace (prefixWord ++ tailWord_930610) baseStart_930610 baseEnd_930610 := by
    simpa [prefixWord, tailWord_930610, baseEnd_930610] using wordTrace_append hprefix tailTrace_930610
  have hstable : (prefixWord ++ tailWord_930610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930610).length < 2 ^ (prefixWord ++ tailWord_930610).sum := by decide
  have hdescent : baseEnd_930610 < baseStart_930610 := by decide
  rcases family_descends (prefixWord ++ tailWord_930610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930624 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 7]
def baseStart_930624 : Nat := 118140960795 + 930624 * 2 ^ 59
def prefixEnd_930624 : Nat := 4983230072969 + 3 ^ 40 * 930624 * 2
def baseEnd_930624 : Nat := 212381075826609850231175

theorem tailTrace_930624 : CollatzResearch.WordTrace tailWord_930624 prefixEnd_930624 212381075826609850231175 := by
  unfold tailWord_930624
  simp only [CollatzResearch.WordTrace]
  refine ⟨16971322890257830385307463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22628430520343773847076617 16971322890257830385307463)
  ·
    refine ⟨25456984335386745577961195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16971322890257830385307463 25456984335386745577961195)
    ·
      refine ⟨38185476503080118366941793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25456984335386745577961195 38185476503080118366941793)
      ·
        refine ⟨28639107377310088775206345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38185476503080118366941793 28639107377310088775206345)
        ·
          refine ⟨21479330532982566581404759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28639107377310088775206345 21479330532982566581404759)
          ·
            refine ⟨32218995799473849872107139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21479330532982566581404759 32218995799473849872107139)
            ·
              refine ⟨48328493699210774808160709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32218995799473849872107139 48328493699210774808160709)
              ·
                refine ⟨9061592568602020276530133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48328493699210774808160709 9061592568602020276530133)
                ·
                  refine ⟨212381075826609850231175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9061592568602020276530133 212381075826609850231175)
                  ·
                    rfl

theorem cell21_930624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_930624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930624 prefixEnd_930624 := by exact prefixLift 930624
  have htrace : WordTrace (prefixWord ++ tailWord_930624) baseStart_930624 baseEnd_930624 := by
    simpa [prefixWord, tailWord_930624, baseEnd_930624] using wordTrace_append hprefix tailTrace_930624
  have hstable : (prefixWord ++ tailWord_930624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930624).length < 2 ^ (prefixWord ++ tailWord_930624).sum := by decide
  have hdescent : baseEnd_930624 < baseStart_930624 := by decide
  rcases family_descends (prefixWord ++ tailWord_930624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930717 : List Nat := [1, 4, 2, 1, 2, 1, 3, 2, 5]
def baseStart_930717 : Nat := 118140960795 + 930717 * 2 ^ 59
def prefixEnd_930717 : Nat := 4983230072969 + 3 ^ 40 * 930717 * 2
def baseEnd_930717 : Nat := 212402299693662355180985

theorem tailTrace_930717 : CollatzResearch.WordTrace tailWord_930717 prefixEnd_930717 212402299693662355180985 := by
  unfold tailWord_930717
  simp only [CollatzResearch.WordTrace]
  refine ⟨33946037769178737653750405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22630691846119158435833603 33946037769178737653750405)
  ·
    refine ⟨6364882081721013310078201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33946037769178737653750405 6364882081721013310078201)
    ·
      refine ⟨4773661561290759982558651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6364882081721013310078201 4773661561290759982558651)
      ·
        refine ⟨7160492341936139973837977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4773661561290759982558651 7160492341936139973837977)
        ·
          refine ⟨5370369256452104980378483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7160492341936139973837977 5370369256452104980378483)
          ·
            refine ⟨8055553884678157470567725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5370369256452104980378483 8055553884678157470567725)
            ·
              refine ⟨3020832706754309051462897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8055553884678157470567725 3020832706754309051462897)
              ·
                refine ⟨2265624530065731788597173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3020832706754309051462897 2265624530065731788597173)
                ·
                  refine ⟨212402299693662355180985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2265624530065731788597173 212402299693662355180985)
                  ·
                    rfl

theorem cell21_930717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_930717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930717 prefixEnd_930717 := by exact prefixLift 930717
  have htrace : WordTrace (prefixWord ++ tailWord_930717) baseStart_930717 baseEnd_930717 := by
    simpa [prefixWord, tailWord_930717, baseEnd_930717] using wordTrace_append hprefix tailTrace_930717
  have hstable : (prefixWord ++ tailWord_930717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930717).length < 2 ^ (prefixWord ++ tailWord_930717).sum := by decide
  have hdescent : baseEnd_930717 < baseStart_930717 := by decide
  rcases family_descends (prefixWord ++ tailWord_930717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930824 : List Nat := [2, 1, 3, 2, 1, 4, 1, 3, 4]
def baseStart_930824 : Nat := 118140960795 + 930824 * 2 ^ 59
def prefixEnd_930824 : Nat := 4983230072969 + 3 ^ 40 * 930824 * 2
def baseEnd_930824 : Nat := 212426718551453946897433

theorem tailTrace_930824 : CollatzResearch.WordTrace tailWord_930824 prefixEnd_930824 212426718551453946897433 := by
  unfold tailWord_930824
  simp only [CollatzResearch.WordTrace]
  refine ⟨16974970189895547463947763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22633293586527396618597017 16974970189895547463947763)
  ·
    refine ⟨25462455284843321195921645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16974970189895547463947763 25462455284843321195921645)
    ·
      refine ⟨9548420731816245448470617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25462455284843321195921645 9548420731816245448470617)
      ·
        refine ⟨7161315548862184086352963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9548420731816245448470617 7161315548862184086352963)
        ·
          refine ⟨10741973323293276129529445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7161315548862184086352963 10741973323293276129529445)
          ·
            refine ⟨2014119998117489274286771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10741973323293276129529445 2014119998117489274286771)
            ·
              refine ⟨3021179997176233911430157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2014119998117489274286771 3021179997176233911430157)
              ·
                refine ⟨1132942498941087716786309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3021179997176233911430157 1132942498941087716786309)
                ·
                  refine ⟨212426718551453946897433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1132942498941087716786309 212426718551453946897433)
                  ·
                    rfl

theorem cell21_930824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_930824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930824 prefixEnd_930824 := by exact prefixLift 930824
  have htrace : WordTrace (prefixWord ++ tailWord_930824) baseStart_930824 baseEnd_930824 := by
    simpa [prefixWord, tailWord_930824, baseEnd_930824] using wordTrace_append hprefix tailTrace_930824
  have hstable : (prefixWord ++ tailWord_930824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930824).length < 2 ^ (prefixWord ++ tailWord_930824).sum := by decide
  have hdescent : baseEnd_930824 < baseStart_930824 := by decide
  rcases family_descends (prefixWord ++ tailWord_930824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930883 : List Nat := [1, 1, 1, 3, 1, 2, 3, 5, 4]
def baseStart_930883 : Nat := 118140960795 + 930883 * 2 ^ 59
def prefixEnd_930883 : Nat := 4983230072969 + 3 ^ 40 * 930883 * 2
def baseEnd_930883 : Nat := 212440183155282955413979

theorem tailTrace_930883 : CollatzResearch.WordTrace tailWord_930883 prefixEnd_930883 212440183155282955413979 := by
  unfold tailWord_930883
  simp only [CollatzResearch.WordTrace]
  refine ⟨33952092286577348004293303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22634728191051565336195535 33952092286577348004293303)
  ·
    refine ⟨50928138429866022006439955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33952092286577348004293303 50928138429866022006439955)
    ·
      refine ⟨76392207644799033009659933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50928138429866022006439955 76392207644799033009659933)
      ·
        refine ⟨28647077866799637378622475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76392207644799033009659933 28647077866799637378622475)
        ·
          refine ⟨42970616800199456067933713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28647077866799637378622475 42970616800199456067933713)
          ·
            refine ⟨32227962600149592050950285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42970616800199456067933713 32227962600149592050950285)
            ·
              refine ⟨12085485975056097019106357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32227962600149592050950285 12085485975056097019106357)
              ·
                refine ⟨1133014310161509095541221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12085485975056097019106357 1133014310161509095541221)
                ·
                  refine ⟨212440183155282955413979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1133014310161509095541221 212440183155282955413979)
                  ·
                    rfl

theorem cell21_930883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 4].length) (baseStart_930883 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930883 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930883 prefixEnd_930883 := by exact prefixLift 930883
  have htrace : WordTrace (prefixWord ++ tailWord_930883) baseStart_930883 baseEnd_930883 := by
    simpa [prefixWord, tailWord_930883, baseEnd_930883] using wordTrace_append hprefix tailTrace_930883
  have hstable : (prefixWord ++ tailWord_930883).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930883).length < 2 ^ (prefixWord ++ tailWord_930883).sum := by decide
  have hdescent : baseEnd_930883 < baseStart_930883 := by decide
  rcases family_descends (prefixWord ++ tailWord_930883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930886 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_930886 : Nat := 118140960795 + 930886 * 2 ^ 59
def prefixEnd_930886 : Nat := 4983230072969 + 3 ^ 40 * 930886 * 2
def baseEnd_930886 : Nat := 212440867796155616863973

theorem tailTrace_930886 : CollatzResearch.WordTrace tailWord_930886 prefixEnd_930886 212440867796155616863973 := by
  unfold tailWord_930886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1061006303298952484895391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22634801137044319677768341 1061006303298952484895391)
  ·
    refine ⟨1591509454948428727343087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1061006303298952484895391 1591509454948428727343087)
    ·
      refine ⟨2387264182422643091014631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1591509454948428727343087 2387264182422643091014631)
      ·
        refine ⟨3580896273633964636521947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2387264182422643091014631 3580896273633964636521947)
        ·
          refine ⟨5371344410450946954782921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3580896273633964636521947 5371344410450946954782921)
          ·
            refine ⟨4028508307838210216087191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5371344410450946954782921 4028508307838210216087191)
            ·
              refine ⟨6042762461757315324130787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4028508307838210216087191 6042762461757315324130787)
              ·
                refine ⟨9064143692635972986196181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6042762461757315324130787 9064143692635972986196181)
                ·
                  refine ⟨212440867796155616863973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9064143692635972986196181 212440867796155616863973)
                  ·
                    rfl

theorem cell21_930886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_930886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930886 prefixEnd_930886 := by exact prefixLift 930886
  have htrace : WordTrace (prefixWord ++ tailWord_930886) baseStart_930886 baseEnd_930886 := by
    simpa [prefixWord, tailWord_930886, baseEnd_930886] using wordTrace_append hprefix tailTrace_930886
  have hstable : (prefixWord ++ tailWord_930886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930886).length < 2 ^ (prefixWord ++ tailWord_930886).sum := by decide
  have hdescent : baseEnd_930886 < baseStart_930886 := by decide
  rcases family_descends (prefixWord ++ tailWord_930886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930897 : List Nat := [1, 2, 2, 1, 3, 1, 2, 9]
def baseStart_930897 : Nat := 118140960795 + 930897 * 2 ^ 59
def prefixEnd_930897 : Nat := 4983230072969 + 3 ^ 40 * 930897 * 2
def baseEnd_930897 : Nat := 70814459382007347393539

theorem tailTrace_930897 : CollatzResearch.WordTrace tailWord_930897 prefixEnd_930897 70814459382007347393539 := by
  unfold tailWord_930897
  simp only [CollatzResearch.WordTrace]
  refine ⟨33952602908526628395302945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22635068605684418930201963 33952602908526628395302945)
  ·
    refine ⟨25464452181394971296477209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33952602908526628395302945 25464452181394971296477209)
    ·
      refine ⟨19098339136046228472357907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25464452181394971296477209 19098339136046228472357907)
      ·
        refine ⟨28647508704069342708536861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19098339136046228472357907 28647508704069342708536861)
        ·
          refine ⟨10742815764026003515701323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28647508704069342708536861 10742815764026003515701323)
          ·
            refine ⟨16114223646039005273551985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10742815764026003515701323 16114223646039005273551985)
            ·
              refine ⟨12085667734529253955163989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16114223646039005273551985 12085667734529253955163989)
              ·
                refine ⟨70814459382007347393539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12085667734529253955163989 70814459382007347393539)
                ·
                  rfl

theorem cell21_930897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 9].length) (baseStart_930897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930897 prefixEnd_930897 := by exact prefixLift 930897
  have htrace : WordTrace (prefixWord ++ tailWord_930897) baseStart_930897 baseEnd_930897 := by
    simpa [prefixWord, tailWord_930897, baseEnd_930897] using wordTrace_append hprefix tailTrace_930897
  have hstable : (prefixWord ++ tailWord_930897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930897).length < 2 ^ (prefixWord ++ tailWord_930897).sum := by decide
  have hdescent : baseEnd_930897 < baseStart_930897 := by decide
  rcases family_descends (prefixWord ++ tailWord_930897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930945 : List Nat := [1, 2, 4, 2, 2, 1, 2, 2, 5]
def baseStart_930945 : Nat := 118140960795 + 930945 * 2 ^ 59
def prefixEnd_930945 : Nat := 4983230072969 + 3 ^ 40 * 930945 * 2
def baseEnd_930945 : Nat := 212454332399984625380519

theorem tailTrace_930945 : CollatzResearch.WordTrace tailWord_930945 prefixEnd_930945 212454332399984625380519 := by
  unfold tailWord_930945
  simp only [CollatzResearch.WordTrace]
  refine ⟨33954353612352732593050289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22636235741568488395366859 33954353612352732593050289)
  ·
    refine ⟨25465765209264549444787717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33954353612352732593050289 25465765209264549444787717)
    ·
      refine ⟨4774830976737103020897697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25465765209264549444787717 4774830976737103020897697)
      ·
        refine ⟨3581123232552827265673273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4774830976737103020897697 3581123232552827265673273)
        ·
          refine ⟨2685842424414620449254955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3581123232552827265673273 2685842424414620449254955)
          ·
            refine ⟨4028763636621930673882433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2685842424414620449254955 4028763636621930673882433)
            ·
              refine ⟨3021572727466448005411825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4028763636621930673882433 3021572727466448005411825)
              ·
                refine ⟨2266179545599836004058869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3021572727466448005411825 2266179545599836004058869)
                ·
                  refine ⟨212454332399984625380519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2266179545599836004058869 212454332399984625380519)
                  ·
                    rfl

theorem cell21_930945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_930945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930945 prefixEnd_930945 := by exact prefixLift 930945
  have htrace : WordTrace (prefixWord ++ tailWord_930945) baseStart_930945 baseEnd_930945 := by
    simpa [prefixWord, tailWord_930945, baseEnd_930945] using wordTrace_append hprefix tailTrace_930945
  have hstable : (prefixWord ++ tailWord_930945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930945).length < 2 ^ (prefixWord ++ tailWord_930945).sum := by decide
  have hdescent : baseEnd_930945 < baseStart_930945 := by decide
  rcases family_descends (prefixWord ++ tailWord_930945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930993 : List Nat := [1, 2, 2, 5, 1, 1, 4, 1, 4]
def baseStart_930993 : Nat := 118140960795 + 930993 * 2 ^ 59
def prefixEnd_930993 : Nat := 4983230072969 + 3 ^ 40 * 930993 * 2
def baseEnd_930993 : Nat := 212465286653947208580421

theorem tailTrace_930993 : CollatzResearch.WordTrace tailWord_930993 prefixEnd_930993 212465286653947208580421 := by
  unfold tailWord_930993
  simp only [CollatzResearch.WordTrace]
  refine ⟨33956104316178836790797633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22637402877452557860531755 33956104316178836790797633)
  ·
    refine ⟨25467078237134127593098225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33956104316178836790797633 25467078237134127593098225)
    ·
      refine ⟨19100308677850595694823669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25467078237134127593098225 19100308677850595694823669)
      ·
        refine ⟨1790653938548493346389719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19100308677850595694823669 1790653938548493346389719)
        ·
          refine ⟨2685980907822740019584579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1790653938548493346389719 2685980907822740019584579)
          ·
            refine ⟨4028971361734110029376869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2685980907822740019584579 4028971361734110029376869)
            ·
              refine ⟨755432130325145630508163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4028971361734110029376869 755432130325145630508163)
              ·
                refine ⟨1133148195487718445762245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755432130325145630508163 1133148195487718445762245)
                ·
                  refine ⟨212465286653947208580421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1133148195487718445762245 212465286653947208580421)
                  ·
                    rfl

theorem cell21_930993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 4].length) (baseStart_930993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_930993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_930993 prefixEnd_930993 := by exact prefixLift 930993
  have htrace : WordTrace (prefixWord ++ tailWord_930993) baseStart_930993 baseEnd_930993 := by
    simpa [prefixWord, tailWord_930993, baseEnd_930993] using wordTrace_append hprefix tailTrace_930993
  have hstable : (prefixWord ++ tailWord_930993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930993).length < 2 ^ (prefixWord ++ tailWord_930993).sum := by decide
  have hdescent : baseEnd_930993 < baseStart_930993 := by decide
  rcases family_descends (prefixWord ++ tailWord_930993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931030 : List Nat := [5, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_931030 : Nat := 118140960795 + 931030 * 2 ^ 59
def prefixEnd_931030 : Nat := 4983230072969 + 3 ^ 40 * 931030 * 2
def baseEnd_931030 : Nat := 212473730558043366463679

theorem tailTrace_931030 : CollatzResearch.WordTrace tailWord_931030 prefixEnd_931030 212473730558043366463679 := by
  unfold tailWord_931030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2122340863565299506868409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22638302544696528073263029 2122340863565299506868409)
  ·
    refine ⟨1591755647673974630151307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2122340863565299506868409 1591755647673974630151307)
    ·
      refine ⟨2387633471510961945226961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1591755647673974630151307 2387633471510961945226961)
      ·
        refine ⟨1790725103633221458920221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2387633471510961945226961 1790725103633221458920221)
        ·
          refine ⟨671521913862458047095083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1790725103633221458920221 671521913862458047095083)
          ·
            refine ⟨1007282870793687070642625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671521913862458047095083 1007282870793687070642625)
            ·
              refine ⟨755462153095265302981969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1007282870793687070642625 755462153095265302981969)
              ·
                refine ⟨566596614821448977236477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 755462153095265302981969 566596614821448977236477)
                ·
                  refine ⟨212473730558043366463679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 566596614821448977236477 212473730558043366463679)
                  ·
                    rfl

theorem cell21_931030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_931030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_931030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_931030 prefixEnd_931030 := by exact prefixLift 931030
  have htrace : WordTrace (prefixWord ++ tailWord_931030) baseStart_931030 baseEnd_931030 := by
    simpa [prefixWord, tailWord_931030, baseEnd_931030] using wordTrace_append hprefix tailTrace_931030
  have hstable : (prefixWord ++ tailWord_931030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931030).length < 2 ^ (prefixWord ++ tailWord_931030).sum := by decide
  have hdescent : baseEnd_931030 < baseStart_931030 := by decide
  rcases family_descends (prefixWord ++ tailWord_931030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931066 : List Nat := [3, 1, 1, 1, 1, 4, 5, 5]
def baseStart_931066 : Nat := 118140960795 + 931066 * 2 ^ 59
def prefixEnd_931066 : Nat := 4983230072969 + 3 ^ 40 * 931066 * 2
def baseEnd_931066 : Nat := 70827315416171767954535

theorem tailTrace_931066 : CollatzResearch.WordTrace tailWord_931066 prefixEnd_931066 70827315416171767954535 := by
  unfold tailWord_931066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8489691711228592564551263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22639177896609580172136701 8489691711228592564551263)
  ·
    refine ⟨12734537566842888846826895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8489691711228592564551263 12734537566842888846826895)
    ·
      refine ⟨19101806350264333270240343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12734537566842888846826895 19101806350264333270240343)
      ·
        refine ⟨28652709525396499905360515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19101806350264333270240343 28652709525396499905360515)
        ·
          refine ⟨42979064288094749858040773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28652709525396499905360515 42979064288094749858040773)
          ·
            refine ⟨8058574554017765598382645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42979064288094749858040773 8058574554017765598382645)
            ·
              refine ⟨755491364439165524848373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8058574554017765598382645 755491364439165524848373)
              ·
                refine ⟨70827315416171767954535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 755491364439165524848373 70827315416171767954535)
                ·
                  rfl

theorem cell21_931066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_931066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_931066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_931066 prefixEnd_931066 := by exact prefixLift 931066
  have htrace : WordTrace (prefixWord ++ tailWord_931066) baseStart_931066 baseEnd_931066 := by
    simpa [prefixWord, tailWord_931066, baseEnd_931066] using wordTrace_append hprefix tailTrace_931066
  have hstable : (prefixWord ++ tailWord_931066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931066).length < 2 ^ (prefixWord ++ tailWord_931066).sum := by decide
  have hdescent : baseEnd_931066 < baseStart_931066 := by decide
  rcases family_descends (prefixWord ++ tailWord_931066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931201 : List Nat := [1, 2, 4, 3, 11]
def baseStart_931201 : Nat := 118140960795 + 931201 * 2 ^ 59
def prefixEnd_931201 : Nat := 4983230072969 + 3 ^ 40 * 931201 * 2
def baseEnd_931201 : Nat := 2623614260343025544609

theorem tailTrace_931201 : CollatzResearch.WordTrace tailWord_931201 prefixEnd_931201 2623614260343025544609 := by
  unfold tailWord_931201
  simp only [CollatzResearch.WordTrace]
  refine ⟨33963690699425288314369457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22642460466283525542912971 33963690699425288314369457)
  ·
    refine ⟨25472768024568966235777093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33963690699425288314369457 25472768024568966235777093)
    ·
      refine ⟨4776144004606681169208205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25472768024568966235777093 4776144004606681169208205)
      ·
        refine ⟨1791054001727505438453077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4776144004606681169208205 1791054001727505438453077)
        ·
          refine ⟨2623614260343025544609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1791054001727505438453077 2623614260343025544609)
          ·
            rfl

theorem cell21_931201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 11].length) (baseStart_931201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_931201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_931201 prefixEnd_931201 := by exact prefixLift 931201
  have htrace : WordTrace (prefixWord ++ tailWord_931201) baseStart_931201 baseEnd_931201 := by
    simpa [prefixWord, tailWord_931201, baseEnd_931201] using wordTrace_append hprefix tailTrace_931201
  have hstable : (prefixWord ++ tailWord_931201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931201).length < 2 ^ (prefixWord ++ tailWord_931201).sum := by decide
  have hdescent : baseEnd_931201 < baseStart_931201 := by decide
  rcases family_descends (prefixWord ++ tailWord_931201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931204 : List Nat := [2, 3, 2, 1, 1, 4, 2, 2, 4]
def baseStart_931204 : Nat := 118140960795 + 931204 * 2 ^ 59
def prefixEnd_931204 : Nat := 4983230072969 + 3 ^ 40 * 931204 * 2
def baseEnd_931204 : Nat := 212513439728657730563323

theorem tailTrace_931204 : CollatzResearch.WordTrace tailWord_931204 prefixEnd_931204 212513439728657730563323 := by
  unfold tailWord_931204
  simp only [CollatzResearch.WordTrace]
  refine ⟨16981900059207209913364333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22642533412276279884485777 16981900059207209913364333)
  ·
    refine ⟨6368212522202703717511625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16981900059207209913364333 6368212522202703717511625)
    ·
      refine ⟨4776159391652027788133719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6368212522202703717511625 4776159391652027788133719)
      ·
        refine ⟨7164239087478041682200579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4776159391652027788133719 7164239087478041682200579)
        ·
          refine ⟨10746358631217062523300869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7164239087478041682200579 10746358631217062523300869)
          ·
            refine ⟨2014942243353199223118913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10746358631217062523300869 2014942243353199223118913)
            ·
              refine ⟨1511206682514899417339185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2014942243353199223118913 1511206682514899417339185)
              ·
                refine ⟨1133405011886174563004389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1511206682514899417339185 1133405011886174563004389)
                ·
                  refine ⟨212513439728657730563323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1133405011886174563004389 212513439728657730563323)
                  ·
                    rfl

theorem cell21_931204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_931204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_931204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_931204 prefixEnd_931204 := by exact prefixLift 931204
  have htrace : WordTrace (prefixWord ++ tailWord_931204) baseStart_931204 baseEnd_931204 := by
    simpa [prefixWord, tailWord_931204, baseEnd_931204] using wordTrace_append hprefix tailTrace_931204
  have hstable : (prefixWord ++ tailWord_931204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931204).length < 2 ^ (prefixWord ++ tailWord_931204).sum := by decide
  have hdescent : baseEnd_931204 < baseStart_931204 := by decide
  rcases family_descends (prefixWord ++ tailWord_931204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931207 : List Nat := [1, 1, 4, 2, 2, 4, 2, 2, 3]
def baseStart_931207 : Nat := 118140960795 + 931207 * 2 ^ 59
def prefixEnd_931207 : Nat := 4983230072969 + 3 ^ 40 * 931207 * 2
def baseEnd_931207 : Nat := 212514124369530392013317

theorem tailTrace_931207 : CollatzResearch.WordTrace tailWord_931207 prefixEnd_931207 212514124369530392013317 := by
  unfold tailWord_931207
  simp only [CollatzResearch.WordTrace]
  refine ⟨33963909537403551339087875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22642606358269034226058583 33963909537403551339087875)
  ·
    refine ⟨50945864306105327008631813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33963909537403551339087875 50945864306105327008631813)
    ·
      refine ⟨9552349557394748814118465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50945864306105327008631813 9552349557394748814118465)
      ·
        refine ⟨7164262168046061610588849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9552349557394748814118465 7164262168046061610588849)
        ·
          refine ⟨5373196626034546207941637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7164262168046061610588849 5373196626034546207941637)
          ·
            refine ⟨1007474367381477413989057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5373196626034546207941637 1007474367381477413989057)
            ·
              refine ⟨755605775536108060491793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1007474367381477413989057 755605775536108060491793)
              ·
                refine ⟨566704331652081045368845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 755605775536108060491793 566704331652081045368845)
                ·
                  refine ⟨212514124369530392013317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 566704331652081045368845 212514124369530392013317)
                  ·
                    rfl

theorem cell21_931207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 3].length) (baseStart_931207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_931207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_931207 prefixEnd_931207 := by exact prefixLift 931207
  have htrace : WordTrace (prefixWord ++ tailWord_931207) baseStart_931207 baseEnd_931207 := by
    simpa [prefixWord, tailWord_931207, baseEnd_931207] using wordTrace_append hprefix tailTrace_931207
  have hstable : (prefixWord ++ tailWord_931207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931207).length < 2 ^ (prefixWord ++ tailWord_931207).sum := by decide
  have hdescent : baseEnd_931207 < baseStart_931207 := by decide
  rcases family_descends (prefixWord ++ tailWord_931207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931232 : List Nat := [2, 1, 1, 4, 1, 2, 3, 2, 5]
def baseStart_931232 : Nat := 118140960795 + 931232 * 2 ^ 59
def prefixEnd_931232 : Nat := 4983230072969 + 3 ^ 40 * 931232 * 2
def baseEnd_931232 : Nat := 212519829710135904096599

theorem tailTrace_931232 : CollatzResearch.WordTrace tailWord_931232 prefixEnd_931232 212519829710135904096599 := by
  unfold tailWord_931232
  simp only [CollatzResearch.WordTrace]
  refine ⟨16982410681156490304373975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22643214241541987072498633 16982410681156490304373975)
  ·
    refine ⟨25473616021734735456560963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16982410681156490304373975 25473616021734735456560963)
    ·
      refine ⟨38210424032602103184841445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25473616021734735456560963 38210424032602103184841445)
      ·
        refine ⟨7164454506112894347157771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38210424032602103184841445 7164454506112894347157771)
        ·
          refine ⟨10746681759169341520736657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7164454506112894347157771 10746681759169341520736657)
          ·
            refine ⟨8060011319377006140552493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10746681759169341520736657 8060011319377006140552493)
            ·
              refine ⟨3022504244766377302707185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8060011319377006140552493 3022504244766377302707185)
              ·
                refine ⟨2266878183574782977030389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3022504244766377302707185 2266878183574782977030389)
                ·
                  refine ⟨212519829710135904096599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2266878183574782977030389 212519829710135904096599)
                  ·
                    rfl

theorem cell21_931232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_931232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_931232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_931232 prefixEnd_931232 := by exact prefixLift 931232
  have htrace : WordTrace (prefixWord ++ tailWord_931232) baseStart_931232 baseEnd_931232 := by
    simpa [prefixWord, tailWord_931232, baseEnd_931232] using wordTrace_append hprefix tailTrace_931232
  have hstable : (prefixWord ++ tailWord_931232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931232).length < 2 ^ (prefixWord ++ tailWord_931232).sum := by decide
  have hdescent : baseEnd_931232 < baseStart_931232 := by decide
  rcases family_descends (prefixWord ++ tailWord_931232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931322 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 6]
def baseStart_931322 : Nat := 118140960795 + 931322 * 2 ^ 59
def prefixEnd_931322 : Nat := 4983230072969 + 3 ^ 40 * 931322 * 2
def baseEnd_931322 : Nat := 212540368936315747596415

theorem tailTrace_931322 : CollatzResearch.WordTrace tailWord_931322 prefixEnd_931322 212540368936315747596415 := by
  unfold tailWord_931322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8492025982996731494881055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22645402621324617319682813 8492025982996731494881055)
  ·
    refine ⟨12738038974495097242321583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8492025982996731494881055 12738038974495097242321583)
    ·
      refine ⟨19107058461742645863482375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12738038974495097242321583 19107058461742645863482375)
      ·
        refine ⟨28660587692613968795223563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19107058461742645863482375 28660587692613968795223563)
        ·
          refine ⟨42990881538920953192835345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28660587692613968795223563 42990881538920953192835345)
          ·
            refine ⟨32243161154190714894626509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42990881538920953192835345 32243161154190714894626509)
            ·
              refine ⟨12091185432821518085484941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32243161154190714894626509 12091185432821518085484941)
              ·
                refine ⟨4534194537308069282056853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12091185432821518085484941 4534194537308069282056853)
                ·
                  refine ⟨212540368936315747596415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4534194537308069282056853 212540368936315747596415)
                  ·
                    rfl

theorem cell21_931322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_931322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_931322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_931322 prefixEnd_931322 := by exact prefixLift 931322
  have htrace : WordTrace (prefixWord ++ tailWord_931322) baseStart_931322 baseEnd_931322 := by
    simpa [prefixWord, tailWord_931322, baseEnd_931322] using wordTrace_append hprefix tailTrace_931322
  have hstable : (prefixWord ++ tailWord_931322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931322).length < 2 ^ (prefixWord ++ tailWord_931322).sum := by decide
  have hdescent : baseEnd_931322 < baseStart_931322 := by decide
  rcases family_descends (prefixWord ++ tailWord_931322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931325 : List Nat := [1, 4, 1, 1, 1, 6, 1, 1, 5]
def baseStart_931325 : Nat := 118140960795 + 931325 * 2 ^ 59
def prefixEnd_931325 : Nat := 4983230072969 + 3 ^ 40 * 931325 * 2
def baseEnd_931325 : Nat := 212541053577188409046409

theorem tailTrace_931325 : CollatzResearch.WordTrace tailWord_931325 prefixEnd_931325 212541053577188409046409 := by
  unfold tailWord_931325
  simp only [CollatzResearch.WordTrace]
  refine ⟨33968213350976057491883429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22645475567317371661255619 33968213350976057491883429)
  ·
    refine ⟨6369040003308010779728143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33968213350976057491883429 6369040003308010779728143)
    ·
      refine ⟨9553560004962016169592215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6369040003308010779728143 9553560004962016169592215)
      ·
        refine ⟨14330340007443024254388323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9553560004962016169592215 14330340007443024254388323)
        ·
          refine ⟨21495510011164536381582485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14330340007443024254388323 21495510011164536381582485)
          ·
            refine ⟨1007602031773337642886679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21495510011164536381582485 1007602031773337642886679)
            ·
              refine ⟨1511403047660006464330019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1007602031773337642886679 1511403047660006464330019)
              ·
                refine ⟨2267104571490009696495029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511403047660006464330019 2267104571490009696495029)
                ·
                  refine ⟨212541053577188409046409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2267104571490009696495029 212541053577188409046409)
                  ·
                    rfl

theorem cell21_931325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_931325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_931325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_931325 prefixEnd_931325 := by exact prefixLift 931325
  have htrace : WordTrace (prefixWord ++ tailWord_931325) baseStart_931325 baseEnd_931325 := by
    simpa [prefixWord, tailWord_931325, baseEnd_931325] using wordTrace_append hprefix tailTrace_931325
  have hstable : (prefixWord ++ tailWord_931325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931325).length < 2 ^ (prefixWord ++ tailWord_931325).sum := by decide
  have hdescent : baseEnd_931325 < baseStart_931325 := by decide
  rcases family_descends (prefixWord ++ tailWord_931325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931429 : List Nat := [1, 3, 1, 3, 3, 2, 8]
def baseStart_931429 : Nat := 118140960795 + 931429 * 2 ^ 59
def prefixEnd_931429 : Nat := 4983230072969 + 3 ^ 40 * 931429 * 2
def baseEnd_931429 : Nat := 23618309754900815479207

theorem tailTrace_931429 : CollatzResearch.WordTrace tailWord_931429 prefixEnd_931429 23618309754900815479207 := by
  unfold tailWord_931429
  simp only [CollatzResearch.WordTrace]
  refine ⟨33972006542599283253669341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22648004361732855502446227 33972006542599283253669341)
  ·
    refine ⟨12739502453474731220126003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33972006542599283253669341 12739502453474731220126003)
    ·
      refine ⟨19109253680212096830189005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12739502453474731220126003 19109253680212096830189005)
      ·
        refine ⟨7165970130079536311320877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19109253680212096830189005 7165970130079536311320877)
        ·
          refine ⟨2687238798779826116745329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7165970130079536311320877 2687238798779826116745329)
          ·
            refine ⟨2015429099084869587558997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2687238798779826116745329 2015429099084869587558997)
            ·
              refine ⟨23618309754900815479207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2015429099084869587558997 23618309754900815479207)
              ·
                rfl

theorem cell21_931429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 8].length) (baseStart_931429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_931429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_931429 prefixEnd_931429 := by exact prefixLift 931429
  have htrace : WordTrace (prefixWord ++ tailWord_931429) baseStart_931429 baseEnd_931429 := by
    simpa [prefixWord, tailWord_931429, baseEnd_931429] using wordTrace_append hprefix tailTrace_931429
  have hstable : (prefixWord ++ tailWord_931429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931429).length < 2 ^ (prefixWord ++ tailWord_931429).sum := by decide
  have hdescent : baseEnd_931429 < baseStart_931429 := by decide
  rcases family_descends (prefixWord ++ tailWord_931429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931432 : List Nat := [2, 1, 4, 3, 1, 1, 3, 2, 4]
def baseStart_931432 : Nat := 118140960795 + 931432 * 2 ^ 59
def prefixEnd_931432 : Nat := 4983230072969 + 3 ^ 40 * 931432 * 2
def baseEnd_931432 : Nat := 212565472434980000762857

theorem tailTrace_931432 : CollatzResearch.WordTrace tailWord_931432 prefixEnd_931432 212565472434980000762857 := by
  unfold tailWord_931432
  simp only [CollatzResearch.WordTrace]
  refine ⟨16986057980794207383014275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22648077307725609844019033 16986057980794207383014275)
  ·
    refine ⟨25479086971191311074521413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16986057980794207383014275 25479086971191311074521413)
    ·
      refine ⟨4777328807098370826472765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25479086971191311074521413 4777328807098370826472765)
      ·
        refine ⟨1791498302661889059927287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4777328807098370826472765 1791498302661889059927287)
        ·
          refine ⟨2687247453992833589890931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1791498302661889059927287 2687247453992833589890931)
          ·
            refine ⟨4030871180989250384836397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2687247453992833589890931 4030871180989250384836397)
            ·
              refine ⟨1511576692870968894313649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4030871180989250384836397 1511576692870968894313649)
              ·
                refine ⟨1133682519653226670735237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1511576692870968894313649 1133682519653226670735237)
                ·
                  refine ⟨212565472434980000762857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1133682519653226670735237 212565472434980000762857)
                  ·
                    rfl

theorem cell21_931432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_931432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_931432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_931432 prefixEnd_931432 := by exact prefixLift 931432
  have htrace : WordTrace (prefixWord ++ tailWord_931432) baseStart_931432 baseEnd_931432 := by
    simpa [prefixWord, tailWord_931432, baseEnd_931432] using wordTrace_append hprefix tailTrace_931432
  have hstable : (prefixWord ++ tailWord_931432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931432).length < 2 ^ (prefixWord ++ tailWord_931432).sum := by decide
  have hdescent : baseEnd_931432 < baseStart_931432 := by decide
  rcases family_descends (prefixWord ++ tailWord_931432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931519 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 7]
def baseStart_931519 : Nat := 118140960795 + 931519 * 2 ^ 59
def prefixEnd_931519 : Nat := 4983230072969 + 3 ^ 40 * 931519 * 2
def baseEnd_931519 : Nat := 212585327020287182812679

theorem tailTrace_931519 : CollatzResearch.WordTrace tailWord_931519 prefixEnd_931519 212585327020287182812679 := by
  unfold tailWord_931519
  simp only [CollatzResearch.WordTrace]
  refine ⟨33975289112273228624445611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22650192741515485749630407 33975289112273228624445611)
  ·
    refine ⟨50962933668409842936668417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33975289112273228624445611 50962933668409842936668417)
    ·
      refine ⟨38222200251307382202501313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50962933668409842936668417 38222200251307382202501313)
      ·
        refine ⟨28666650188480536651875985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38222200251307382202501313 28666650188480536651875985)
        ·
          refine ⟨21499987641360402488906989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28666650188480536651875985 21499987641360402488906989)
          ·
            refine ⟨8062495365510150933340121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21499987641360402488906989 8062495365510150933340121)
            ·
              refine ⟨6046871524132613200005091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8062495365510150933340121 6046871524132613200005091)
              ·
                refine ⟨9070307286198919800007637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6046871524132613200005091 9070307286198919800007637)
                ·
                  refine ⟨212585327020287182812679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9070307286198919800007637 212585327020287182812679)
                  ·
                    rfl

theorem cell21_931519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 7].length) (baseStart_931519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_931519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_931519 prefixEnd_931519 := by exact prefixLift 931519
  have htrace : WordTrace (prefixWord ++ tailWord_931519) baseStart_931519 baseEnd_931519 := by
    simpa [prefixWord, tailWord_931519, baseEnd_931519] using wordTrace_append hprefix tailTrace_931519
  have hstable : (prefixWord ++ tailWord_931519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931519).length < 2 ^ (prefixWord ++ tailWord_931519).sum := by decide
  have hdescent : baseEnd_931519 < baseStart_931519 := by decide
  rcases family_descends (prefixWord ++ tailWord_931519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931542 : List Nat := [5, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_931542 : Nat := 118140960795 + 931542 * 2 ^ 59
def prefixEnd_931542 : Nat := 4983230072969 + 3 ^ 40 * 931542 * 2
def baseEnd_931542 : Nat := 212590575933644253929299

theorem tailTrace_931542 : CollatzResearch.WordTrace tailWord_931542 prefixEnd_931542 212590575933644253929299 := by
  unfold tailWord_931542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2123507999449368972033305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22650751994126602368355253 2123507999449368972033305)
  ·
    refine ⟨1592630999587026729024979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2123507999449368972033305 1592630999587026729024979)
    ·
      refine ⟨2388946499380540093537469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1592630999587026729024979 2388946499380540093537469)
      ·
        refine ⟨895854937267702535076551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2388946499380540093537469 895854937267702535076551)
        ·
          refine ⟨1343782405901553802614827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 895854937267702535076551 1343782405901553802614827)
          ·
            refine ⟨2015673608852330703922241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343782405901553802614827 2015673608852330703922241)
            ·
              refine ⟨1511755206639248027941681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2015673608852330703922241 1511755206639248027941681)
              ·
                refine ⟨1133816404979436020956261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1511755206639248027941681 1133816404979436020956261)
                ·
                  refine ⟨212590575933644253929299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1133816404979436020956261 212590575933644253929299)
                  ·
                    rfl

theorem cell21_931542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_931542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_931542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_931542 prefixEnd_931542 := by exact prefixLift 931542
  have htrace : WordTrace (prefixWord ++ tailWord_931542) baseStart_931542 baseEnd_931542 := by
    simpa [prefixWord, tailWord_931542, baseEnd_931542] using wordTrace_append hprefix tailTrace_931542
  have hstable : (prefixWord ++ tailWord_931542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931542).length < 2 ^ (prefixWord ++ tailWord_931542).sum := by decide
  have hdescent : baseEnd_931542 < baseStart_931542 := by decide
  rcases family_descends (prefixWord ++ tailWord_931542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931612 : List Nat := [2, 2, 3, 1, 1, 2, 4, 1, 5]
def baseStart_931612 : Nat := 118140960795 + 931612 * 2 ^ 59
def prefixEnd_931612 : Nat := 4983230072969 + 3 ^ 40 * 931612 * 2
def baseEnd_931612 : Nat := 212606550887339687762489

theorem tailTrace_931612 : CollatzResearch.WordTrace tailWord_931612 prefixEnd_931612 212606550887339687762489 := by
  unfold tailWord_931612
  simp only [CollatzResearch.WordTrace]
  refine ⟨16989340550468152753790545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22652454067290870338387393 16989340550468152753790545)
  ·
    refine ⟨12742005412851114565342909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16989340550468152753790545 12742005412851114565342909)
    ·
      refine ⟨4778252029819167962003591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12742005412851114565342909 4778252029819167962003591)
      ·
        refine ⟨7167378044728751943005387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4778252029819167962003591 7167378044728751943005387)
        ·
          refine ⟨10751067067093127914508081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7167378044728751943005387 10751067067093127914508081)
          ·
            refine ⟨8063300300319845935881061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10751067067093127914508081 8063300300319845935881061)
            ·
              refine ⟨1511868806309971112977699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8063300300319845935881061 1511868806309971112977699)
              ·
                refine ⟨2267803209464956669466549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511868806309971112977699 2267803209464956669466549)
                ·
                  refine ⟨212606550887339687762489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2267803209464956669466549 212606550887339687762489)
                  ·
                    rfl

theorem cell21_931612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_931612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_931612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_931612 prefixEnd_931612 := by exact prefixLift 931612
  have htrace : WordTrace (prefixWord ++ tailWord_931612) baseStart_931612 baseEnd_931612 := by
    simpa [prefixWord, tailWord_931612, baseEnd_931612] using wordTrace_append hprefix tailTrace_931612
  have hstable : (prefixWord ++ tailWord_931612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931612).length < 2 ^ (prefixWord ++ tailWord_931612).sum := by decide
  have hdescent : baseEnd_931612 < baseStart_931612 := by decide
  rcases family_descends (prefixWord ++ tailWord_931612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931646 : List Nat := [4, 2, 1, 2, 2, 1, 3, 3, 3]
def baseStart_931646 : Nat := 118140960795 + 931646 * 2 ^ 59
def prefixEnd_931646 : Nat := 4983230072969 + 3 ^ 40 * 931646 * 2
def baseEnd_931646 : Nat := 212614310150563184195753

theorem tailTrace_931646 : CollatzResearch.WordTrace tailWord_931646 prefixEnd_931646 212614310150563184195753 := by
  unfold tailWord_931646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4247490147851641164289849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22653280788542086209545861 4247490147851641164289849)
  ·
    refine ⟨3185617610888730873217387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4247490147851641164289849 3185617610888730873217387)
    ·
      refine ⟨4778426416333096309826081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3185617610888730873217387 4778426416333096309826081)
      ·
        refine ⟨3583819812249822232369561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4778426416333096309826081 3583819812249822232369561)
        ·
          refine ⟨2687864859187366674277171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3583819812249822232369561 2687864859187366674277171)
          ·
            refine ⟨4031797288781050011415757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2687864859187366674277171 4031797288781050011415757)
            ·
              refine ⟨1511923983292893754280909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4031797288781050011415757 1511923983292893754280909)
              ·
                refine ⟨566971493734835157855341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1511923983292893754280909 566971493734835157855341)
                ·
                  refine ⟨212614310150563184195753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 566971493734835157855341 212614310150563184195753)
                  ·
                    rfl

theorem cell21_931646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_931646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_931646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_931646 prefixEnd_931646 := by exact prefixLift 931646
  have htrace : WordTrace (prefixWord ++ tailWord_931646) baseStart_931646 baseEnd_931646 := by
    simpa [prefixWord, tailWord_931646, baseEnd_931646] using wordTrace_append hprefix tailTrace_931646
  have hstable : (prefixWord ++ tailWord_931646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931646).length < 2 ^ (prefixWord ++ tailWord_931646).sum := by decide
  have hdescent : baseEnd_931646 < baseStart_931646 := by decide
  rcases family_descends (prefixWord ++ tailWord_931646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931722 : List Nat := [3, 1, 2, 4, 2, 1, 1, 4, 3]
def baseStart_931722 : Nat := 118140960795 + 931722 * 2 ^ 59
def prefixEnd_931722 : Nat := 4983230072969 + 3 ^ 40 * 931722 * 2
def baseEnd_931722 : Nat := 212631654386003940928931

theorem tailTrace_931722 : CollatzResearch.WordTrace tailWord_931722 prefixEnd_931722 212631654386003940928931 := by
  unfold tailWord_931722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8495673282634448573521355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22655128753691862862723613 8495673282634448573521355)
  ·
    refine ⟨12743509923951672860282033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8495673282634448573521355 12743509923951672860282033)
    ·
      refine ⟨9557632442963754645211525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12743509923951672860282033 9557632442963754645211525)
      ·
        refine ⟨1792056083055703995977161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9557632442963754645211525 1792056083055703995977161)
        ·
          refine ⟨1344042062291777996982871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1792056083055703995977161 1344042062291777996982871)
          ·
            refine ⟨2016063093437666995474307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1344042062291777996982871 2016063093437666995474307)
            ·
              refine ⟨3024094640156500493211461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2016063093437666995474307 3024094640156500493211461)
              ·
                refine ⟨567017745029343842477149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3024094640156500493211461 567017745029343842477149)
                ·
                  refine ⟨212631654386003940928931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 567017745029343842477149 212631654386003940928931)
                  ·
                    rfl

theorem cell21_931722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_931722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_931722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_931722 prefixEnd_931722 := by exact prefixLift 931722
  have htrace : WordTrace (prefixWord ++ tailWord_931722) baseStart_931722 baseEnd_931722 := by
    simpa [prefixWord, tailWord_931722, baseEnd_931722] using wordTrace_append hprefix tailTrace_931722
  have hstable : (prefixWord ++ tailWord_931722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931722).length < 2 ^ (prefixWord ++ tailWord_931722).sum := by decide
  have hdescent : baseEnd_931722 < baseStart_931722 := by decide
  rcases family_descends (prefixWord ++ tailWord_931722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931809 : List Nat := [1, 2, 3, 1, 2, 1, 6, 5]
def baseStart_931809 : Nat := 118140960795 + 931809 * 2 ^ 59
def prefixEnd_931809 : Nat := 4983230072969 + 3 ^ 40 * 931809 * 2
def baseEnd_931809 : Nat := 70883836323770374326251

theorem tailTrace_931809 : CollatzResearch.WordTrace tailWord_931809 prefixEnd_931809 70883836323770374326251 := by
  unfold tailWord_931809
  simp only [CollatzResearch.WordTrace]
  refine ⟨33985866281222608152502481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22657244187481738768334987 33985866281222608152502481)
  ·
    refine ⟨25489399710916956114376861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33985866281222608152502481 25489399710916956114376861)
    ·
      refine ⟨9558524891593858542891323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25489399710916956114376861 9558524891593858542891323)
      ·
        refine ⟨14337787337390787814336985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9558524891593858542891323 14337787337390787814336985)
        ·
          refine ⟨10753340503043090860752739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14337787337390787814336985 10753340503043090860752739)
          ·
            refine ⟨16130010754564636291129109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10753340503043090860752739 16130010754564636291129109)
            ·
              refine ⟨756094254120217326146677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16130010754564636291129109 756094254120217326146677)
              ·
                refine ⟨70883836323770374326251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 756094254120217326146677 70883836323770374326251)
                ·
                  rfl

theorem cell21_931809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 5].length) (baseStart_931809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_931809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_931809 prefixEnd_931809 := by exact prefixLift 931809
  have htrace : WordTrace (prefixWord ++ tailWord_931809) baseStart_931809 baseEnd_931809 := by
    simpa [prefixWord, tailWord_931809, baseEnd_931809] using wordTrace_append hprefix tailTrace_931809
  have hstable : (prefixWord ++ tailWord_931809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931809).length < 2 ^ (prefixWord ++ tailWord_931809).sum := by decide
  have hdescent : baseEnd_931809 < baseStart_931809 := by decide
  rcases family_descends (prefixWord ++ tailWord_931809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931815 : List Nat := [1, 1, 5, 2, 4, 1, 1, 3, 3]
def baseStart_931815 : Nat := 118140960795 + 931815 * 2 ^ 59
def prefixEnd_931815 : Nat := 4983230072969 + 3 ^ 40 * 931815 * 2
def baseEnd_931815 : Nat := 212652878253056445878741

theorem tailTrace_931815 : CollatzResearch.WordTrace tailWord_931815 prefixEnd_931815 212652878253056445878741 := by
  unfold tailWord_931815
  simp only [CollatzResearch.WordTrace]
  refine ⟨33986085119200871177220899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22657390079467247451480599 33986085119200871177220899)
  ·
    refine ⟨50979127678801306765831349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33986085119200871177220899 50979127678801306765831349)
    ·
      refine ⟨4779293219887622509296689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50979127678801306765831349 4779293219887622509296689)
      ·
        refine ⟨3584469914915716881972517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4779293219887622509296689 3584469914915716881972517)
        ·
          refine ⟨672088109046696915369847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3584469914915716881972517 672088109046696915369847)
          ·
            refine ⟨1008132163570045373054771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672088109046696915369847 1008132163570045373054771)
            ·
              refine ⟨1512198245355068059582157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008132163570045373054771 1512198245355068059582157)
              ·
                refine ⟨567074342008150522343309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1512198245355068059582157 567074342008150522343309)
                ·
                  refine ⟨212652878253056445878741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 567074342008150522343309 212652878253056445878741)
                  ·
                    rfl

theorem cell21_931815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 3].length) (baseStart_931815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_931815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_931815 prefixEnd_931815 := by exact prefixLift 931815
  have htrace : WordTrace (prefixWord ++ tailWord_931815) baseStart_931815 baseEnd_931815 := by
    simpa [prefixWord, tailWord_931815, baseEnd_931815] using wordTrace_append hprefix tailTrace_931815
  have hstable : (prefixWord ++ tailWord_931815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931815).length < 2 ^ (prefixWord ++ tailWord_931815).sum := by decide
  have hdescent : baseEnd_931815 < baseStart_931815 := by decide
  rcases family_descends (prefixWord ++ tailWord_931815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931975 : List Nat := [1, 1, 4, 2, 1, 1, 4, 2, 5]
def baseStart_931975 : Nat := 118140960795 + 931975 * 2 ^ 59
def prefixEnd_931975 : Nat := 4983230072969 + 3 ^ 40 * 931975 * 2
def baseEnd_931975 : Nat := 212689392432931723211747

theorem tailTrace_931975 : CollatzResearch.WordTrace tailWord_931975 prefixEnd_931975 212689392432931723211747 := by
  unfold tailWord_931975
  simp only [CollatzResearch.WordTrace]
  refine ⟨33991920798621218503045379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22661280532414145668696919 33991920798621218503045379)
  ·
    refine ⟨50987881197931827754568069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33991920798621218503045379 50987881197931827754568069)
    ·
      refine ⟨9560227724612217703981513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50987881197931827754568069 9560227724612217703981513)
      ·
        refine ⟨7170170793459163277986135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9560227724612217703981513 7170170793459163277986135)
        ·
          refine ⟨10755256190188744916979203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7170170793459163277986135 10755256190188744916979203)
          ·
            refine ⟨16132884285283117375468805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10755256190188744916979203 16132884285283117375468805)
            ·
              refine ⟨3024915803490584507900401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16132884285283117375468805 3024915803490584507900401)
              ·
                refine ⟨2268686852617938380925301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3024915803490584507900401 2268686852617938380925301)
                ·
                  refine ⟨212689392432931723211747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2268686852617938380925301 212689392432931723211747)
                  ·
                    rfl

theorem cell21_931975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 5].length) (baseStart_931975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_931975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_931975 prefixEnd_931975 := by exact prefixLift 931975
  have htrace : WordTrace (prefixWord ++ tailWord_931975) baseStart_931975 baseEnd_931975 := by
    simpa [prefixWord, tailWord_931975, baseEnd_931975] using wordTrace_append hprefix tailTrace_931975
  have hstable : (prefixWord ++ tailWord_931975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931975).length < 2 ^ (prefixWord ++ tailWord_931975).sum := by decide
  have hdescent : baseEnd_931975 < baseStart_931975 := by decide
  rcases family_descends (prefixWord ++ tailWord_931975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931978 : List Nat := [3, 1, 2, 3, 1, 4, 2, 5]
def baseStart_931978 : Nat := 118140960795 + 931978 * 2 ^ 59
def prefixEnd_931978 : Nat := 4983230072969 + 3 ^ 40 * 931978 * 2
def baseEnd_931978 : Nat := 70896692357934794887247

theorem tailTrace_931978 : CollatzResearch.WordTrace tailWord_931978 prefixEnd_931978 70896692357934794887247 := by
  unfold tailWord_931978
  simp only [CollatzResearch.WordTrace]
  refine ⟨8498007554402587503851147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22661353478406900010269725 8498007554402587503851147)
  ·
    refine ⟨12747011331603881255776721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8498007554402587503851147 12747011331603881255776721)
    ·
      refine ⟨9560258498702910941832541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12747011331603881255776721 9560258498702910941832541)
      ·
        refine ⟨3585096937013591603187203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9560258498702910941832541 3585096937013591603187203)
        ·
          refine ⟨5377645405520387404780805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3585096937013591603187203 5377645405520387404780805)
          ·
            refine ⟨1008308513535072638396401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5377645405520387404780805 1008308513535072638396401)
            ·
              refine ⟨756231385151304478797301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1008308513535072638396401 756231385151304478797301)
              ·
                refine ⟨70896692357934794887247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 756231385151304478797301 70896692357934794887247)
                ·
                  rfl

theorem cell21_931978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_931978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_931978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_931978 prefixEnd_931978 := by exact prefixLift 931978
  have htrace : WordTrace (prefixWord ++ tailWord_931978) baseStart_931978 baseEnd_931978 := by
    simpa [prefixWord, tailWord_931978, baseEnd_931978] using wordTrace_append hprefix tailTrace_931978
  have hstable : (prefixWord ++ tailWord_931978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931978).length < 2 ^ (prefixWord ++ tailWord_931978).sum := by decide
  have hdescent : baseEnd_931978 < baseStart_931978 := by decide
  rcases family_descends (prefixWord ++ tailWord_931978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_931989 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 8]
def baseStart_931989 : Nat := 118140960795 + 931989 * 2 ^ 59
def prefixEnd_931989 : Nat := 4983230072969 + 3 ^ 40 * 931989 * 2
def baseEnd_931989 : Nat := 212692587423670809978385

theorem tailTrace_931989 : CollatzResearch.WordTrace tailWord_931989 prefixEnd_931989 212692587423670809978385 := by
  unfold tailWord_931989
  simp only [CollatzResearch.WordTrace]
  refine ⟨33992431420570498894055021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22661620947046999262703347 33992431420570498894055021)
  ·
    refine ⟨12747161782713937085270633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33992431420570498894055021 12747161782713937085270633)
    ·
      refine ⟨9560371337035452813952975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12747161782713937085270633 9560371337035452813952975)
      ·
        refine ⟨14340557005553179220929463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9560371337035452813952975 14340557005553179220929463)
        ·
          refine ⟨21510835508329768831394195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14340557005553179220929463 21510835508329768831394195)
          ·
            refine ⟨32266253262494653247091293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21510835508329768831394195 32266253262494653247091293)
            ·
              refine ⟨12099844973435494967659235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32266253262494653247091293 12099844973435494967659235)
              ·
                refine ⟨18149767460153242451488853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12099844973435494967659235 18149767460153242451488853)
                ·
                  refine ⟨212692587423670809978385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18149767460153242451488853 212692587423670809978385)
                  ·
                    rfl

theorem cell21_931989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_931989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_931989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_931989 prefixEnd_931989 := by exact prefixLift 931989
  have htrace : WordTrace (prefixWord ++ tailWord_931989) baseStart_931989 baseEnd_931989 := by
    simpa [prefixWord, tailWord_931989, baseEnd_931989] using wordTrace_append hprefix tailTrace_931989
  have hstable : (prefixWord ++ tailWord_931989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_931989).length < 2 ^ (prefixWord ++ tailWord_931989).sum := by decide
  have hdescent : baseEnd_931989 < baseStart_931989 := by decide
  rcases family_descends (prefixWord ++ tailWord_931989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_932023 : List Nat := [1, 1, 3, 1, 4, 2, 4, 1, 4]
def baseStart_932023 : Nat := 118140960795 + 932023 * 2 ^ 59
def prefixEnd_932023 : Nat := 4983230072969 + 3 ^ 40 * 932023 * 2
def baseEnd_932023 : Nat := 212700346686894306411649

theorem tailTrace_932023 : CollatzResearch.WordTrace tailWord_932023 prefixEnd_932023 212700346686894306411649 := by
  unfold tailWord_932023
  simp only [CollatzResearch.WordTrace]
  refine ⟨33993671502447322700792723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22662447668298215133861815 33993671502447322700792723)
  ·
    refine ⟨50990507253670984051189085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33993671502447322700792723 50990507253670984051189085)
    ·
      refine ⟨19121440220126619019195907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50990507253670984051189085 19121440220126619019195907)
      ·
        refine ⟨28682160330189928528793861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19121440220126619019195907 28682160330189928528793861)
        ·
          refine ⟨5377905061910611599148849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28682160330189928528793861 5377905061910611599148849)
          ·
            refine ⟨4033428796432958699361637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5377905061910611599148849 4033428796432958699361637)
            ·
              refine ⟨756267899331179756130307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4033428796432958699361637 756267899331179756130307)
              ·
                refine ⟨1134401848996769634195461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756267899331179756130307 1134401848996769634195461)
                ·
                  refine ⟨212700346686894306411649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1134401848996769634195461 212700346686894306411649)
                  ·
                    rfl

theorem cell21_932023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 4].length) (baseStart_932023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_932023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_932023 prefixEnd_932023 := by exact prefixLift 932023
  have htrace : WordTrace (prefixWord ++ tailWord_932023) baseStart_932023 baseEnd_932023 := by
    simpa [prefixWord, tailWord_932023, baseEnd_932023] using wordTrace_append hprefix tailTrace_932023
  have hstable : (prefixWord ++ tailWord_932023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_932023).length < 2 ^ (prefixWord ++ tailWord_932023).sum := by decide
  have hdescent : baseEnd_932023 < baseStart_932023 := by decide
  rcases family_descends (prefixWord ++ tailWord_932023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
