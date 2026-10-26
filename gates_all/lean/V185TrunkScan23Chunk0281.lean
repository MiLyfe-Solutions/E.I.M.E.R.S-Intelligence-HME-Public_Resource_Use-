import V185TrunkScan23Chunk0280

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1661293 : List Nat := [1, 5, 1, 1, 1, 2, 1, 6, 1, 2, 2]
def baseStart_1661293 : Nat := 118140960795 + 1661293 * 2 ^ 59
def prefixEnd_1661293 : Nat := 4983230072969 + 3 ^ 40 * 1661293 * 2
def baseEnd_1661293 : Nat := 853041816949873917197359

theorem tailTrace_1661293 : CollatzResearch.WordTrace tailWord_1661293 prefixEnd_1661293 853041816949873917197359 := by
  unfold tailWord_1661293
  simp only [CollatzResearch.WordTrace]
  refine ⟨60592333570426662100908533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40394889046951108067272355 60592333570426662100908533)
  ·
    refine ⟨5680531272227499571960175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60592333570426662100908533 5680531272227499571960175)
    ·
      refine ⟨8520796908341249357940263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5680531272227499571960175 8520796908341249357940263)
      ·
        refine ⟨12781195362511874036910395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8520796908341249357940263 12781195362511874036910395)
        ·
          refine ⟨19171793043767811055365593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12781195362511874036910395 19171793043767811055365593)
          ·
            refine ⟨14378844782825858291524195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19171793043767811055365593 14378844782825858291524195)
            ·
              refine ⟨21568267174238787437286293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14378844782825858291524195 21568267174238787437286293)
              ·
                refine ⟨1011012523792443161122795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21568267174238787437286293 1011012523792443161122795)
                ·
                  refine ⟨1516518785688664741684193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011012523792443161122795 1516518785688664741684193)
                  ·
                    refine ⟨1137389089266498556263145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1516518785688664741684193 1137389089266498556263145)
                    ·
                      refine ⟨853041816949873917197359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1137389089266498556263145 853041816949873917197359)
                      ·
                        rfl

theorem cell23_1661293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_1661293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661293 prefixEnd_1661293 := by exact prefixLift 1661293
  have htrace : WordTrace (prefixWord ++ tailWord_1661293) baseStart_1661293 baseEnd_1661293 := by
    simpa [prefixWord, tailWord_1661293, baseEnd_1661293] using wordTrace_append hprefix tailTrace_1661293
  have hstable : (prefixWord ++ tailWord_1661293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661293).length < 2 ^ (prefixWord ++ tailWord_1661293).sum := by decide
  have hdescent : baseEnd_1661293 < baseStart_1661293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661295 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 2, 7]
def baseStart_1661295 : Nat := 118140960795 + 1661295 * 2 ^ 59
def prefixEnd_1661295 : Nat := 4983230072969 + 3 ^ 40 * 1661295 * 2
def baseEnd_1661295 : Nat := 284347614637060969790783

theorem tailTrace_1661295 : CollatzResearch.WordTrace tailWord_1661295 prefixEnd_1661295 284347614637060969790783 := by
  unfold tailWord_1661295
  simp only [CollatzResearch.WordTrace]
  refine ⟨60592406516419416442481339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40394937677612944294987559 60592406516419416442481339)
  ·
    refine ⟨90888609774629124663722009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60592406516419416442481339 90888609774629124663722009)
    ·
      refine ⟨68166457330971843497791507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90888609774629124663722009 68166457330971843497791507)
      ·
        refine ⟨102249685996457765246687261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68166457330971843497791507 102249685996457765246687261)
        ·
          refine ⟨38343632248671661967507723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102249685996457765246687261 38343632248671661967507723)
          ·
            refine ⟨57515448373007492951261585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38343632248671661967507723 57515448373007492951261585)
            ·
              refine ⟨43136586279755619713446189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57515448373007492951261585 43136586279755619713446189)
              ·
                refine ⟨16176219854908357392542321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43136586279755619713446189 16176219854908357392542321)
                ·
                  refine ⟨12132164891181268044406741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16176219854908357392542321 12132164891181268044406741)
                  ·
                    refine ⟨284347614637060969790783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12132164891181268044406741 284347614637060969790783)
                    ·
                      rfl

theorem cell23_1661295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 7].length) (baseStart_1661295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661295 prefixEnd_1661295 := by exact prefixLift 1661295
  have htrace : WordTrace (prefixWord ++ tailWord_1661295) baseStart_1661295 baseEnd_1661295 := by
    simpa [prefixWord, tailWord_1661295, baseEnd_1661295] using wordTrace_append hprefix tailTrace_1661295
  have hstable : (prefixWord ++ tailWord_1661295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661295).length < 2 ^ (prefixWord ++ tailWord_1661295).sum := by decide
  have hdescent : baseEnd_1661295 < baseStart_1661295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661309 : List Nat := [1, 4, 1, 1, 2, 3, 3, 1, 1, 3, 3]
def baseStart_1661309 : Nat := 118140960795 + 1661309 * 2 ^ 59
def prefixEnd_1661309 : Nat := 4983230072969 + 3 ^ 40 * 1661309 * 2
def baseEnd_1661309 : Nat := 853050032640345854597285

theorem tailTrace_1661309 : CollatzResearch.WordTrace tailWord_1661309 prefixEnd_1661309 853050032640345854597285 := by
  unfold tailWord_1661309
  simp only [CollatzResearch.WordTrace]
  refine ⟨60592917138368696833490981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40395278092245797888993987 60592917138368696833490981)
  ·
    refine ⟨11361171963444130656279559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60592917138368696833490981 11361171963444130656279559)
    ·
      refine ⟨17041757945166195984419339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11361171963444130656279559 17041757945166195984419339)
      ·
        refine ⟨25562636917749293976629009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17041757945166195984419339 25562636917749293976629009)
        ·
          refine ⟨19171977688311970482471757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25562636917749293976629009 19171977688311970482471757)
          ·
            refine ⟨7189491633116988930926909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19171977688311970482471757 7189491633116988930926909)
            ·
              refine ⟨2696059362418870849097591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7189491633116988930926909 2696059362418870849097591)
              ·
                refine ⟨4044089043628306273646387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2696059362418870849097591 4044089043628306273646387)
                ·
                  refine ⟨6066133565442459410469581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4044089043628306273646387 6066133565442459410469581)
                  ·
                    refine ⟨2274800087040922278926093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6066133565442459410469581 2274800087040922278926093)
                    ·
                      refine ⟨853050032640345854597285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2274800087040922278926093 853050032640345854597285)
                      ·
                        rfl

theorem cell23_1661309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_1661309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661309 prefixEnd_1661309 := by exact prefixLift 1661309
  have htrace : WordTrace (prefixWord ++ tailWord_1661309) baseStart_1661309 baseEnd_1661309 := by
    simpa [prefixWord, tailWord_1661309, baseEnd_1661309] using wordTrace_append hprefix tailTrace_1661309
  have hstable : (prefixWord ++ tailWord_1661309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661309).length < 2 ^ (prefixWord ++ tailWord_1661309).sum := by decide
  have hdescent : baseEnd_1661309 < baseStart_1661309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661326 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3]
def baseStart_1661326 : Nat := 118140960795 + 1661326 * 2 ^ 59
def prefixEnd_1661326 : Nat := 4983230072969 + 3 ^ 40 * 1661326 * 2
def baseEnd_1661326 : Nat := 853058761811472288084707

theorem tailTrace_1661326 : CollatzResearch.WordTrace tailWord_1661326 prefixEnd_1661326 853058761811472288084707 := by
  unfold tailWord_1661326
  simp only [CollatzResearch.WordTrace]
  refine ⟨7574192147413388592107479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40395691452871405824573221 7574192147413388592107479)
  ·
    refine ⟨11361288221120082888161219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7574192147413388592107479 11361288221120082888161219)
    ·
      refine ⟨17041932331680124332241829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11361288221120082888161219 17041932331680124332241829)
      ·
        refine ⟨3195362312190023312295343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17041932331680124332241829 3195362312190023312295343)
        ·
          refine ⟨4793043468285034968443015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3195362312190023312295343 4793043468285034968443015)
          ·
            refine ⟨7189565202427552452664523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4793043468285034968443015 7189565202427552452664523)
            ·
              refine ⟨10784347803641328678996785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7189565202427552452664523 10784347803641328678996785)
              ·
                refine ⟨8088260852730996509247589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10784347803641328678996785 8088260852730996509247589)
                ·
                  refine ⟨1516548909887061845483923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8088260852730996509247589 1516548909887061845483923)
                  ·
                    refine ⟨2274823364830592768225885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1516548909887061845483923 2274823364830592768225885)
                    ·
                      refine ⟨853058761811472288084707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2274823364830592768225885 853058761811472288084707)
                      ·
                        rfl

theorem cell23_1661326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_1661326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661326 prefixEnd_1661326 := by exact prefixLift 1661326
  have htrace : WordTrace (prefixWord ++ tailWord_1661326) baseStart_1661326 baseEnd_1661326 := by
    simpa [prefixWord, tailWord_1661326, baseEnd_1661326] using wordTrace_append hprefix tailTrace_1661326
  have hstable : (prefixWord ++ tailWord_1661326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661326).length < 2 ^ (prefixWord ++ tailWord_1661326).sum := by decide
  have hdescent : baseEnd_1661326 < baseStart_1661326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661354 : List Nat := [3, 1, 6, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1661354 : Nat := 118140960795 + 1661354 * 2 ^ 59
def prefixEnd_1661354 : Nat := 4983230072969 + 3 ^ 40 * 1661354 * 2
def baseEnd_1661354 : Nat := 284357713089932726178193

theorem tailTrace_1661354 : CollatzResearch.WordTrace tailWord_1661354 prefixEnd_1661354 284357713089932726178193 := by
  unfold tailWord_1661354
  simp only [CollatzResearch.WordTrace]
  refine ⟨15148639605801417379719779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40396372282137113012586077 15148639605801417379719779)
  ·
    refine ⟨22722959408702126069579669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15148639605801417379719779 22722959408702126069579669)
    ·
      refine ⟨1065138722282912159511547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22722959408702126069579669 1065138722282912159511547)
      ·
        refine ⟨1597708083424368239267321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1065138722282912159511547 1597708083424368239267321)
        ·
          refine ⟨1198281062568276179450491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1597708083424368239267321 1198281062568276179450491)
          ·
            refine ⟨1797421593852414269175737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198281062568276179450491 1797421593852414269175737)
            ·
              refine ⟨1348066195389310701881803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1797421593852414269175737 1348066195389310701881803)
              ·
                refine ⟨2022099293083966052822705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1348066195389310701881803 2022099293083966052822705)
                ·
                  refine ⟨1516574469812974539617029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2022099293083966052822705 1516574469812974539617029)
                  ·
                    refine ⟨284357713089932726178193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1516574469812974539617029 284357713089932726178193)
                    ·
                      rfl

theorem cell23_1661354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1661354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661354 prefixEnd_1661354 := by exact prefixLift 1661354
  have htrace : WordTrace (prefixWord ++ tailWord_1661354) baseStart_1661354 baseEnd_1661354 := by
    simpa [prefixWord, tailWord_1661354, baseEnd_1661354] using wordTrace_append hprefix tailTrace_1661354
  have hstable : (prefixWord ++ tailWord_1661354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661354).length < 2 ^ (prefixWord ++ tailWord_1661354).sum := by decide
  have hdescent : baseEnd_1661354 < baseStart_1661354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661362 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_1661362 : Nat := 118140960795 + 1661362 * 2 ^ 59
def prefixEnd_1661362 : Nat := 4983230072969 + 3 ^ 40 * 1661362 * 2
def baseEnd_1661362 : Nat := 853077247115034147234541

theorem tailTrace_1661362 : CollatzResearch.WordTrace tailWord_1661362 prefixEnd_1661362 853077247115034147234541 := by
  unfold tailWord_1661362
  simp only [CollatzResearch.WordTrace]
  refine ⟨15148712551794171721292585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40396566804784457923446893 15148712551794171721292585)
  ·
    refine ⟨11361534413845628790969439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15148712551794171721292585 11361534413845628790969439)
    ·
      refine ⟨17042301620768443186454159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11361534413845628790969439 17042301620768443186454159)
      ·
        refine ⟨25563452431152664779681239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17042301620768443186454159 25563452431152664779681239)
        ·
          refine ⟨38345178646728997169521859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25563452431152664779681239 38345178646728997169521859)
          ·
            refine ⟨57517767970093495754282789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38345178646728997169521859 57517767970093495754282789)
            ·
              refine ⟨10784581494392530453928023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57517767970093495754282789 10784581494392530453928023)
              ·
                refine ⟨16176872241588795680892035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10784581494392530453928023 16176872241588795680892035)
                ·
                  refine ⟨24265308362383193521338053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16176872241588795680892035 24265308362383193521338053)
                  ·
                    refine ⟨4549745317946848785250885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24265308362383193521338053 4549745317946848785250885)
                    ·
                      refine ⟨853077247115034147234541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4549745317946848785250885 853077247115034147234541)
                      ·
                        rfl

theorem cell23_1661362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_1661362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661362 prefixEnd_1661362 := by exact prefixLift 1661362
  have htrace : WordTrace (prefixWord ++ tailWord_1661362) baseStart_1661362 baseEnd_1661362 := by
    simpa [prefixWord, tailWord_1661362, baseEnd_1661362] using wordTrace_append hprefix tailTrace_1661362
  have hstable : (prefixWord ++ tailWord_1661362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661362).length < 2 ^ (prefixWord ++ tailWord_1661362).sum := by decide
  have hdescent : baseEnd_1661362 < baseStart_1661362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661409 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 1, 7, 2]
def baseStart_1661409 : Nat := 118140960795 + 1661409 * 2 ^ 59
def prefixEnd_1661409 : Nat := 4983230072969 + 3 ^ 40 * 1661409 * 2
def baseEnd_1661409 : Nat := 853101380705795463346825

theorem tailTrace_1661409 : CollatzResearch.WordTrace tailWord_1661409 prefixEnd_1661409 853101380705795463346825 := by
  unfold tailWord_1661409
  simp only [CollatzResearch.WordTrace]
  refine ⟨60596564438006413912131281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40397709625337609274754187 60596564438006413912131281)
  ·
    refine ⟨45447423328504810434098461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60596564438006413912131281 45447423328504810434098461)
    ·
      refine ⟨17042783748189303912786923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45447423328504810434098461 17042783748189303912786923)
      ·
        refine ⟨25564175622283955869180385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17042783748189303912786923 25564175622283955869180385)
        ·
          refine ⟨19173131716712966901885289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25564175622283955869180385 19173131716712966901885289)
          ·
            refine ⟨14379848787534725176413967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19173131716712966901885289 14379848787534725176413967)
            ·
              refine ⟨21569773181302087764620951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14379848787534725176413967 21569773181302087764620951)
              ·
                refine ⟨32354659771953131646931427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21569773181302087764620951 32354659771953131646931427)
                ·
                  refine ⟨48531989657929697470397141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32354659771953131646931427 48531989657929697470397141)
                  ·
                    refine ⟨1137468507607727284462433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48531989657929697470397141 1137468507607727284462433)
                    ·
                      refine ⟨853101380705795463346825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1137468507607727284462433 853101380705795463346825)
                      ·
                        rfl

theorem cell23_1661409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_1661409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661409 prefixEnd_1661409 := by exact prefixLift 1661409
  have htrace : WordTrace (prefixWord ++ tailWord_1661409) baseStart_1661409 baseEnd_1661409 := by
    simpa [prefixWord, tailWord_1661409, baseEnd_1661409] using wordTrace_append hprefix tailTrace_1661409
  have hstable : (prefixWord ++ tailWord_1661409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661409).length < 2 ^ (prefixWord ++ tailWord_1661409).sum := by decide
  have hdescent : baseEnd_1661409 < baseStart_1661409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661439 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 1, 6, 2]
def baseStart_1661439 : Nat := 118140960795 + 1661439 * 2 ^ 59
def prefixEnd_1661439 : Nat := 4983230072969 + 3 ^ 40 * 1661439 * 2
def baseEnd_1661439 : Nat := 853116785125430345971687

theorem tailTrace_1661439 : CollatzResearch.WordTrace tailWord_1661439 prefixEnd_1661439 853116785125430345971687 := by
  unfold tailWord_1661439
  simp only [CollatzResearch.WordTrace]
  refine ⟨60597658627897729035723371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40398439085265152690482247 60597658627897729035723371)
  ·
    refine ⟨90896487941846593553585057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60597658627897729035723371 90896487941846593553585057)
    ·
      refine ⟨68172365956384945165188793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90896487941846593553585057 68172365956384945165188793)
      ·
        refine ⟨51129274467288708873891595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68172365956384945165188793 51129274467288708873891595)
        ·
          refine ⟨76693911700933063310837393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51129274467288708873891595 76693911700933063310837393)
          ·
            refine ⟨57520433775699797483128045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76693911700933063310837393 57520433775699797483128045)
            ·
              refine ⟨21570162665887424056173017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57520433775699797483128045 21570162665887424056173017)
              ·
                refine ⟨16177621999415568042129763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21570162665887424056173017 16177621999415568042129763)
                ·
                  refine ⟨24266432999123352063194645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16177621999415568042129763 24266432999123352063194645)
                  ·
                    refine ⟨1137489046833907127962249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24266432999123352063194645 1137489046833907127962249)
                    ·
                      refine ⟨853116785125430345971687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1137489046833907127962249 853116785125430345971687)
                      ·
                        rfl

theorem cell23_1661439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 6, 2].length) (baseStart_1661439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661439 prefixEnd_1661439 := by exact prefixLift 1661439
  have htrace : WordTrace (prefixWord ++ tailWord_1661439) baseStart_1661439 baseEnd_1661439 := by
    simpa [prefixWord, tailWord_1661439, baseEnd_1661439] using wordTrace_append hprefix tailTrace_1661439
  have hstable : (prefixWord ++ tailWord_1661439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661439).length < 2 ^ (prefixWord ++ tailWord_1661439).sum := by decide
  have hdescent : baseEnd_1661439 < baseStart_1661439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661459 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 3]
def baseStart_1661459 : Nat := 118140960795 + 1661459 * 2 ^ 59
def prefixEnd_1661459 : Nat := 4983230072969 + 3 ^ 40 * 1661459 * 2
def baseEnd_1661459 : Nat := 853127054738520267721595

theorem tailTrace_1661459 : CollatzResearch.WordTrace tailWord_1661459 prefixEnd_1661459 853127054738520267721595 := by
  unfold tailWord_1661459
  simp only [CollatzResearch.WordTrace]
  refine ⟨60598388087825272451451431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40398925391883514967634287 60598388087825272451451431)
  ·
    refine ⟨90897582131737908677177147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60598388087825272451451431 90897582131737908677177147)
    ·
      refine ⟨136346373197606863015765721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90897582131737908677177147 136346373197606863015765721)
      ·
        refine ⟨102259779898205147261824291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136346373197606863015765721 102259779898205147261824291)
        ·
          refine ⟨153389669847307720892736437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102259779898205147261824291 153389669847307720892736437)
          ·
            refine ⟨14380281548185098833694041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 153389669847307720892736437 14380281548185098833694041)
            ·
              refine ⟨10785211161138824125270531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14380281548185098833694041 10785211161138824125270531)
              ·
                refine ⟨16177816741708236187905797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10785211161138824125270531 16177816741708236187905797)
                ·
                  refine ⟨3033340639070294285232337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16177816741708236187905797 3033340639070294285232337)
                  ·
                    refine ⟨2275005479302720713924253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3033340639070294285232337 2275005479302720713924253)
                    ·
                      refine ⟨853127054738520267721595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2275005479302720713924253 853127054738520267721595)
                      ·
                        rfl

theorem cell23_1661459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 2, 3].length) (baseStart_1661459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661459 prefixEnd_1661459 := by exact prefixLift 1661459
  have htrace : WordTrace (prefixWord ++ tailWord_1661459) baseStart_1661459 baseEnd_1661459 := by
    simpa [prefixWord, tailWord_1661459, baseEnd_1661459] using wordTrace_append hprefix tailTrace_1661459
  have hstable : (prefixWord ++ tailWord_1661459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661459).length < 2 ^ (prefixWord ++ tailWord_1661459).sum := by decide
  have hdescent : baseEnd_1661459 < baseStart_1661459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661500 : List Nat := [2, 2, 2, 2, 3, 3, 1, 3, 1, 4]
def baseStart_1661500 : Nat := 118140960795 + 1661500 * 2 ^ 59
def prefixEnd_1661500 : Nat := 4983230072969 + 3 ^ 40 * 1661500 * 2
def baseEnd_1661500 : Nat := 284382702481784869102969

theorem tailTrace_1661500 : CollatzResearch.WordTrace tailWord_1661500 prefixEnd_1661500 284382702481784869102969 := by
  unfold tailWord_1661500
  simp only [CollatzResearch.WordTrace]
  refine ⟨30299941740338368226846977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40399922320451157635795969 30299941740338368226846977)
  ·
    refine ⟨22724956305253776170135233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30299941740338368226846977 22724956305253776170135233)
    ·
      refine ⟨17043717228940332127601425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22724956305253776170135233 17043717228940332127601425)
      ·
        refine ⟨12782787921705249095701069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17043717228940332127601425 12782787921705249095701069)
        ·
          refine ⟨4793545470639468410887901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12782787921705249095701069 4793545470639468410887901)
          ·
            refine ⟨1797579551489800654082963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4793545470639468410887901 1797579551489800654082963)
            ·
              refine ⟨2696369327234700981124445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1797579551489800654082963 2696369327234700981124445)
              ·
                refine ⟨1011138497713012867921667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2696369327234700981124445 1011138497713012867921667)
                ·
                  refine ⟨1516707746569519301882501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011138497713012867921667 1516707746569519301882501)
                  ·
                    refine ⟨284382702481784869102969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1516707746569519301882501 284382702481784869102969)
                    ·
                      rfl

theorem cell23_1661500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_1661500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661500 prefixEnd_1661500 := by exact prefixLift 1661500
  have htrace : WordTrace (prefixWord ++ tailWord_1661500) baseStart_1661500 baseEnd_1661500 := by
    simpa [prefixWord, tailWord_1661500, baseEnd_1661500] using wordTrace_append hprefix tailTrace_1661500
  have hstable : (prefixWord ++ tailWord_1661500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661500).length < 2 ^ (prefixWord ++ tailWord_1661500).sum := by decide
  have hdescent : baseEnd_1661500 < baseStart_1661500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661510 : List Nat := [6, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_1661510 : Nat := 118140960795 + 1661510 * 2 ^ 59
def prefixEnd_1661510 : Nat := 4983230072969 + 3 ^ 40 * 1661510 * 2
def baseEnd_1661510 : Nat := 853153242251899568183861

theorem tailTrace_1661510 : CollatzResearch.WordTrace tailWord_1661510 prefixEnd_1661510 853153242251899568183861 := by
  unfold tailWord_1661510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1893757756582515880048687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40400165473760338774371989 1893757756582515880048687)
  ·
    refine ⟨2840636634873773820073031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1893757756582515880048687 2840636634873773820073031)
    ·
      refine ⟨4260954952310660730109547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2840636634873773820073031 4260954952310660730109547)
      ·
        refine ⟨6391432428465991095164321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4260954952310660730109547 6391432428465991095164321)
        ·
          refine ⟨4793574321349493321373241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6391432428465991095164321 4793574321349493321373241)
          ·
            refine ⟨3595180741012119991029931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4793574321349493321373241 3595180741012119991029931)
            ·
              refine ⟨5392771111518179986544897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3595180741012119991029931 5392771111518179986544897)
              ·
                refine ⟨4044578333638634989908673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5392771111518179986544897 4044578333638634989908673)
                ·
                  refine ⟨3033433750228976242431505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4044578333638634989908673 3033433750228976242431505)
                  ·
                    refine ⟨2275075312671732181823629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3033433750228976242431505 2275075312671732181823629)
                    ·
                      refine ⟨853153242251899568183861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2275075312671732181823629 853153242251899568183861)
                      ·
                        rfl

theorem cell23_1661510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_1661510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661510 prefixEnd_1661510 := by exact prefixLift 1661510
  have htrace : WordTrace (prefixWord ++ tailWord_1661510) baseStart_1661510 baseEnd_1661510 := by
    simpa [prefixWord, tailWord_1661510, baseEnd_1661510] using wordTrace_append hprefix tailTrace_1661510
  have hstable : (prefixWord ++ tailWord_1661510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661510).length < 2 ^ (prefixWord ++ tailWord_1661510).sum := by decide
  have hdescent : baseEnd_1661510 < baseStart_1661510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661517 : List Nat := [1, 6, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_1661517 : Nat := 118140960795 + 1661517 * 2 ^ 59
def prefixEnd_1661517 : Nat := 4983230072969 + 3 ^ 40 * 1661517 * 2
def baseEnd_1661517 : Nat := 284385612205493680265443

theorem tailTrace_1661517 : CollatzResearch.WordTrace tailWord_1661517 prefixEnd_1661517 284385612205493680265443 := by
  unfold tailWord_1661517
  simp only [CollatzResearch.WordTrace]
  refine ⟨60600503521615148357062805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40400335681076765571375203 60600503521615148357062805)
  ·
    refine ⟨2840648602575710079237319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60600503521615148357062805 2840648602575710079237319)
    ·
      refine ⟨4260972903863565118855979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2840648602575710079237319 4260972903863565118855979)
      ·
        refine ⟨6391459355795347678283969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4260972903863565118855979 6391459355795347678283969)
        ·
          refine ⟨4793594516846510758712977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6391459355795347678283969 4793594516846510758712977)
          ·
            refine ⟨3595195887634883069034733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4793594516846510758712977 3595195887634883069034733)
            ·
              refine ⟨1348198457863081150888025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3595195887634883069034733 1348198457863081150888025)
              ·
                refine ⟨1011148843397310863166019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1348198457863081150888025 1011148843397310863166019)
                ·
                  refine ⟨1516723265095966294749029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011148843397310863166019 1516723265095966294749029)
                  ·
                    refine ⟨284385612205493680265443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1516723265095966294749029 284385612205493680265443)
                    ·
                      rfl

theorem cell23_1661517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_1661517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661517 prefixEnd_1661517 := by exact prefixLift 1661517
  have htrace : WordTrace (prefixWord ++ tailWord_1661517) baseStart_1661517 baseEnd_1661517 := by
    simpa [prefixWord, tailWord_1661517, baseEnd_1661517] using wordTrace_append hprefix tailTrace_1661517
  have hstable : (prefixWord ++ tailWord_1661517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661517).length < 2 ^ (prefixWord ++ tailWord_1661517).sum := by decide
  have hdescent : baseEnd_1661517 < baseStart_1661517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661539 : List Nat := [1, 1, 1, 5, 1, 2, 2, 3, 1, 6]
def baseStart_1661539 : Nat := 118140960795 + 1661539 * 2 ^ 59
def prefixEnd_1661539 : Nat := 4983230072969 + 3 ^ 40 * 1661539 * 2
def baseEnd_1661539 : Nat := 284389377730293318240409

theorem tailTrace_1661539 : CollatzResearch.WordTrace tailWord_1661539 prefixEnd_1661539 284389377730293318240409 := by
  unfold tailWord_1661539
  simp only [CollatzResearch.WordTrace]
  refine ⟨60601305927535446114363671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40400870618356964076242447 60601305927535446114363671)
  ·
    refine ⟨90901958891303169171545507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60601305927535446114363671 90901958891303169171545507)
    ·
      refine ⟨136352938336954753757318261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90901958891303169171545507 136352938336954753757318261)
      ·
        refine ⟨12783087969089508164748587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136352938336954753757318261 12783087969089508164748587)
        ·
          refine ⟨19174631953634262247122881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12783087969089508164748587 19174631953634262247122881)
          ·
            refine ⟨14380973965225696685342161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19174631953634262247122881 14380973965225696685342161)
            ·
              refine ⟨10785730473919272514006621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14380973965225696685342161 10785730473919272514006621)
              ·
                refine ⟨4044648927719727192752483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10785730473919272514006621 4044648927719727192752483)
                ·
                  refine ⟨6066973391579590789128725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4044648927719727192752483 6066973391579590789128725)
                  ·
                    refine ⟨284389377730293318240409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6066973391579590789128725 284389377730293318240409)
                    ·
                      rfl

theorem cell23_1661539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 6].length) (baseStart_1661539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661539 prefixEnd_1661539 := by exact prefixLift 1661539
  have htrace : WordTrace (prefixWord ++ tailWord_1661539) baseStart_1661539 baseEnd_1661539 := by
    simpa [prefixWord, tailWord_1661539, baseEnd_1661539] using wordTrace_append hprefix tailTrace_1661539
  have hstable : (prefixWord ++ tailWord_1661539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661539).length < 2 ^ (prefixWord ++ tailWord_1661539).sum := by decide
  have hdescent : baseEnd_1661539 < baseStart_1661539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661546 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_1661546 : Nat := 118140960795 + 1661546 * 2 ^ 59
def prefixEnd_1661546 : Nat := 4983230072969 + 3 ^ 40 * 1661546 * 2
def baseEnd_1661546 : Nat := 853171727555461427333695

theorem tailTrace_1661546 : CollatzResearch.WordTrace tailWord_1661546 prefixEnd_1661546 853171727555461427333695 := by
  unfold tailWord_1661546
  simp only [CollatzResearch.WordTrace]
  refine ⟨15150390309627521577467123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40401040825673390873245661 15150390309627521577467123)
  ·
    refine ⟨22725585464441282366200685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15150390309627521577467123 22725585464441282366200685)
    ·
      refine ⟨8522094549165480887325257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22725585464441282366200685 8522094549165480887325257)
      ·
        refine ⟨6391570911874110665493943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8522094549165480887325257 6391570911874110665493943)
        ·
          refine ⟨9587356367811165998240915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6391570911874110665493943 9587356367811165998240915)
          ·
            refine ⟨14381034551716748997361373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9587356367811165998240915 14381034551716748997361373)
            ·
              refine ⟨5392887956893780874010515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14381034551716748997361373 5392887956893780874010515)
              ·
                refine ⟨8089331935340671311015773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5392887956893780874010515 8089331935340671311015773)
                ·
                  refine ⟨3033499475752751741630915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8089331935340671311015773 3033499475752751741630915)
                  ·
                    refine ⟨4550249213629127612446373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3033499475752751741630915 4550249213629127612446373)
                    ·
                      refine ⟨853171727555461427333695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4550249213629127612446373 853171727555461427333695)
                      ·
                        rfl

theorem cell23_1661546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_1661546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661546 prefixEnd_1661546 := by exact prefixLift 1661546
  have htrace : WordTrace (prefixWord ++ tailWord_1661546) baseStart_1661546 baseEnd_1661546 := by
    simpa [prefixWord, tailWord_1661546, baseEnd_1661546] using wordTrace_append hprefix tailTrace_1661546
  have hstable : (prefixWord ++ tailWord_1661546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661546).length < 2 ^ (prefixWord ++ tailWord_1661546).sum := by decide
  have hdescent : baseEnd_1661546 < baseStart_1661546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661550 : List Nat := [4, 1, 2, 2, 2, 2, 2, 1, 2, 3, 2]
def baseStart_1661550 : Nat := 118140960795 + 1661550 * 2 ^ 59
def prefixEnd_1661550 : Nat := 4983230072969 + 3 ^ 40 * 1661550 * 2
def baseEnd_1661550 : Nat := 853173781478079411683677

theorem tailTrace_1661550 : CollatzResearch.WordTrace tailWord_1661550 prefixEnd_1661550 853173781478079411683677 := by
  unfold tailWord_1661550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7575213391311949374126763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40401138086997063328676069 7575213391311949374126763)
  ·
    refine ⟨11362820086967924061190145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7575213391311949374126763 11362820086967924061190145)
    ·
      refine ⟨8522115065225943045892609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11362820086967924061190145 8522115065225943045892609)
      ·
        refine ⟨6391586298919457284419457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8522115065225943045892609 6391586298919457284419457)
        ·
          refine ⟨4793689724189592963314593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6391586298919457284419457 4793689724189592963314593)
          ·
            refine ⟨3595267293142194722485945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4793689724189592963314593 3595267293142194722485945)
            ·
              refine ⟨2696450469856646041864459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3595267293142194722485945 2696450469856646041864459)
              ·
                refine ⟨4044675704784969062796689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2696450469856646041864459 4044675704784969062796689)
                ·
                  refine ⟨3033506778588726797097517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4044675704784969062796689 3033506778588726797097517)
                  ·
                    refine ⟨1137565041970772548911569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3033506778588726797097517 1137565041970772548911569)
                    ·
                      refine ⟨853173781478079411683677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1137565041970772548911569 853173781478079411683677)
                      ·
                        rfl

theorem cell23_1661550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_1661550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661550 prefixEnd_1661550 := by exact prefixLift 1661550
  have htrace : WordTrace (prefixWord ++ tailWord_1661550) baseStart_1661550 baseEnd_1661550 := by
    simpa [prefixWord, tailWord_1661550, baseEnd_1661550] using wordTrace_append hprefix tailTrace_1661550
  have hstable : (prefixWord ++ tailWord_1661550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661550).length < 2 ^ (prefixWord ++ tailWord_1661550).sum := by decide
  have hdescent : baseEnd_1661550 < baseStart_1661550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661559 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 4]
def baseStart_1661559 : Nat := 118140960795 + 1661559 * 2 ^ 59
def prefixEnd_1661559 : Nat := 4983230072969 + 3 ^ 40 * 1661559 * 2
def baseEnd_1661559 : Nat := 853178402803969876471135

theorem tailTrace_1661559 : CollatzResearch.WordTrace tailWord_1661559 prefixEnd_1661559 853178402803969876471135 := by
  unfold tailWord_1661559
  simp only [CollatzResearch.WordTrace]
  refine ⟨60602035387462989530091731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40401356924975326353394487 60602035387462989530091731)
  ·
    refine ⟨90903053081194484295137597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60602035387462989530091731 90903053081194484295137597)
    ·
      refine ⟨34088644905447931610676599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90903053081194484295137597 34088644905447931610676599)
      ·
        refine ⟨51132967358171897416014899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34088644905447931610676599 51132967358171897416014899)
        ·
          refine ⟨76699451037257846124022349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51132967358171897416014899 76699451037257846124022349)
          ·
            refine ⟨28762294138971692296508381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76699451037257846124022349 28762294138971692296508381)
            ·
              refine ⟨10785860302114384611190643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28762294138971692296508381 10785860302114384611190643)
              ·
                refine ⟨16178790453171576916785965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10785860302114384611190643 16178790453171576916785965)
                ·
                  refine ⟨6067046419939341343794737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16178790453171576916785965 6067046419939341343794737)
                  ·
                    refine ⟨4550284814954506007846053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6067046419939341343794737 4550284814954506007846053)
                    ·
                      refine ⟨853178402803969876471135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4550284814954506007846053 853178402803969876471135)
                      ·
                        rfl

theorem cell23_1661559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_1661559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661559 prefixEnd_1661559 := by exact prefixLift 1661559
  have htrace : WordTrace (prefixWord ++ tailWord_1661559) baseStart_1661559 baseEnd_1661559 := by
    simpa [prefixWord, tailWord_1661559, baseEnd_1661559] using wordTrace_append hprefix tailTrace_1661559
  have hstable : (prefixWord ++ tailWord_1661559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661559).length < 2 ^ (prefixWord ++ tailWord_1661559).sum := by decide
  have hdescent : baseEnd_1661559 < baseStart_1661559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661573 : List Nat := [1, 3, 1, 1, 4, 3, 2, 2, 2, 4]
def baseStart_1661573 : Nat := 118140960795 + 1661573 * 2 ^ 59
def prefixEnd_1661573 : Nat := 4983230072969 + 3 ^ 40 * 1661573 * 2
def baseEnd_1661573 : Nat := 284395197177710940565357

theorem tailTrace_1661573 : CollatzResearch.WordTrace tailWord_1661573 prefixEnd_1661573 284395197177710940565357 := by
  unfold tailWord_1661573
  simp only [CollatzResearch.WordTrace]
  refine ⟨60602546009412269921101373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40401697339608179947400915 60602546009412269921101373)
  ·
    refine ⟨22725954753529601220413015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60602546009412269921101373 22725954753529601220413015)
    ·
      refine ⟨34088932130294401830619523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22725954753529601220413015 34088932130294401830619523)
      ·
        refine ⟨51133398195441602745929285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34088932130294401830619523 51133398195441602745929285)
        ·
          refine ⟨9587512161645300514861741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51133398195441602745929285 9587512161645300514861741)
          ·
            refine ⟨3595317060616987693073153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9587512161645300514861741 3595317060616987693073153)
            ·
              refine ⟨2696487795462740769804865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3595317060616987693073153 2696487795462740769804865)
              ·
                refine ⟨2022365846597055577353649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2696487795462740769804865 2022365846597055577353649)
                ·
                  refine ⟨1516774384947791683015237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2022365846597055577353649 1516774384947791683015237)
                  ·
                    refine ⟨284395197177710940565357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1516774384947791683015237 284395197177710940565357)
                    ·
                      rfl

theorem cell23_1661573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_1661573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661573 prefixEnd_1661573 := by exact prefixLift 1661573
  have htrace : WordTrace (prefixWord ++ tailWord_1661573) baseStart_1661573 baseEnd_1661573 := by
    simpa [prefixWord, tailWord_1661573, baseEnd_1661573] using wordTrace_append hprefix tailTrace_1661573
  have hstable : (prefixWord ++ tailWord_1661573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661573).length < 2 ^ (prefixWord ++ tailWord_1661573).sum := by decide
  have hdescent : baseEnd_1661573 < baseStart_1661573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661586 : List Nat := [3, 2, 3, 1, 2, 1, 3, 8]
def baseStart_1661586 : Nat := 118140960795 + 1661586 * 2 ^ 59
def prefixEnd_1661586 : Nat := 4983230072969 + 3 ^ 40 * 1661586 * 2
def baseEnd_1661586 : Nat := 31599713584505232253093

theorem tailTrace_1661586 : CollatzResearch.WordTrace tailWord_1661586 prefixEnd_1661586 31599713584505232253093 := by
  unfold tailWord_1661586
  simp only [CollatzResearch.WordTrace]
  refine ⟨15150755039591293285331153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40402013438910115427549741 15150755039591293285331153)
  ·
    refine ⟨11363066279693469963998365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15150755039591293285331153 11363066279693469963998365)
    ·
      refine ⟨4261149854885051236499387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11363066279693469963998365 4261149854885051236499387)
      ·
        refine ⟨6391724782327576854749081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4261149854885051236499387 6391724782327576854749081)
        ·
          refine ⟨4793793586745682641061811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6391724782327576854749081 4793793586745682641061811)
          ·
            refine ⟨7190690380118523961592717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4793793586745682641061811 7190690380118523961592717)
            ·
              refine ⟨2696508892544446485597269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7190690380118523961592717 2696508892544446485597269)
              ·
                refine ⟨31599713584505232253093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2696508892544446485597269 31599713584505232253093)
                ·
                  rfl

theorem cell23_1661586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 8].length) (baseStart_1661586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661586 prefixEnd_1661586 := by exact prefixLift 1661586
  have htrace : WordTrace (prefixWord ++ tailWord_1661586) baseStart_1661586 baseEnd_1661586 := by
    simpa [prefixWord, tailWord_1661586, baseEnd_1661586] using wordTrace_append hprefix tailTrace_1661586
  have hstable : (prefixWord ++ tailWord_1661586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661586).length < 2 ^ (prefixWord ++ tailWord_1661586).sum := by decide
  have hdescent : baseEnd_1661586 < baseStart_1661586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661613 : List Nat := [1, 5, 2, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_1661613 : Nat := 118140960795 + 1661613 * 2 ^ 59
def prefixEnd_1661613 : Nat := 4983230072969 + 3 ^ 40 * 1661613 * 2
def baseEnd_1661613 : Nat := 853206130759312665195887

theorem tailTrace_1661613 : CollatzResearch.WordTrace tailWord_1661613 prefixEnd_1661613 853206130759312665195887 := by
  unfold tailWord_1661613
  simp only [CollatzResearch.WordTrace]
  refine ⟨60604004929267356752557493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40402669952844904501704995 60604004929267356752557493)
  ·
    refine ⟨5681625462118814695552265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60604004929267356752557493 5681625462118814695552265)
    ·
      refine ⟨4261219096589111021664199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5681625462118814695552265 4261219096589111021664199)
      ·
        refine ⟨6391828644883666532496299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4261219096589111021664199 6391828644883666532496299)
        ·
          refine ⟨9587742967325499798744449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6391828644883666532496299 9587742967325499798744449)
          ·
            refine ⟨7190807225494124849058337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9587742967325499798744449 7190807225494124849058337)
            ·
              refine ⟨5393105419120593636793753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7190807225494124849058337 5393105419120593636793753)
              ·
                refine ⟨4044829064340445227595315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5393105419120593636793753 4044829064340445227595315)
                ·
                  refine ⟨6067243596510667841392973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4044829064340445227595315 6067243596510667841392973)
                  ·
                    refine ⟨2275216348691500440522365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6067243596510667841392973 2275216348691500440522365)
                    ·
                      refine ⟨853206130759312665195887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2275216348691500440522365 853206130759312665195887)
                      ·
                        rfl

theorem cell23_1661613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_1661613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661613 prefixEnd_1661613 := by exact prefixLift 1661613
  have htrace : WordTrace (prefixWord ++ tailWord_1661613) baseStart_1661613 baseEnd_1661613 := by
    simpa [prefixWord, tailWord_1661613, baseEnd_1661613] using wordTrace_append hprefix tailTrace_1661613
  have hstable : (prefixWord ++ tailWord_1661613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661613).length < 2 ^ (prefixWord ++ tailWord_1661613).sum := by decide
  have hdescent : baseEnd_1661613 < baseStart_1661613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661614 : List Nat := [4, 1, 4, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_1661614 : Nat := 118140960795 + 1661614 * 2 ^ 59
def prefixEnd_1661614 : Nat := 4983230072969 + 3 ^ 40 * 1661614 * 2
def baseEnd_1661614 : Nat := 853206644239967161283383

theorem tailTrace_1661614 : CollatzResearch.WordTrace tailWord_1661614 prefixEnd_1661614 853206644239967161283383 := by
  unfold tailWord_1661614
  simp only [CollatzResearch.WordTrace]
  refine ⟨7575505175282966740417987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40402694268175822615562597 7575505175282966740417987)
  ·
    refine ⟨11363257762924450110626981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7575505175282966740417987 11363257762924450110626981)
    ·
      refine ⟨2130610830548334395742559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11363257762924450110626981 2130610830548334395742559)
      ·
        refine ⟨3195916245822501593613839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2130610830548334395742559 3195916245822501593613839)
        ·
          refine ⟨4793874368733752390420759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3195916245822501593613839 4793874368733752390420759)
          ·
            refine ⟨7190811553100628585631139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4793874368733752390420759 7190811553100628585631139)
            ·
              refine ⟨10786217329650942878446709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7190811553100628585631139 10786217329650942878446709)
              ·
                refine ⟨1011207874654775894854379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10786217329650942878446709 1011207874654775894854379)
                ·
                  refine ⟨1516811811982163842281569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011207874654775894854379 1516811811982163842281569)
                  ·
                    refine ⟨1137608858986622881711177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1516811811982163842281569 1137608858986622881711177)
                    ·
                      refine ⟨853206644239967161283383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1137608858986622881711177 853206644239967161283383)
                      ·
                        rfl

theorem cell23_1661614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_1661614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661614 prefixEnd_1661614 := by exact prefixLift 1661614
  have htrace : WordTrace (prefixWord ++ tailWord_1661614) baseStart_1661614 baseEnd_1661614 := by
    simpa [prefixWord, tailWord_1661614, baseEnd_1661614] using wordTrace_append hprefix tailTrace_1661614
  have hstable : (prefixWord ++ tailWord_1661614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661614).length < 2 ^ (prefixWord ++ tailWord_1661614).sum := by decide
  have hdescent : baseEnd_1661614 < baseStart_1661614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661639 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_1661639 : Nat := 118140960795 + 1661639 * 2 ^ 59
def prefixEnd_1661639 : Nat := 4983230072969 + 3 ^ 40 * 1661639 * 2
def baseEnd_1661639 : Nat := 853219481256329563470767

theorem tailTrace_1661639 : CollatzResearch.WordTrace tailWord_1661639 prefixEnd_1661639 853219481256329563470767 := by
  unfold tailWord_1661639
  simp only [CollatzResearch.WordTrace]
  refine ⟨60604953227173163193003971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40403302151448775462002647 60604953227173163193003971)
  ·
    refine ⟨90907429840759744789505957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60604953227173163193003971 90907429840759744789505957)
    ·
      refine ⟨17045143095142452148032367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90907429840759744789505957 17045143095142452148032367)
      ·
        refine ⟨25567714642713678222048551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17045143095142452148032367 25567714642713678222048551)
        ·
          refine ⟨38351571964070517333072827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25567714642713678222048551 38351571964070517333072827)
          ·
            refine ⟨57527357946105775999609241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38351571964070517333072827 57527357946105775999609241)
            ·
              refine ⟨43145518459579331999706931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57527357946105775999609241 43145518459579331999706931)
              ·
                refine ⟨64718277689368997999560397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43145518459579331999706931 64718277689368997999560397)
                ·
                  refine ⟨24269354133513374249835149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64718277689368997999560397 24269354133513374249835149)
                  ·
                    refine ⟨9101007800067515343688181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24269354133513374249835149 9101007800067515343688181)
                    ·
                      refine ⟨853219481256329563470767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9101007800067515343688181 853219481256329563470767)
                      ·
                        rfl

theorem cell23_1661639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_1661639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661639 prefixEnd_1661639 := by exact prefixLift 1661639
  have htrace : WordTrace (prefixWord ++ tailWord_1661639) baseStart_1661639 baseEnd_1661639 := by
    simpa [prefixWord, tailWord_1661639, baseEnd_1661639] using wordTrace_append hprefix tailTrace_1661639
  have hstable : (prefixWord ++ tailWord_1661639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661639).length < 2 ^ (prefixWord ++ tailWord_1661639).sum := by decide
  have hdescent : baseEnd_1661639 < baseStart_1661639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661646 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 2, 6]
def baseStart_1661646 : Nat := 118140960795 + 1661646 * 2 ^ 59
def prefixEnd_1661646 : Nat := 4983230072969 + 3 ^ 40 * 1661646 * 2
def baseEnd_1661646 : Nat := 284407691873637012027745

theorem tailTrace_1661646 : CollatzResearch.WordTrace tailWord_1661646 prefixEnd_1661646 284407691873637012027745 := by
  unfold tailWord_1661646
  simp only [CollatzResearch.WordTrace]
  refine ⟨7575651067268475423563599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40403472358765202259005861 7575651067268475423563599)
  ·
    refine ⟨11363476600902713135345399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7575651067268475423563599 11363476600902713135345399)
    ·
      refine ⟨17045214901354069703018099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11363476600902713135345399 17045214901354069703018099)
      ·
        refine ⟨25567822352031104554527149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17045214901354069703018099 25567822352031104554527149)
        ·
          refine ⟨9587933382011664207947681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25567822352031104554527149 9587933382011664207947681)
          ·
            refine ⟨7190950036508748155960761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9587933382011664207947681 7190950036508748155960761)
            ·
              refine ⟨5393212527381561116970571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7190950036508748155960761 5393212527381561116970571)
              ·
                refine ⟨8089818791072341675455857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5393212527381561116970571 8089818791072341675455857)
                ·
                  refine ⟨6067364093304256256591893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8089818791072341675455857 6067364093304256256591893)
                  ·
                    refine ⟨284407691873637012027745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6067364093304256256591893 284407691873637012027745)
                    ·
                      rfl

theorem cell23_1661646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_1661646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661646 prefixEnd_1661646 := by exact prefixLift 1661646
  have htrace : WordTrace (prefixWord ++ tailWord_1661646) baseStart_1661646 baseEnd_1661646 := by
    simpa [prefixWord, tailWord_1661646, baseEnd_1661646] using wordTrace_append hprefix tailTrace_1661646
  have hstable : (prefixWord ++ tailWord_1661646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661646).length < 2 ^ (prefixWord ++ tailWord_1661646).sum := by decide
  have hdescent : baseEnd_1661646 < baseStart_1661646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661686 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_1661686 : Nat := 118140960795 + 1661686 * 2 ^ 59
def prefixEnd_1661686 : Nat := 4983230072969 + 3 ^ 40 * 1661686 * 2
def baseEnd_1661686 : Nat := 853243614847090879583051

theorem tailTrace_1661686 : CollatzResearch.WordTrace tailWord_1661686 prefixEnd_1661686 853243614847090879583051 := by
  unfold tailWord_1661686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3787916716125180638747807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40404444972001926813309941 3787916716125180638747807)
  ·
    refine ⟨5681875074187770958121711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3787916716125180638747807 5681875074187770958121711)
    ·
      refine ⟨8522812611281656437182567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5681875074187770958121711 8522812611281656437182567)
      ·
        refine ⟨12784218916922484655773851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8522812611281656437182567 12784218916922484655773851)
        ·
          refine ⟨19176328375383726983660777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12784218916922484655773851 19176328375383726983660777)
          ·
            refine ⟨14382246281537795237745583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19176328375383726983660777 14382246281537795237745583)
            ·
              refine ⟨21573369422306692856618375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14382246281537795237745583 21573369422306692856618375)
              ·
                refine ⟨32360054133460039284927563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21573369422306692856618375 32360054133460039284927563)
                ·
                  refine ⟨48540081200190058927391345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32360054133460039284927563 48540081200190058927391345)
                  ·
                    refine ⟨36405060900142544195543509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48540081200190058927391345 36405060900142544195543509)
                    ·
                      refine ⟨853243614847090879583051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36405060900142544195543509 853243614847090879583051)
                      ·
                        rfl

theorem cell23_1661686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_1661686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661686 prefixEnd_1661686 := by exact prefixLift 1661686
  have htrace : WordTrace (prefixWord ++ tailWord_1661686) baseStart_1661686 baseEnd_1661686 := by
    simpa [prefixWord, tailWord_1661686, baseEnd_1661686] using wordTrace_append hprefix tailTrace_1661686
  have hstable : (prefixWord ++ tailWord_1661686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661686).length < 2 ^ (prefixWord ++ tailWord_1661686).sum := by decide
  have hdescent : baseEnd_1661686 < baseStart_1661686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661704 : List Nat := [2, 1, 3, 2, 2, 4, 2, 1, 2, 2, 2]
def baseStart_1661704 : Nat := 118140960795 + 1661704 * 2 ^ 59
def prefixEnd_1661704 : Nat := 4983230072969 + 3 ^ 40 * 1661704 * 2
def baseEnd_1661704 : Nat := 853252857498871809157969

theorem tailTrace_1661704 : CollatzResearch.WordTrace tailWord_1661704 prefixEnd_1661704 853252857498871809157969 := by
  unfold tailWord_1661704
  simp only [CollatzResearch.WordTrace]
  refine ⟨30303661985968839647060083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40404882647958452862746777 30303661985968839647060083)
  ·
    refine ⟨45455492978953259470590125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30303661985968839647060083 45455492978953259470590125)
    ·
      refine ⟨17045809867107472301471297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45455492978953259470590125 17045809867107472301471297)
      ·
        refine ⟨12784357400330604226103473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17045809867107472301471297 12784357400330604226103473)
        ·
          refine ⟨9588268050247953169577605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12784357400330604226103473 9588268050247953169577605)
          ·
            refine ⟨1797800259421491219295801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9588268050247953169577605 1797800259421491219295801)
            ·
              refine ⟨1348350194566118414471851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1797800259421491219295801 1348350194566118414471851)
              ·
                refine ⟨2022525291849177621707777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1348350194566118414471851 2022525291849177621707777)
                ·
                  refine ⟨1516893968886883216280833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2022525291849177621707777 1516893968886883216280833)
                  ·
                    refine ⟨1137670476665162412210625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1516893968886883216280833 1137670476665162412210625)
                    ·
                      refine ⟨853252857498871809157969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1137670476665162412210625 853252857498871809157969)
                      ·
                        rfl

theorem cell23_1661704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_1661704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661704 prefixEnd_1661704 := by exact prefixLift 1661704
  have htrace : WordTrace (prefixWord ++ tailWord_1661704) baseStart_1661704 baseEnd_1661704 := by
    simpa [prefixWord, tailWord_1661704, baseEnd_1661704] using wordTrace_append hprefix tailTrace_1661704
  have hstable : (prefixWord ++ tailWord_1661704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661704).length < 2 ^ (prefixWord ++ tailWord_1661704).sum := by decide
  have hdescent : baseEnd_1661704 < baseStart_1661704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661706 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 4, 5]
def baseStart_1661706 : Nat := 118140960795 + 1661706 * 2 ^ 59
def prefixEnd_1661706 : Nat := 4983230072969 + 3 ^ 40 * 1661706 * 2
def baseEnd_1661706 : Nat := 284417961486726933777653

theorem tailTrace_1661706 : CollatzResearch.WordTrace tailWord_1661706 prefixEnd_1661706 284417961486726933777653 := by
  unfold tailWord_1661706
  simp only [CollatzResearch.WordTrace]
  refine ⟨15151849229482608408923243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40404931278620289090461981 15151849229482608408923243)
  ·
    refine ⟨22727773844223912613384865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15151849229482608408923243 22727773844223912613384865)
    ·
      refine ⟨17045830383167934460038649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22727773844223912613384865 17045830383167934460038649)
      ·
        refine ⟨12784372787375950845028987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17045830383167934460038649 12784372787375950845028987)
        ·
          refine ⟨19176559181063926267543481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12784372787375950845028987 19176559181063926267543481)
          ·
            refine ⟨14382419385797944700657611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19176559181063926267543481 14382419385797944700657611)
            ·
              refine ⟨21573629078696917050986417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14382419385797944700657611 21573629078696917050986417)
              ·
                refine ⟨16180221809022687788239813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21573629078696917050986417 16180221809022687788239813)
                ·
                  refine ⟨3033791589191753960294965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16180221809022687788239813 3033791589191753960294965)
                  ·
                    refine ⟨284417961486726933777653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3033791589191753960294965 284417961486726933777653)
                    ·
                      rfl

theorem cell23_1661706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_1661706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661706 prefixEnd_1661706 := by exact prefixLift 1661706
  have htrace : WordTrace (prefixWord ++ tailWord_1661706) baseStart_1661706 baseEnd_1661706 := by
    simpa [prefixWord, tailWord_1661706, baseEnd_1661706] using wordTrace_append hprefix tailTrace_1661706
  have hstable : (prefixWord ++ tailWord_1661706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661706).length < 2 ^ (prefixWord ++ tailWord_1661706).sum := by decide
  have hdescent : baseEnd_1661706 < baseStart_1661706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661746 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_1661746 : Nat := 118140960795 + 1661746 * 2 ^ 59
def prefixEnd_1661746 : Nat := 4983230072969 + 3 ^ 40 * 1661746 * 2
def baseEnd_1661746 : Nat := 853274423686360644832775

theorem tailTrace_1661746 : CollatzResearch.WordTrace tailWord_1661746 prefixEnd_1661746 853274423686360644832775 := by
  unfold tailWord_1661746
  simp only [CollatzResearch.WordTrace]
  refine ⟨15152213959446380116787273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40405903891857013644766061 15152213959446380116787273)
  ·
    refine ⟨11364160469584785087590455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15152213959446380116787273 11364160469584785087590455)
    ·
      refine ⟨17046240704377177631385683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11364160469584785087590455 17046240704377177631385683)
      ·
        refine ⟨25569361056565766447078525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17046240704377177631385683 25569361056565766447078525)
        ·
          refine ⟨9588510396212162417654447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25569361056565766447078525 9588510396212162417654447)
          ·
            refine ⟨14382765594318243626481671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9588510396212162417654447 14382765594318243626481671)
            ·
              refine ⟨21574148391477365439722507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14382765594318243626481671 21574148391477365439722507)
              ·
                refine ⟨32361222587216048159583761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21574148391477365439722507 32361222587216048159583761)
                ·
                  refine ⟨24270916940412036119687821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32361222587216048159583761 24270916940412036119687821)
                  ·
                    refine ⟨9101593852654513544882933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24270916940412036119687821 9101593852654513544882933)
                    ·
                      refine ⟨853274423686360644832775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9101593852654513544882933 853274423686360644832775)
                      ·
                        rfl

theorem cell23_1661746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_1661746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661746 prefixEnd_1661746 := by exact prefixLift 1661746
  have htrace : WordTrace (prefixWord ++ tailWord_1661746) baseStart_1661746 baseEnd_1661746 := by
    simpa [prefixWord, tailWord_1661746, baseEnd_1661746] using wordTrace_append hprefix tailTrace_1661746
  have hstable : (prefixWord ++ tailWord_1661746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661746).length < 2 ^ (prefixWord ++ tailWord_1661746).sum := by decide
  have hdescent : baseEnd_1661746 < baseStart_1661746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661756 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_1661756 : Nat := 118140960795 + 1661756 * 2 ^ 59
def prefixEnd_1661756 : Nat := 4983230072969 + 3 ^ 40 * 1661756 * 2
def baseEnd_1661756 : Nat := 853279558492905605707729

theorem tailTrace_1661756 : CollatzResearch.WordTrace tailWord_1661756 prefixEnd_1661756 853279558492905605707729 := by
  unfold tailWord_1661756
  simp only [CollatzResearch.WordTrace]
  refine ⟨30304610283874646087506561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40406147045166194783342081 30304610283874646087506561)
  ·
    refine ⟨22728457712905984565629921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30304610283874646087506561 22728457712905984565629921)
    ·
      refine ⟨17046343284679488424222441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22728457712905984565629921 17046343284679488424222441)
      ·
        refine ⟨12784757463509616318166831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17046343284679488424222441 12784757463509616318166831)
        ·
          refine ⟨19177136195264424477250247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12784757463509616318166831 19177136195264424477250247)
          ·
            refine ⟨28765704292896636715875371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19177136195264424477250247 28765704292896636715875371)
            ·
              refine ⟨43148556439344955073813057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28765704292896636715875371 43148556439344955073813057)
              ·
                refine ⟨32361417329508716305359793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43148556439344955073813057 32361417329508716305359793)
                ·
                  refine ⟨24271062997131537229019845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32361417329508716305359793 24271062997131537229019845)
                  ·
                    refine ⟨4550824311962163230441221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24271062997131537229019845 4550824311962163230441221)
                    ·
                      refine ⟨853279558492905605707729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4550824311962163230441221 853279558492905605707729)
                      ·
                        rfl

theorem cell23_1661756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_1661756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661756 prefixEnd_1661756 := by exact prefixLift 1661756
  have htrace : WordTrace (prefixWord ++ tailWord_1661756) baseStart_1661756 baseEnd_1661756 := by
    simpa [prefixWord, tailWord_1661756, baseEnd_1661756] using wordTrace_append hprefix tailTrace_1661756
  have hstable : (prefixWord ++ tailWord_1661756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661756).length < 2 ^ (prefixWord ++ tailWord_1661756).sum := by decide
  have hdescent : baseEnd_1661756 < baseStart_1661756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661777 : List Nat := [1, 2, 2, 1, 7, 1, 1, 1, 2, 1, 4]
def baseStart_1661777 : Nat := 118140960795 + 1661777 * 2 ^ 59
def prefixEnd_1661777 : Nat := 4983230072969 + 3 ^ 40 * 1661777 * 2
def baseEnd_1661777 : Nat := 853290341586650023545133

theorem tailTrace_1661777 : CollatzResearch.WordTrace tailWord_1661777 prefixEnd_1661777 853290341586650023545133 := by
  unfold tailWord_1661777
  simp only [CollatzResearch.WordTrace]
  refine ⟨60609986500673212761527585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40406657667115475174351723 60609986500673212761527585)
  ·
    refine ⟨45457489875504909571145689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60609986500673212761527585 45457489875504909571145689)
    ·
      refine ⟨34093117406628682178359267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45457489875504909571145689 34093117406628682178359267)
      ·
        refine ⟨51139676109943023267538901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34093117406628682178359267 51139676109943023267538901)
        ·
          refine ⟨1198586158826789607832943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 51139676109943023267538901 1198586158826789607832943)
          ·
            refine ⟨1797879238240184411749415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198586158826789607832943 1797879238240184411749415)
            ·
              refine ⟨2696818857360276617624123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1797879238240184411749415 2696818857360276617624123)
              ·
                refine ⟨4045228286040414926436185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2696818857360276617624123 4045228286040414926436185)
                ·
                  refine ⟨3033921214530311194827139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4045228286040414926436185 3033921214530311194827139)
                  ·
                    refine ⟨4550881821795466792240709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3033921214530311194827139 4550881821795466792240709)
                    ·
                      refine ⟨853290341586650023545133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4550881821795466792240709 853290341586650023545133)
                      ·
                        rfl

theorem cell23_1661777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 2, 1, 4].length) (baseStart_1661777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661777 prefixEnd_1661777 := by exact prefixLift 1661777
  have htrace : WordTrace (prefixWord ++ tailWord_1661777) baseStart_1661777 baseEnd_1661777 := by
    simpa [prefixWord, tailWord_1661777, baseEnd_1661777] using wordTrace_append hprefix tailTrace_1661777
  have hstable : (prefixWord ++ tailWord_1661777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661777).length < 2 ^ (prefixWord ++ tailWord_1661777).sum := by decide
  have hdescent : baseEnd_1661777 < baseStart_1661777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661780 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_1661780 : Nat := 118140960795 + 1661780 * 2 ^ 59
def prefixEnd_1661780 : Nat := 4983230072969 + 3 ^ 40 * 1661780 * 2
def baseEnd_1661780 : Nat := 853291882028613511807619

theorem tailTrace_1661780 : CollatzResearch.WordTrace tailWord_1661780 prefixEnd_1661780 853291882028613511807619 := by
  unfold tailWord_1661780
  simp only [CollatzResearch.WordTrace]
  refine ⟨30305047959831172136943397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40406730613108229515924529 30305047959831172136943397)
  ·
    refine ⟨5682196492468344775676887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30305047959831172136943397 5682196492468344775676887)
    ·
      refine ⟨8523294738702517163515331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5682196492468344775676887 8523294738702517163515331)
      ·
        refine ⟨12784942108053775745272997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8523294738702517163515331 12784942108053775745272997)
        ·
          refine ⟨2397176645260082952238687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12784942108053775745272997 2397176645260082952238687)
          ·
            refine ⟨3595764967890124428358031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2397176645260082952238687 3595764967890124428358031)
            ·
              refine ⟨5393647451835186642537047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3595764967890124428358031 5393647451835186642537047)
              ·
                refine ⟨8090471177752779963805571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5393647451835186642537047 8090471177752779963805571)
                ·
                  refine ⟨12135706766629169945708357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8090471177752779963805571 12135706766629169945708357)
                  ·
                    refine ⟨2275445018742969364820317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12135706766629169945708357 2275445018742969364820317)
                    ·
                      refine ⟨853291882028613511807619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2275445018742969364820317 853291882028613511807619)
                      ·
                        rfl

theorem cell23_1661780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_1661780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661780 prefixEnd_1661780 := by exact prefixLift 1661780
  have htrace : WordTrace (prefixWord ++ tailWord_1661780) baseStart_1661780 baseEnd_1661780 := by
    simpa [prefixWord, tailWord_1661780, baseEnd_1661780] using wordTrace_append hprefix tailTrace_1661780
  have hstable : (prefixWord ++ tailWord_1661780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661780).length < 2 ^ (prefixWord ++ tailWord_1661780).sum := by decide
  have hdescent : baseEnd_1661780 < baseStart_1661780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661800 : List Nat := [2, 1, 4, 2, 1, 4, 1, 2, 6]
def baseStart_1661800 : Nat := 118140960795 + 1661800 * 2 ^ 59
def prefixEnd_1661800 : Nat := 4983230072969 + 3 ^ 40 * 1661800 * 2
def baseEnd_1661800 : Nat := 94811350182411492617503

theorem tailTrace_1661800 : CollatzResearch.WordTrace tailWord_1661800 prefixEnd_1661800 94811350182411492617503 := by
  unfold tailWord_1661800
  simp only [CollatzResearch.WordTrace]
  refine ⟨30305412689794943844807427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40407216919726591793076569 30305412689794943844807427)
  ·
    refine ⟨45458119034692415767211141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30305412689794943844807427 45458119034692415767211141)
    ·
      refine ⟨8523397319004827956352089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45458119034692415767211141 8523397319004827956352089)
      ·
        refine ⟨6392547989253620967264067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8523397319004827956352089 6392547989253620967264067)
        ·
          refine ⟨9588821983880431450896101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6392547989253620967264067 9588821983880431450896101)
          ·
            refine ⟨1797904121977580897043019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9588821983880431450896101 1797904121977580897043019)
            ·
              refine ⟨2696856182966371345564529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1797904121977580897043019 2696856182966371345564529)
              ·
                refine ⟨2022642137224778509173397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2696856182966371345564529 2022642137224778509173397)
                ·
                  refine ⟨94811350182411492617503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2022642137224778509173397 94811350182411492617503)
                  ·
                    rfl

theorem cell23_1661800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 6].length) (baseStart_1661800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661800 prefixEnd_1661800 := by exact prefixLift 1661800
  have htrace : WordTrace (prefixWord ++ tailWord_1661800) baseStart_1661800 baseEnd_1661800 := by
    simpa [prefixWord, tailWord_1661800, baseEnd_1661800] using wordTrace_append hprefix tailTrace_1661800
  have hstable : (prefixWord ++ tailWord_1661800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661800).length < 2 ^ (prefixWord ++ tailWord_1661800).sum := by decide
  have hdescent : baseEnd_1661800 < baseStart_1661800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661810 : List Nat := [3, 2, 1, 2, 1, 1, 3, 3, 3, 1, 3]
def baseStart_1661810 : Nat := 118140960795 + 1661810 * 2 ^ 59
def prefixEnd_1661810 : Nat := 4983230072969 + 3 ^ 40 * 1661810 * 2
def baseEnd_1661810 : Nat := 853307286448248394432481

theorem tailTrace_1661810 : CollatzResearch.WordTrace tailWord_1661810 prefixEnd_1661810 853307286448248394432481 := by
  unfold tailWord_1661810
  simp only [CollatzResearch.WordTrace]
  refine ⟨15152797527388414849369721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40407460073035772931652589 15152797527388414849369721)
  ·
    refine ⟨11364598145541311137027291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15152797527388414849369721 11364598145541311137027291)
    ·
      refine ⟨17046897218311966705540937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11364598145541311137027291 17046897218311966705540937)
      ·
        refine ⟨12785172913733975029155703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17046897218311966705540937 12785172913733975029155703)
        ·
          refine ⟨19177759370600962543733555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12785172913733975029155703 19177759370600962543733555)
          ·
            refine ⟨28766639055901443815600333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19177759370600962543733555 28766639055901443815600333)
            ·
              refine ⟨10787489645963041430850125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28766639055901443815600333 10787489645963041430850125)
              ·
                refine ⟨4045308617236140536568797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10787489645963041430850125 4045308617236140536568797)
                ·
                  refine ⟨1516990731463552701213299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4045308617236140536568797 1516990731463552701213299)
                  ·
                    refine ⟨2275486097195329051819949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1516990731463552701213299 2275486097195329051819949)
                    ·
                      refine ⟨853307286448248394432481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2275486097195329051819949 853307286448248394432481)
                      ·
                        rfl

theorem cell23_1661810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_1661810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661810 prefixEnd_1661810 := by exact prefixLift 1661810
  have htrace : WordTrace (prefixWord ++ tailWord_1661810) baseStart_1661810 baseEnd_1661810 := by
    simpa [prefixWord, tailWord_1661810, baseEnd_1661810] using wordTrace_append hprefix tailTrace_1661810
  have hstable : (prefixWord ++ tailWord_1661810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661810).length < 2 ^ (prefixWord ++ tailWord_1661810).sum := by decide
  have hdescent : baseEnd_1661810 < baseStart_1661810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661816 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 2, 5, 4]
def baseStart_1661816 : Nat := 118140960795 + 1661816 * 2 ^ 59
def prefixEnd_1661816 : Nat := 4983230072969 + 3 ^ 40 * 1661816 * 2
def baseEnd_1661816 : Nat := 853310367332175370957453

theorem tailTrace_1661816 : CollatzResearch.WordTrace tailWord_1661816 prefixEnd_1661816 853310367332175370957453 := by
  unfold tailWord_1661816
  simp only [CollatzResearch.WordTrace]
  refine ⟨30305704473765961211098651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40407605965021281614798201 30305704473765961211098651)
  ·
    refine ⟨45458556710648941816647977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30305704473765961211098651 45458556710648941816647977)
    ·
      refine ⟨34093917532986706362485983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45458556710648941816647977 34093917532986706362485983)
      ·
        refine ⟨51140876299480059543728975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34093917532986706362485983 51140876299480059543728975)
        ·
          refine ⟨76711314449220089315593463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51140876299480059543728975 76711314449220089315593463)
          ·
            refine ⟨115066971673830133973390195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76711314449220089315593463 115066971673830133973390195)
            ·
              refine ⟨172600457510745200960085293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115066971673830133973390195 172600457510745200960085293)
              ·
                refine ⟨64725171566529450360031985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172600457510745200960085293 64725171566529450360031985)
                ·
                  refine ⟨48543878674897087770023989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64725171566529450360031985 48543878674897087770023989)
                  ·
                    refine ⟨4550988625771601978439749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48543878674897087770023989 4550988625771601978439749)
                    ·
                      refine ⟨853310367332175370957453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4550988625771601978439749 853310367332175370957453)
                      ·
                        rfl

theorem cell23_1661816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_1661816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661816 prefixEnd_1661816 := by exact prefixLift 1661816
  have htrace : WordTrace (prefixWord ++ tailWord_1661816) baseStart_1661816 baseEnd_1661816 := by
    simpa [prefixWord, tailWord_1661816, baseEnd_1661816] using wordTrace_append hprefix tailTrace_1661816
  have hstable : (prefixWord ++ tailWord_1661816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661816).length < 2 ^ (prefixWord ++ tailWord_1661816).sum := by decide
  have hdescent : baseEnd_1661816 < baseStart_1661816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661856 : List Nat := [2, 1, 1, 4, 1, 1, 13]
def baseStart_1661856 : Nat := 118140960795 + 1661856 * 2 ^ 59
def prefixEnd_1661856 : Nat := 4983230072969 + 3 ^ 40 * 1661856 * 2
def baseEnd_1661856 : Nat := 10534949463683397709349

theorem tailTrace_1661856 : CollatzResearch.WordTrace tailWord_1661856 prefixEnd_1661856 10534949463683397709349 := by
  unfold tailWord_1661856
  simp only [CollatzResearch.WordTrace]
  refine ⟨30306433933693504626826711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40408578578258006169102281 30306433933693504626826711)
  ·
    refine ⟨45459650900540256940240067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30306433933693504626826711 45459650900540256940240067)
    ·
      refine ⟨68189476350810385410360101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45459650900540256940240067 68189476350810385410360101)
      ·
        refine ⟨12785526815776947264442519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68189476350810385410360101 12785526815776947264442519)
        ·
          refine ⟨19178290223665420896663779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12785526815776947264442519 19178290223665420896663779)
          ·
            refine ⟨28767435335498131344995669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19178290223665420896663779 28767435335498131344995669)
            ·
              refine ⟨10534949463683397709349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 28767435335498131344995669 10534949463683397709349)
              ·
                rfl

theorem cell23_1661856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 13].length) (baseStart_1661856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661856 prefixEnd_1661856 := by exact prefixLift 1661856
  have htrace : WordTrace (prefixWord ++ tailWord_1661856) baseStart_1661856 baseEnd_1661856 := by
    simpa [prefixWord, tailWord_1661856, baseEnd_1661856] using wordTrace_append hprefix tailTrace_1661856
  have hstable : (prefixWord ++ tailWord_1661856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661856).length < 2 ^ (prefixWord ++ tailWord_1661856).sum := by decide
  have hdescent : baseEnd_1661856 < baseStart_1661856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661860 : List Nat := [2, 3, 1, 2, 1, 2, 2, 4, 2, 4]
def baseStart_1661860 : Nat := 118140960795 + 1661860 * 2 ^ 59
def prefixEnd_1661860 : Nat := 4983230072969 + 3 ^ 40 * 1661860 * 2
def baseEnd_1661860 : Nat := 284444320160324399602417

theorem tailTrace_1661860 : CollatzResearch.WordTrace tailWord_1661860 prefixEnd_1661860 284444320160324399602417 := by
  unfold tailWord_1661860
  simp only [CollatzResearch.WordTrace]
  refine ⟨30306506879686258968399517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40408675839581678624532689 30306506879686258968399517)
  ·
    refine ⟨11364940079882347113149819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30306506879686258968399517 11364940079882347113149819)
    ·
      refine ⟨17047410119823520669724729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11364940079882347113149819 17047410119823520669724729)
      ·
        refine ⟨12785557589867640502293547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17047410119823520669724729 12785557589867640502293547)
        ·
          refine ⟨19178336384801460753440321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12785557589867640502293547 19178336384801460753440321)
          ·
            refine ⟨14383752288601095565080241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19178336384801460753440321 14383752288601095565080241)
            ·
              refine ⟨10787814216450821673810181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14383752288601095565080241 10787814216450821673810181)
              ·
                refine ⟨2022715165584529063839409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10787814216450821673810181 2022715165584529063839409)
                ·
                  refine ⟨1517036374188396797879557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2022715165584529063839409 1517036374188396797879557)
                  ·
                    refine ⟨284444320160324399602417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1517036374188396797879557 284444320160324399602417)
                    ·
                      rfl

theorem cell23_1661860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_1661860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661860 prefixEnd_1661860 := by exact prefixLift 1661860
  have htrace : WordTrace (prefixWord ++ tailWord_1661860) baseStart_1661860 baseEnd_1661860 := by
    simpa [prefixWord, tailWord_1661860, baseEnd_1661860] using wordTrace_append hprefix tailTrace_1661860
  have hstable : (prefixWord ++ tailWord_1661860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661860).length < 2 ^ (prefixWord ++ tailWord_1661860).sum := by decide
  have hdescent : baseEnd_1661860 < baseStart_1661860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661900 : List Nat := [2, 2, 1, 4, 1, 1, 3, 2, 1, 3, 3]
def baseStart_1661900 : Nat := 118140960795 + 1661900 * 2 ^ 59
def prefixEnd_1661900 : Nat := 4983230072969 + 3 ^ 40 * 1661900 * 2
def baseEnd_1661900 : Nat := 853353499707153042307067

theorem tailTrace_1661900 : CollatzResearch.WordTrace tailWord_1661900 prefixEnd_1661900 853353499707153042307067 := by
  unfold tailWord_1661900
  simp only [CollatzResearch.WordTrace]
  refine ⟨30307236339613802384127577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40409648452818403178836769 30307236339613802384127577)
  ·
    refine ⟨22730427254710351788095683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30307236339613802384127577 22730427254710351788095683)
    ·
      refine ⟨34095640882065527682143525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22730427254710351788095683 34095640882065527682143525)
      ·
        refine ⟨6392932665387286440401911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34095640882065527682143525 6392932665387286440401911)
        ·
          refine ⟨9589398998080929660602867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6392932665387286440401911 9589398998080929660602867)
          ·
            refine ⟨14384098497121394490904301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9589398998080929660602867 14384098497121394490904301)
            ·
              refine ⟨5394036936420522934089113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14384098497121394490904301 5394036936420522934089113)
              ·
                refine ⟨4045527702315392200566835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5394036936420522934089113 4045527702315392200566835)
                ·
                  refine ⟨6068291553473088300850253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4045527702315392200566835 6068291553473088300850253)
                  ·
                    refine ⟨2275609332552408112818845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6068291553473088300850253 2275609332552408112818845)
                    ·
                      refine ⟨853353499707153042307067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2275609332552408112818845 853353499707153042307067)
                      ·
                        rfl

theorem cell23_1661900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_1661900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661900 prefixEnd_1661900 := by exact prefixLift 1661900
  have htrace : WordTrace (prefixWord ++ tailWord_1661900) baseStart_1661900 baseEnd_1661900 := by
    simpa [prefixWord, tailWord_1661900, baseEnd_1661900] using wordTrace_append hprefix tailTrace_1661900
  have hstable : (prefixWord ++ tailWord_1661900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661900).length < 2 ^ (prefixWord ++ tailWord_1661900).sum := by decide
  have hdescent : baseEnd_1661900 < baseStart_1661900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661923 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1661923 : Nat := 118140960795 + 1661923 * 2 ^ 59
def prefixEnd_1661923 : Nat := 4983230072969 + 3 ^ 40 * 1661923 * 2
def baseEnd_1661923 : Nat := 853365309762206452319461

theorem tailTrace_1661923 : CollatzResearch.WordTrace tailWord_1661923 prefixEnd_1661923 853365309762206452319461 := by
  unfold tailWord_1661923
  simp only [CollatzResearch.WordTrace]
  refine ⟨60615311558144279696342423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40410207705429519797561615 60615311558144279696342423)
  ·
    refine ⟨90922967337216419544513635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60615311558144279696342423 90922967337216419544513635)
    ·
      refine ⟨136384451005824629316770453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90922967337216419544513635 136384451005824629316770453)
      ·
        refine ⟨6393021140898029499223615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 136384451005824629316770453 6393021140898029499223615)
        ·
          refine ⟨9589531711347044248835423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6393021140898029499223615 9589531711347044248835423)
          ·
            refine ⟨14384297567020566373253135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9589531711347044248835423 14384297567020566373253135)
            ·
              refine ⟨21576446350530849559879703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14384297567020566373253135 21576446350530849559879703)
              ·
                refine ⟨32364669525796274339819555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21576446350530849559879703 32364669525796274339819555)
                ·
                  refine ⟨48547004288694411509729333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32364669525796274339819555 48547004288694411509729333)
                  ·
                    refine ⟨4551281652065101079037125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48547004288694411509729333 4551281652065101079037125)
                    ·
                      refine ⟨853365309762206452319461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4551281652065101079037125 853365309762206452319461)
                      ·
                        rfl

theorem cell23_1661923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1661923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661923 prefixEnd_1661923 := by exact prefixLift 1661923
  have htrace : WordTrace (prefixWord ++ tailWord_1661923) baseStart_1661923 baseEnd_1661923 := by
    simpa [prefixWord, tailWord_1661923, baseEnd_1661923] using wordTrace_append hprefix tailTrace_1661923
  have hstable : (prefixWord ++ tailWord_1661923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661923).length < 2 ^ (prefixWord ++ tailWord_1661923).sum := by decide
  have hdescent : baseEnd_1661923 < baseStart_1661923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661927 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 3, 3, 2]
def baseStart_1661927 : Nat := 118140960795 + 1661927 * 2 ^ 59
def prefixEnd_1661927 : Nat := 4983230072969 + 3 ^ 40 * 1661927 * 2
def baseEnd_1661927 : Nat := 853367363684824436669443

theorem tailTrace_1661927 : CollatzResearch.WordTrace tailWord_1661927 prefixEnd_1661927 853367363684824436669443 := by
  unfold tailWord_1661927
  simp only [CollatzResearch.WordTrace]
  refine ⟨60615457450129788379488035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40410304966753192252992023 60615457450129788379488035)
  ·
    refine ⟨90923186175194682569232053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60615457450129788379488035 90923186175194682569232053)
    ·
      refine ⟨8524048703924501490865505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90923186175194682569232053 8524048703924501490865505)
      ·
        refine ⟨6393036527943376118149129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8524048703924501490865505 6393036527943376118149129)
        ·
          refine ⟨4794777395957532088611847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6393036527943376118149129 4794777395957532088611847)
          ·
            refine ⟨7192166093936298132917771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4794777395957532088611847 7192166093936298132917771)
            ·
              refine ⟨10788249140904447199376657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7192166093936298132917771 10788249140904447199376657)
              ·
                refine ⟨8091186855678335399532493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10788249140904447199376657 8091186855678335399532493)
                ·
                  refine ⟨3034195070879375774824685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8091186855678335399532493 3034195070879375774824685)
                  ·
                    refine ⟨1137823151579765915559257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3034195070879375774824685 1137823151579765915559257)
                    ·
                      refine ⟨853367363684824436669443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1137823151579765915559257 853367363684824436669443)
                      ·
                        rfl

theorem cell23_1661927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_1661927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661927 prefixEnd_1661927 := by exact prefixLift 1661927
  have htrace : WordTrace (prefixWord ++ tailWord_1661927) baseStart_1661927 baseEnd_1661927 := by
    simpa [prefixWord, tailWord_1661927, baseEnd_1661927] using wordTrace_append hprefix tailTrace_1661927
  have hstable : (prefixWord ++ tailWord_1661927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661927).length < 2 ^ (prefixWord ++ tailWord_1661927).sum := by decide
  have hdescent : baseEnd_1661927 < baseStart_1661927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661957 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 4, 2, 2]
def baseStart_1661957 : Nat := 118140960795 + 1661957 * 2 ^ 59
def prefixEnd_1661957 : Nat := 4983230072969 + 3 ^ 40 * 1661957 * 2
def baseEnd_1661957 : Nat := 853382768104459319294305

theorem tailTrace_1661957 : CollatzResearch.WordTrace tailWord_1661957 prefixEnd_1661957 853382768104459319294305 := by
  unfold tailWord_1661957
  simp only [CollatzResearch.WordTrace]
  refine ⟨60616551640021103503080125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40411034426680735668720083 60616551640021103503080125)
  ·
    refine ⟨22731206865007913813655047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60616551640021103503080125 22731206865007913813655047)
    ·
      refine ⟨34096810297511870720482571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22731206865007913813655047 34096810297511870720482571)
      ·
        refine ⟨51145215446267806080723857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34096810297511870720482571 51145215446267806080723857)
        ·
          refine ⟨38358911584700854560542893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51145215446267806080723857 38358911584700854560542893)
          ·
            refine ⟨14384591844262820460203585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38358911584700854560542893 14384591844262820460203585)
            ·
              refine ⟨10788443883197115345152689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14384591844262820460203585 10788443883197115345152689)
              ·
                refine ⟨8091332912397836508864517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10788443883197115345152689 8091332912397836508864517)
                ·
                  refine ⟨1517124921074594345412097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8091332912397836508864517 1517124921074594345412097)
                  ·
                    refine ⟨1137843690805945759059073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1517124921074594345412097 1137843690805945759059073)
                    ·
                      refine ⟨853382768104459319294305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1137843690805945759059073 853382768104459319294305)
                      ·
                        rfl

theorem cell23_1661957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 2, 2].length) (baseStart_1661957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661957 prefixEnd_1661957 := by exact prefixLift 1661957
  have htrace : WordTrace (prefixWord ++ tailWord_1661957) baseStart_1661957 baseEnd_1661957 := by
    simpa [prefixWord, tailWord_1661957, baseEnd_1661957] using wordTrace_append hprefix tailTrace_1661957
  have hstable : (prefixWord ++ tailWord_1661957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661957).length < 2 ^ (prefixWord ++ tailWord_1661957).sum := by decide
  have hdescent : baseEnd_1661957 < baseStart_1661957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1661991 : List Nat := [1, 1, 7, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_1661991 : Nat := 118140960795 + 1661991 * 2 ^ 59
def prefixEnd_1661991 : Nat := 4983230072969 + 3 ^ 40 * 1661991 * 2
def baseEnd_1661991 : Nat := 853400226446712186269149

theorem tailTrace_1661991 : CollatzResearch.WordTrace tailWord_1661991 prefixEnd_1661991 853400226446712186269149 := by
  unfold tailWord_1661991
  simp only [CollatzResearch.WordTrace]
  refine ⟨60617791721897927309817827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40411861147931951539878551 60617791721897927309817827)
  ·
    refine ⟨90926687582846890964726741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60617791721897927309817827 90926687582846890964726741)
    ·
      refine ⟨2131094240222974006985783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 90926687582846890964726741 2131094240222974006985783)
      ·
        refine ⟨3196641360334461010478675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2131094240222974006985783 3196641360334461010478675)
        ·
          refine ⟨4794962040501691515718013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3196641360334461010478675 4794962040501691515718013)
          ·
            refine ⟨1798110765188134318394255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4794962040501691515718013 1798110765188134318394255)
            ·
              refine ⟨2697166147782201477591383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1798110765188134318394255 2697166147782201477591383)
              ·
                refine ⟨4045749221673302216387075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2697166147782201477591383 4045749221673302216387075)
                ·
                  refine ⟨6068623832509953324580613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4045749221673302216387075 6068623832509953324580613)
                  ·
                    refine ⟨1137866968595616248358865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6068623832509953324580613 1137866968595616248358865)
                    ·
                      refine ⟨853400226446712186269149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1137866968595616248358865 853400226446712186269149)
                      ·
                        rfl

theorem cell23_1661991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_1661991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1661991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1661991 prefixEnd_1661991 := by exact prefixLift 1661991
  have htrace : WordTrace (prefixWord ++ tailWord_1661991) baseStart_1661991 baseEnd_1661991 := by
    simpa [prefixWord, tailWord_1661991, baseEnd_1661991] using wordTrace_append hprefix tailTrace_1661991
  have hstable : (prefixWord ++ tailWord_1661991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1661991).length < 2 ^ (prefixWord ++ tailWord_1661991).sum := by decide
  have hdescent : baseEnd_1661991 < baseStart_1661991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1661991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662003 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 5]
def baseStart_1662003 : Nat := 118140960795 + 1662003 * 2 ^ 59
def prefixEnd_1662003 : Nat := 4983230072969 + 3 ^ 40 * 1662003 * 2
def baseEnd_1662003 : Nat := 853406388214566139319093

theorem tailTrace_1662003 : CollatzResearch.WordTrace tailWord_1662003 prefixEnd_1662003 853406388214566139319093 := by
  unfold tailWord_1662003
  simp only [CollatzResearch.WordTrace]
  refine ⟨60618229397854453359254663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40412152931902968906169775 60618229397854453359254663)
  ·
    refine ⟨90927344096781680038881995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60618229397854453359254663 90927344096781680038881995)
    ·
      refine ⟨136391016145172520058322993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90927344096781680038881995 136391016145172520058322993)
      ·
        refine ⟨102293262108879390043742245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136391016145172520058322993 102293262108879390043742245)
        ·
          refine ⟨19179986645414885633201671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102293262108879390043742245 19179986645414885633201671)
          ·
            refine ⟨28769979968122328449802507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19179986645414885633201671 28769979968122328449802507)
            ·
              refine ⟨43154969952183492674703761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28769979968122328449802507 43154969952183492674703761)
              ·
                refine ⟨32366227464137619506027821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43154969952183492674703761 32366227464137619506027821)
                ·
                  refine ⟨12137335299051607314760433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32366227464137619506027821 12137335299051607314760433)
                  ·
                    refine ⟨9103001474288705486070325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12137335299051607314760433 9103001474288705486070325)
                    ·
                      refine ⟨853406388214566139319093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9103001474288705486070325 853406388214566139319093)
                      ·
                        rfl

theorem cell23_1662003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_1662003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662003 prefixEnd_1662003 := by exact prefixLift 1662003
  have htrace : WordTrace (prefixWord ++ tailWord_1662003) baseStart_1662003 baseEnd_1662003 := by
    simpa [prefixWord, tailWord_1662003, baseEnd_1662003] using wordTrace_append hprefix tailTrace_1662003
  have hstable : (prefixWord ++ tailWord_1662003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662003).length < 2 ^ (prefixWord ++ tailWord_1662003).sum := by decide
  have hdescent : baseEnd_1662003 < baseStart_1662003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662014 : List Nat := [4, 2, 1, 3, 1, 1, 3, 3, 5]
def baseStart_1662014 : Nat := 118140960795 + 1662014 * 2 ^ 59
def prefixEnd_1662014 : Nat := 4983230072969 + 3 ^ 40 * 1662014 * 2
def baseEnd_1662014 : Nat := 94823559611307288475727

theorem tailTrace_1662014 : CollatzResearch.WordTrace tailWord_1662014 prefixEnd_1662014 94823559611307288475727 := by
  unfold tailWord_1662014
  simp only [CollatzResearch.WordTrace]
  refine ⟨7577328825101825279738137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40412420400543068158603397 7577328825101825279738137)
  ·
    refine ⟨5682996618826368959803603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7577328825101825279738137 5682996618826368959803603)
    ·
      refine ⟨8524494928239553439705405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5682996618826368959803603 8524494928239553439705405)
      ·
        refine ⟨3196685598089832539889527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8524494928239553439705405 3196685598089832539889527)
        ·
          refine ⟨4795028397134748809834291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3196685598089832539889527 4795028397134748809834291)
          ·
            refine ⟨7192542595702123214751437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4795028397134748809834291 7192542595702123214751437)
            ·
              refine ⟨2697203473388296205531789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7192542595702123214751437 2697203473388296205531789)
              ·
                refine ⟨1011451302520611077074421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2697203473388296205531789 1011451302520611077074421)
                ·
                  refine ⟨94823559611307288475727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1011451302520611077074421 94823559611307288475727)
                  ·
                    rfl

theorem cell23_1662014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_1662014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662014 prefixEnd_1662014 := by exact prefixLift 1662014
  have htrace : WordTrace (prefixWord ++ tailWord_1662014) baseStart_1662014 baseEnd_1662014 := by
    simpa [prefixWord, tailWord_1662014, baseEnd_1662014] using wordTrace_append hprefix tailTrace_1662014
  have hstable : (prefixWord ++ tailWord_1662014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662014).length < 2 ^ (prefixWord ++ tailWord_1662014).sum := by decide
  have hdescent : baseEnd_1662014 < baseStart_1662014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662090 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_1662090 : Nat := 118140960795 + 1662090 * 2 ^ 59
def prefixEnd_1662090 : Nat := 4983230072969 + 3 ^ 40 * 1662090 * 2
def baseEnd_1662090 : Nat := 853451061031507298931193

theorem tailTrace_1662090 : CollatzResearch.WordTrace tailWord_1662090 prefixEnd_1662090 853451061031507298931193 := by
  unfold tailWord_1662090
  simp only [CollatzResearch.WordTrace]
  refine ⟨15155350637134816804417931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40414268365692844811781149 15155350637134816804417931)
  ·
    refine ⟨22733025955702225206626897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15155350637134816804417931 22733025955702225206626897)
    ·
      refine ⟨17049769466776668904970173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22733025955702225206626897 17049769466776668904970173)
      ·
        refine ⟨6393663550041250839363815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17049769466776668904970173 6393663550041250839363815)
        ·
          refine ⟨9590495325061876259045723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6393663550041250839363815 9590495325061876259045723)
          ·
            refine ⟨14385742987592814388568585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9590495325061876259045723 14385742987592814388568585)
            ·
              refine ⟨10789307240694610791426439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14385742987592814388568585 10789307240694610791426439)
              ·
                refine ⟨16183960861041916187139659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10789307240694610791426439 16183960861041916187139659)
                ·
                  refine ⟨24275941291562874280709489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16183960861041916187139659 24275941291562874280709489)
                  ·
                    refine ⟨18206955968672155710532117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24275941291562874280709489 18206955968672155710532117)
                    ·
                      refine ⟨853451061031507298931193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18206955968672155710532117 853451061031507298931193)
                      ·
                        rfl

theorem cell23_1662090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_1662090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662090 prefixEnd_1662090 := by exact prefixLift 1662090
  have htrace : WordTrace (prefixWord ++ tailWord_1662090) baseStart_1662090 baseEnd_1662090 := by
    simpa [prefixWord, tailWord_1662090, baseEnd_1662090] using wordTrace_append hprefix tailTrace_1662090
  have hstable : (prefixWord ++ tailWord_1662090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662090).length < 2 ^ (prefixWord ++ tailWord_1662090).sum := by decide
  have hdescent : baseEnd_1662090 < baseStart_1662090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662147 : List Nat := [1, 1, 1, 3, 1, 1, 1, 8, 2, 4]
def baseStart_1662147 : Nat := 118140960795 + 1662147 * 2 ^ 59
def prefixEnd_1662147 : Nat := 4983230072969 + 3 ^ 40 * 1662147 * 2
def baseEnd_1662147 : Nat := 284493443142937858639477

theorem tailTrace_1662147 : CollatzResearch.WordTrace tailWord_1662147 prefixEnd_1662147 284493443142937858639477 := by
  unfold tailWord_1662147
  simp only [CollatzResearch.WordTrace]
  refine ⟨60623481509332765952496695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40415654339555177301664463 60623481509332765952496695)
  ·
    refine ⟨90935222263999148928745043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60623481509332765952496695 90935222263999148928745043)
    ·
      refine ⟨136402833395998723393117565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90935222263999148928745043 136402833395998723393117565)
      ·
        refine ⟨51151062523499521272419087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136402833395998723393117565 51151062523499521272419087)
        ·
          refine ⟨76726593785249281908628631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51151062523499521272419087 76726593785249281908628631)
          ·
            refine ⟨115089890677873922862942947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76726593785249281908628631 115089890677873922862942947)
            ·
              refine ⟨172634836016810884294414421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115089890677873922862942947 172634836016810884294414421)
              ·
                refine ⟨2023064484572002550325169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 172634836016810884294414421 2023064484572002550325169)
                ·
                  refine ⟨1517298363429001912743877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2023064484572002550325169 1517298363429001912743877)
                  ·
                    refine ⟨284493443142937858639477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1517298363429001912743877 284493443142937858639477)
                    ·
                      rfl

theorem cell23_1662147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 4].length) (baseStart_1662147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662147 prefixEnd_1662147 := by exact prefixLift 1662147
  have htrace : WordTrace (prefixWord ++ tailWord_1662147) baseStart_1662147 baseEnd_1662147 := by
    simpa [prefixWord, tailWord_1662147, baseEnd_1662147] using wordTrace_append hprefix tailTrace_1662147
  have hstable : (prefixWord ++ tailWord_1662147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662147).length < 2 ^ (prefixWord ++ tailWord_1662147).sum := by decide
  have hdescent : baseEnd_1662147 < baseStart_1662147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662167 : List Nat := [1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 4]
def baseStart_1662167 : Nat := 118140960795 + 1662167 * 2 ^ 59
def prefixEnd_1662167 : Nat := 4983230072969 + 3 ^ 40 * 1662167 * 2
def baseEnd_1662167 : Nat := 853490599041903497668339

theorem tailTrace_1662167 : CollatzResearch.WordTrace tailWord_1662167 prefixEnd_1662167 853490599041903497668339 := by
  unfold tailWord_1662167
  simp only [CollatzResearch.WordTrace]
  refine ⟨60624210969260309368224755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40416140646173539578816503 60624210969260309368224755)
  ·
    refine ⟨90936316453890464052337133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60624210969260309368224755 90936316453890464052337133)
    ·
      refine ⟨34101118670208924019626425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90936316453890464052337133 34101118670208924019626425)
      ·
        refine ⟨25575839002656693014719819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34101118670208924019626425 25575839002656693014719819)
        ·
          refine ⟨38363758503985039522079729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25575839002656693014719819 38363758503985039522079729)
          ·
            refine ⟨28772818877988779641559797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38363758503985039522079729 28772818877988779641559797)
            ·
              refine ⟨2697451769811448091396231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28772818877988779641559797 2697451769811448091396231)
              ·
                refine ⟨4046177654717172137094347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2697451769811448091396231 4046177654717172137094347)
                ·
                  refine ⟨6069266482075758205641521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4046177654717172137094347 6069266482075758205641521)
                  ·
                    refine ⟨4551949861556818654231141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6069266482075758205641521 4551949861556818654231141)
                    ·
                      refine ⟨853490599041903497668339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4551949861556818654231141 853490599041903497668339)
                      ·
                        rfl

theorem cell23_1662167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_1662167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662167 prefixEnd_1662167 := by exact prefixLift 1662167
  have htrace : WordTrace (prefixWord ++ tailWord_1662167) baseStart_1662167 baseEnd_1662167 := by
    simpa [prefixWord, tailWord_1662167, baseEnd_1662167] using wordTrace_append hprefix tailTrace_1662167
  have hstable : (prefixWord ++ tailWord_1662167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662167).length < 2 ^ (prefixWord ++ tailWord_1662167).sum := by decide
  have hdescent : baseEnd_1662167 < baseStart_1662167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662177 : List Nat := [1, 2, 3, 1, 3, 2, 4, 7]
def baseStart_1662177 : Nat := 118140960795 + 1662177 * 2 ^ 59
def prefixEnd_1662177 : Nat := 4983230072969 + 3 ^ 40 * 1662177 * 2
def baseEnd_1662177 : Nat := 31610953105498091057159

theorem tailTrace_1662177 : CollatzResearch.WordTrace tailWord_1662177 prefixEnd_1662177 31610953105498091057159 := by
  unfold tailWord_1662177
  simp only [CollatzResearch.WordTrace]
  refine ⟨60624575699224081076088785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40416383799482720717392523 60624575699224081076088785)
  ·
    refine ⟨45468431774418060807066589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60624575699224081076088785 45468431774418060807066589)
    ·
      refine ⟨17050661915406772802649971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45468431774418060807066589 17050661915406772802649971)
      ·
        refine ⟨25575992873110159203974957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17050661915406772802649971 25575992873110159203974957)
        ·
          refine ⟨9590997327416309701490609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25575992873110159203974957 9590997327416309701490609)
          ·
            refine ⟨7193247995562232276117957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9590997327416309701490609 7193247995562232276117957)
            ·
              refine ⟨1348733999167918551772117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7193247995562232276117957 1348733999167918551772117)
              ·
                refine ⟨31610953105498091057159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1348733999167918551772117 31610953105498091057159)
                ·
                  rfl

theorem cell23_1662177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 7].length) (baseStart_1662177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662177 prefixEnd_1662177 := by exact prefixLift 1662177
  have htrace : WordTrace (prefixWord ++ tailWord_1662177) baseStart_1662177 baseEnd_1662177 := by
    simpa [prefixWord, tailWord_1662177, baseEnd_1662177] using wordTrace_append hprefix tailTrace_1662177
  have hstable : (prefixWord ++ tailWord_1662177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662177).length < 2 ^ (prefixWord ++ tailWord_1662177).sum := by decide
  have hdescent : baseEnd_1662177 < baseStart_1662177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662188 : List Nat := [2, 2, 1, 1, 2, 4, 3, 3, 1, 2, 2]
def baseStart_1662188 : Nat := 118140960795 + 1662188 * 2 ^ 59
def prefixEnd_1662188 : Nat := 4983230072969 + 3 ^ 40 * 1662188 * 2
def baseEnd_1662188 : Nat := 853501382135647915505743

theorem tailTrace_1662188 : CollatzResearch.WordTrace tailWord_1662188 prefixEnd_1662188 853501382135647915505743 := by
  unfold tailWord_1662188
  simp only [CollatzResearch.WordTrace]
  refine ⟨30312488451092114977369609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40416651268122819969826145 30312488451092114977369609)
  ·
    refine ⟨22734366338319086233027207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30312488451092114977369609 22734366338319086233027207)
    ·
      refine ⟨34101549507478629349540811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22734366338319086233027207 34101549507478629349540811)
      ·
        refine ⟨51152324261217944024311217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34101549507478629349540811 51152324261217944024311217)
        ·
          refine ⟨38364243195913458018233413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51152324261217944024311217 38364243195913458018233413)
          ·
            refine ⟨7193295599233773378418765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38364243195913458018233413 7193295599233773378418765)
            ·
              refine ⟨2697485849712665016907037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7193295599233773378418765 2697485849712665016907037)
              ·
                refine ⟨1011557193642249381340139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2697485849712665016907037 1011557193642249381340139)
                ·
                  refine ⟨1517335790463374072010209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011557193642249381340139 1517335790463374072010209)
                  ·
                    refine ⟨1138001842847530554007657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1517335790463374072010209 1138001842847530554007657)
                    ·
                      refine ⟨853501382135647915505743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1138001842847530554007657 853501382135647915505743)
                      ·
                        rfl

theorem cell23_1662188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 1, 2, 2].length) (baseStart_1662188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662188 prefixEnd_1662188 := by exact prefixLift 1662188
  have htrace : WordTrace (prefixWord ++ tailWord_1662188) baseStart_1662188 baseEnd_1662188 := by
    simpa [prefixWord, tailWord_1662188, baseEnd_1662188] using wordTrace_append hprefix tailTrace_1662188
  have hstable : (prefixWord ++ tailWord_1662188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662188).length < 2 ^ (prefixWord ++ tailWord_1662188).sum := by decide
  have hdescent : baseEnd_1662188 < baseStart_1662188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662194 : List Nat := [3, 2, 1, 3, 4, 1, 9]
def baseStart_1662194 : Nat := 118140960795 + 1662194 * 2 ^ 59
def prefixEnd_1662194 : Nat := 4983230072969 + 3 ^ 40 * 1662194 * 2
def baseEnd_1662194 : Nat := 10537092136044134469515

theorem tailTrace_1662194 : CollatzResearch.WordTrace tailWord_1662194 prefixEnd_1662194 10537092136044134469515 := by
  unfold tailWord_1662194
  simp only [CollatzResearch.WordTrace]
  refine ⟨15156298935040623244864409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40416797160108328652971757 15156298935040623244864409)
  ·
    refine ⟨11367224201280467433648307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15156298935040623244864409 11367224201280467433648307)
    ·
      refine ⟨17050836301920701150472461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11367224201280467433648307 17050836301920701150472461)
      ·
        refine ⟨6394063613220262931427173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17050836301920701150472461 6394063613220262931427173)
        ·
          refine ⟨1198886927478799299642595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6394063613220262931427173 1198886927478799299642595)
          ·
            refine ⟨1798330391218198949463893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198886927478799299642595 1798330391218198949463893)
            ·
              refine ⟨10537092136044134469515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1798330391218198949463893 10537092136044134469515)
              ·
                rfl

theorem cell23_1662194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 9].length) (baseStart_1662194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662194 prefixEnd_1662194 := by exact prefixLift 1662194
  have htrace : WordTrace (prefixWord ++ tailWord_1662194) baseStart_1662194 baseEnd_1662194 := by
    simpa [prefixWord, tailWord_1662194, baseEnd_1662194] using wordTrace_append hprefix tailTrace_1662194
  have hstable : (prefixWord ++ tailWord_1662194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662194).length < 2 ^ (prefixWord ++ tailWord_1662194).sum := by decide
  have hdescent : baseEnd_1662194 < baseStart_1662194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662238 : List Nat := [4, 3, 2, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1662238 : Nat := 118140960795 + 1662238 * 2 ^ 59
def prefixEnd_1662238 : Nat := 4983230072969 + 3 ^ 40 * 1662238 * 2
def baseEnd_1662238 : Nat := 853527056168372719880513

theorem tailTrace_1662238 : CollatzResearch.WordTrace tailWord_1662238 prefixEnd_1662238 853527056168372719880513 := by
  unfold tailWord_1662238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7578350069000386061757421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40417867034668725662706245 7578350069000386061757421)
  ·
    refine ⟨2841881275875144773159033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7578350069000386061757421 2841881275875144773159033)
    ·
      refine ⟨2131410956906358579869275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2841881275875144773159033 2131410956906358579869275)
      ·
        refine ⟨3197116435359537869803913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2131410956906358579869275 3197116435359537869803913)
        ·
          refine ⟨2397837326519653402352935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3197116435359537869803913 2397837326519653402352935)
          ·
            refine ⟨3596755989779480103529403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2397837326519653402352935 3596755989779480103529403)
            ·
              refine ⟨5395133984669220155294105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3596755989779480103529403 5395133984669220155294105)
              ·
                refine ⟨4046350488501915116470579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5395133984669220155294105 4046350488501915116470579)
                ·
                  refine ⟨6069525732752872674705869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4046350488501915116470579 6069525732752872674705869)
                  ·
                    refine ⟨2276072149782327253014701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6069525732752872674705869 2276072149782327253014701)
                    ·
                      refine ⟨853527056168372719880513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2276072149782327253014701 853527056168372719880513)
                      ·
                        rfl

theorem cell23_1662238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1662238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662238 prefixEnd_1662238 := by exact prefixLift 1662238
  have htrace : WordTrace (prefixWord ++ tailWord_1662238) baseStart_1662238 baseEnd_1662238 := by
    simpa [prefixWord, tailWord_1662238, baseEnd_1662238] using wordTrace_append hprefix tailTrace_1662238
  have hstable : (prefixWord ++ tailWord_1662238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662238).length < 2 ^ (prefixWord ++ tailWord_1662238).sum := by decide
  have hdescent : baseEnd_1662238 < baseStart_1662238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662312 : List Nat := [2, 1, 4, 2, 4, 1, 1, 2, 2, 2, 2]
def baseStart_1662312 : Nat := 118140960795 + 1662312 * 2 ^ 59
def prefixEnd_1662312 : Nat := 4983230072969 + 3 ^ 40 * 1662312 * 2
def baseEnd_1662312 : Nat := 853565053736805430355173

theorem tailTrace_1662312 : CollatzResearch.WordTrace tailWord_1662312 prefixEnd_1662312 853565053736805430355173 := by
  unfold tailWord_1662312
  simp only [CollatzResearch.WordTrace]
  refine ⟨30314749776867499566126595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40419666369156666088168793 30314749776867499566126595)
  ·
    refine ⟨45472124665301249349189893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30314749776867499566126595 45472124665301249349189893)
    ·
      refine ⟨8526023374743984252973105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45472124665301249349189893 8526023374743984252973105)
      ·
        refine ⟨6394517531057988189729829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8526023374743984252973105 6394517531057988189729829)
        ·
          refine ⟨1198972037073372785574343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6394517531057988189729829 1198972037073372785574343)
          ·
            refine ⟨1798458055610059178361515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198972037073372785574343 1798458055610059178361515)
            ·
              refine ⟨2697687083415088767542273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1798458055610059178361515 2697687083415088767542273)
              ·
                refine ⟨2023265312561316575656705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2697687083415088767542273 2023265312561316575656705)
                ·
                  refine ⟨1517448984420987431742529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2023265312561316575656705 1517448984420987431742529)
                  ·
                    refine ⟨1138086738315740573806897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1517448984420987431742529 1138086738315740573806897)
                    ·
                      refine ⟨853565053736805430355173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1138086738315740573806897 853565053736805430355173)
                      ·
                        rfl

theorem cell23_1662312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_1662312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662312 prefixEnd_1662312 := by exact prefixLift 1662312
  have htrace : WordTrace (prefixWord ++ tailWord_1662312) baseStart_1662312 baseEnd_1662312 := by
    simpa [prefixWord, tailWord_1662312, baseEnd_1662312] using wordTrace_append hprefix tailTrace_1662312
  have hstable : (prefixWord ++ tailWord_1662312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662312).length < 2 ^ (prefixWord ++ tailWord_1662312).sum := by decide
  have hdescent : baseEnd_1662312 < baseStart_1662312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662347 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 4]
def baseStart_1662347 : Nat := 118140960795 + 1662347 * 2 ^ 59
def prefixEnd_1662347 : Nat := 4983230072969 + 3 ^ 40 * 1662347 * 2
def baseEnd_1662347 : Nat := 853583025559712793417511

theorem tailTrace_1662347 : CollatzResearch.WordTrace tailWord_1662347 prefixEnd_1662347 853583025559712793417511 := by
  unfold tailWord_1662347
  simp only [CollatzResearch.WordTrace]
  refine ⟨60630776108608200109777295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40420517405738800073184863 60630776108608200109777295)
  ·
    refine ⟨90946164162912300164665943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60630776108608200109777295 90946164162912300164665943)
    ·
      refine ⟨136419246244368450246998915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90946164162912300164665943 136419246244368450246998915)
      ·
        refine ⟨204628869366552675370498373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136419246244368450246998915 204628869366552675370498373)
        ·
          refine ⟨38367913006228626631968445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204628869366552675370498373 38367913006228626631968445)
          ·
            refine ⟨14387967377335734986988167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38367913006228626631968445 14387967377335734986988167)
            ·
              refine ⟨21581951066003602480482251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14387967377335734986988167 21581951066003602480482251)
              ·
                refine ⟨32372926599005403720723377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21581951066003602480482251 32372926599005403720723377)
                ·
                  refine ⟨24279694949254052790542533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32372926599005403720723377 24279694949254052790542533)
                  ·
                    refine ⟨4552442802985134898226725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24279694949254052790542533 4552442802985134898226725)
                    ·
                      refine ⟨853583025559712793417511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4552442802985134898226725 853583025559712793417511)
                      ·
                        rfl

theorem cell23_1662347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 4].length) (baseStart_1662347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662347 prefixEnd_1662347 := by exact prefixLift 1662347
  have htrace : WordTrace (prefixWord ++ tailWord_1662347) baseStart_1662347 baseEnd_1662347 := by
    simpa [prefixWord, tailWord_1662347, baseEnd_1662347] using wordTrace_append hprefix tailTrace_1662347
  have hstable : (prefixWord ++ tailWord_1662347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662347).length < 2 ^ (prefixWord ++ tailWord_1662347).sum := by decide
  have hdescent : baseEnd_1662347 < baseStart_1662347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662357 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 8]
def baseStart_1662357 : Nat := 118140960795 + 1662357 * 2 ^ 59
def prefixEnd_1662357 : Nat := 4983230072969 + 3 ^ 40 * 1662357 * 2
def baseEnd_1662357 : Nat := 94843128929584194921385

theorem tailTrace_1662357 : CollatzResearch.WordTrace tailWord_1662357 prefixEnd_1662357 94843128929584194921385 := by
  unfold tailWord_1662357
  simp only [CollatzResearch.WordTrace]
  refine ⟨60631140838571971817641325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40420760559047981211760883 60631140838571971817641325)
  ·
    refine ⟨22736677814464489431615497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60631140838571971817641325 22736677814464489431615497)
    ·
      refine ⟨17052508360848367073711623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22736677814464489431615497 17052508360848367073711623)
      ·
        refine ⟨25578762541272550610567435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17052508360848367073711623 25578762541272550610567435)
        ·
          refine ⟨38368143811908825915851153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25578762541272550610567435 38368143811908825915851153)
          ·
            refine ⟨28776107858931619436888365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38368143811908825915851153 28776107858931619436888365)
            ·
              refine ⟨10791040447099357288833137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28776107858931619436888365 10791040447099357288833137)
              ·
                refine ⟨8093280335324517966624853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10791040447099357288833137 8093280335324517966624853)
                ·
                  refine ⟨94843128929584194921385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8093280335324517966624853 94843128929584194921385)
                  ·
                    rfl

theorem cell23_1662357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 8].length) (baseStart_1662357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662357 prefixEnd_1662357 := by exact prefixLift 1662357
  have htrace : WordTrace (prefixWord ++ tailWord_1662357) baseStart_1662357 baseEnd_1662357 := by
    simpa [prefixWord, tailWord_1662357, baseEnd_1662357] using wordTrace_append hprefix tailTrace_1662357
  have hstable : (prefixWord ++ tailWord_1662357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662357).length < 2 ^ (prefixWord ++ tailWord_1662357).sum := by decide
  have hdescent : baseEnd_1662357 < baseStart_1662357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662411 : List Nat := [1, 1, 1, 1, 3, 3, 3, 3, 2, 3, 2]
def baseStart_1662411 : Nat := 118140960795 + 1662411 * 2 ^ 59
def prefixEnd_1662411 : Nat := 4983230072969 + 3 ^ 40 * 1662411 * 2
def baseEnd_1662411 : Nat := 853615888321600543017217

theorem tailTrace_1662411 : CollatzResearch.WordTrace tailWord_1662411 prefixEnd_1662411 853615888321600543017217 := by
  unfold tailWord_1662411
  simp only [CollatzResearch.WordTrace]
  refine ⟨60633110380376339040107087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40422073586917559360071391 60633110380376339040107087)
  ·
    refine ⟨90949665570564508560160631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60633110380376339040107087 90949665570564508560160631)
    ·
      refine ⟨136424498355846762840240947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90949665570564508560160631 136424498355846762840240947)
      ·
        refine ⟨204636747533770144260361421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136424498355846762840240947 204636747533770144260361421)
        ·
          refine ⟨76738780325163804097635533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204636747533770144260361421 76738780325163804097635533)
          ·
            refine ⟨28777042621936426536613325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76738780325163804097635533 28777042621936426536613325)
            ·
              refine ⟨10791390983226159951229997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28777042621936426536613325 10791390983226159951229997)
              ·
                refine ⟨4046771618709809981711249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10791390983226159951229997 4046771618709809981711249)
                ·
                  refine ⟨3035078714032357486283437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4046771618709809981711249 3035078714032357486283437)
                  ·
                    refine ⟨1138154517762134057356289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3035078714032357486283437 1138154517762134057356289)
                    ·
                      refine ⟨853615888321600543017217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1138154517762134057356289 853615888321600543017217)
                      ·
                        rfl

theorem cell23_1662411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 3, 2].length) (baseStart_1662411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662411 prefixEnd_1662411 := by exact prefixLift 1662411
  have htrace : WordTrace (prefixWord ++ tailWord_1662411) baseStart_1662411 baseEnd_1662411 := by
    simpa [prefixWord, tailWord_1662411, baseEnd_1662411] using wordTrace_append hprefix tailTrace_1662411
  have hstable : (prefixWord ++ tailWord_1662411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662411).length < 2 ^ (prefixWord ++ tailWord_1662411).sum := by decide
  have hdescent : baseEnd_1662411 < baseStart_1662411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662427 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 5]
def baseStart_1662427 : Nat := 118140960795 + 1662427 * 2 ^ 59
def prefixEnd_1662427 : Nat := 4983230072969 + 3 ^ 40 * 1662427 * 2
def baseEnd_1662427 : Nat := 853624104012072480417143

theorem tailTrace_1662427 : CollatzResearch.WordTrace tailWord_1662427 prefixEnd_1662427 853624104012072480417143 := by
  unfold tailWord_1662427
  simp only [CollatzResearch.WordTrace]
  refine ⟨60633693948318373772689535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40422462632212249181793023 60633693948318373772689535)
  ·
    refine ⟨90950540922477560659034303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60633693948318373772689535 90950540922477560659034303)
    ·
      refine ⟨136425811383716340988551455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90950540922477560659034303 136425811383716340988551455)
      ·
        refine ⟨204638717075574511482827183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136425811383716340988551455 204638717075574511482827183)
        ·
          refine ⟨306958075613361767224240775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204638717075574511482827183 306958075613361767224240775)
          ·
            refine ⟨460437113420042650836361163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306958075613361767224240775 460437113420042650836361163)
            ·
              refine ⟨690655670130063976254541745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460437113420042650836361163 690655670130063976254541745)
              ·
                refine ⟨517991752597547982190906309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 690655670130063976254541745 517991752597547982190906309)
                ·
                  refine ⟨97123453612040246660794933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 517991752597547982190906309 97123453612040246660794933)
                  ·
                    refine ⟨9105323776128773124449525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97123453612040246660794933 9105323776128773124449525)
                    ·
                      refine ⟨853624104012072480417143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9105323776128773124449525 853624104012072480417143)
                      ·
                        rfl

theorem cell23_1662427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 5].length) (baseStart_1662427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662427 prefixEnd_1662427 := by exact prefixLift 1662427
  have htrace : WordTrace (prefixWord ++ tailWord_1662427) baseStart_1662427 baseEnd_1662427 := by
    simpa [prefixWord, tailWord_1662427, baseEnd_1662427] using wordTrace_append hprefix tailTrace_1662427
  have hstable : (prefixWord ++ tailWord_1662427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662427).length < 2 ^ (prefixWord ++ tailWord_1662427).sum := by decide
  have hdescent : baseEnd_1662427 < baseStart_1662427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662435 : List Nat := [1, 1, 1, 6, 2, 2, 1, 4, 1, 1, 3]
def baseStart_1662435 : Nat := 118140960795 + 1662435 * 2 ^ 59
def prefixEnd_1662435 : Nat := 4983230072969 + 3 ^ 40 * 1662435 * 2
def baseEnd_1662435 : Nat := 853628211857308449117107

theorem tailTrace_1662435 : CollatzResearch.WordTrace tailWord_1662435 prefixEnd_1662435 853628211857308449117107 := by
  unfold tailWord_1662435
  simp only [CollatzResearch.WordTrace]
  refine ⟨60633985732289391138980759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40422657154859594092653839 60633985732289391138980759)
  ·
    refine ⟨90950978598434086708471139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60633985732289391138980759 90950978598434086708471139)
    ·
      refine ⟨136426467897651130062706709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90950978598434086708471139 136426467897651130062706709)
      ·
        refine ⟨6394990682702396721689377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 136426467897651130062706709 6394990682702396721689377)
        ·
          refine ⟨4796243012026797541267033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6394990682702396721689377 4796243012026797541267033)
          ·
            refine ⟨3597182259020098155950275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4796243012026797541267033 3597182259020098155950275)
            ·
              refine ⟨5395773388530147233925413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3597182259020098155950275 5395773388530147233925413)
              ·
                refine ⟨1011707510349402606361015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5395773388530147233925413 1011707510349402606361015)
                ·
                  refine ⟨1517561265524103909541523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011707510349402606361015 1517561265524103909541523)
                  ·
                    refine ⟨2276341898286155864312285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1517561265524103909541523 2276341898286155864312285)
                    ·
                      refine ⟨853628211857308449117107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2276341898286155864312285 853628211857308449117107)
                      ·
                        rfl

theorem cell23_1662435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_1662435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662435 prefixEnd_1662435 := by exact prefixLift 1662435
  have htrace : WordTrace (prefixWord ++ tailWord_1662435) baseStart_1662435 baseEnd_1662435 := by
    simpa [prefixWord, tailWord_1662435, baseEnd_1662435] using wordTrace_append hprefix tailTrace_1662435
  have hstable : (prefixWord ++ tailWord_1662435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662435).length < 2 ^ (prefixWord ++ tailWord_1662435).sum := by decide
  have hdescent : baseEnd_1662435 < baseStart_1662435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662458 : List Nat := [3, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2]
def baseStart_1662458 : Nat := 118140960795 + 1662458 * 2 ^ 59
def prefixEnd_1662458 : Nat := 4983230072969 + 3 ^ 40 * 1662458 * 2
def baseEnd_1662458 : Nat := 853640021912361859129501

theorem tailTrace_1662458 : CollatzResearch.WordTrace tailWord_1662458 prefixEnd_1662458 853640021912361859129501 := by
  unfold tailWord_1662458
  simp only [CollatzResearch.WordTrace]
  refine ⟨15158706152801516516767007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40423216407470710711378685 15158706152801516516767007)
  ·
    refine ⟨22738059229202274775150511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15158706152801516516767007 22738059229202274775150511)
    ·
      refine ⟨34107088843803412162725767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22738059229202274775150511 34107088843803412162725767)
      ·
        refine ⟨51160633265705118244088651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34107088843803412162725767 51160633265705118244088651)
        ·
          refine ⟨76740949898557677366132977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51160633265705118244088651 76740949898557677366132977)
          ·
            refine ⟨57555712423918258024599733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76740949898557677366132977 57555712423918258024599733)
            ·
              refine ⟨5395848039742336689806225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57555712423918258024599733 5395848039742336689806225)
              ·
                refine ⟨4046886029806752517354669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5395848039742336689806225 4046886029806752517354669)
                ·
                  refine ⟨1517582261177532194008001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4046886029806752517354669 1517582261177532194008001)
                  ·
                    refine ⟨1138186695883149145506001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1517582261177532194008001 1138186695883149145506001)
                    ·
                      refine ⟨853640021912361859129501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1138186695883149145506001 853640021912361859129501)
                      ·
                        rfl

theorem cell23_1662458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2].length) (baseStart_1662458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662458 prefixEnd_1662458 := by exact prefixLift 1662458
  have htrace : WordTrace (prefixWord ++ tailWord_1662458) baseStart_1662458 baseEnd_1662458 := by
    simpa [prefixWord, tailWord_1662458, baseEnd_1662458] using wordTrace_append hprefix tailTrace_1662458
  have hstable : (prefixWord ++ tailWord_1662458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662458).length < 2 ^ (prefixWord ++ tailWord_1662458).sum := by decide
  have hdescent : baseEnd_1662458 < baseStart_1662458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662461 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 3, 2, 3]
def baseStart_1662461 : Nat := 118140960795 + 1662461 * 2 ^ 59
def prefixEnd_1662461 : Nat := 4983230072969 + 3 ^ 40 * 1662461 * 2
def baseEnd_1662461 : Nat := 853641562354325347391987

theorem tailTrace_1662461 : CollatzResearch.WordTrace tailWord_1662461 prefixEnd_1662461 853641562354325347391987 := by
  unfold tailWord_1662461
  simp only [CollatzResearch.WordTrace]
  refine ⟨60634934030195197579427237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40423289353463465052951491 60634934030195197579427237)
  ·
    refine ⟨11369050130661599546142607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60634934030195197579427237 11369050130661599546142607)
    ·
      refine ⟨17053575195992399319213911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11369050130661599546142607 17053575195992399319213911)
      ·
        refine ⟨25580362793988598978820867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17053575195992399319213911 25580362793988598978820867)
        ·
          refine ⟨38370544190982898468231301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25580362793988598978820867 38370544190982898468231301)
          ·
            refine ⟨7194477035809293462793369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38370544190982898468231301 7194477035809293462793369)
            ·
              refine ⟨5395857776856970097095027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7194477035809293462793369 5395857776856970097095027)
              ·
                refine ⟨8093786665285455145642541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5395857776856970097095027 8093786665285455145642541)
                ·
                  refine ⟨3035169999482045679615953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8093786665285455145642541 3035169999482045679615953)
                  ·
                    refine ⟨2276377499611534259711965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3035169999482045679615953 2276377499611534259711965)
                    ·
                      refine ⟨853641562354325347391987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2276377499611534259711965 853641562354325347391987)
                      ·
                        rfl

theorem cell23_1662461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_1662461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662461 prefixEnd_1662461 := by exact prefixLift 1662461
  have htrace : WordTrace (prefixWord ++ tailWord_1662461) baseStart_1662461 baseEnd_1662461 := by
    simpa [prefixWord, tailWord_1662461, baseEnd_1662461] using wordTrace_append hprefix tailTrace_1662461
  have hstable : (prefixWord ++ tailWord_1662461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662461).length < 2 ^ (prefixWord ++ tailWord_1662461).sum := by decide
  have hdescent : baseEnd_1662461 < baseStart_1662461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662471 : List Nat := [1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_1662471 : Nat := 118140960795 + 1662471 * 2 ^ 59
def prefixEnd_1662471 : Nat := 4983230072969 + 3 ^ 40 * 1662471 * 2
def baseEnd_1662471 : Nat := 853646697160870308266941

theorem tailTrace_1662471 : CollatzResearch.WordTrace tailWord_1662471 prefixEnd_1662471 853646697160870308266941 := by
  unfold tailWord_1662471
  simp only [CollatzResearch.WordTrace]
  refine ⟨60635298760158969287291267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40423532506772646191527511 60635298760158969287291267)
  ·
    refine ⟨90952948140238453930936901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60635298760158969287291267 90952948140238453930936901)
    ·
      refine ⟨17053677776294710112050669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90952948140238453930936901 17053677776294710112050669)
      ·
        refine ⟨6395129166110516292019001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17053677776294710112050669 6395129166110516292019001)
        ·
          refine ⟨4796346874582887219014251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6395129166110516292019001 4796346874582887219014251)
          ·
            refine ⟨7194520311874330828521377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4796346874582887219014251 7194520311874330828521377)
            ·
              refine ⟨5395890233905748121391033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7194520311874330828521377 5395890233905748121391033)
              ·
                refine ⟨4046917675429311091043275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5395890233905748121391033 4046917675429311091043275)
                ·
                  refine ⟨6070376513143966636564913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4046917675429311091043275 6070376513143966636564913)
                  ·
                    refine ⟨4552782384857974977423685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6070376513143966636564913 4552782384857974977423685)
                    ·
                      refine ⟨853646697160870308266941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4552782384857974977423685 853646697160870308266941)
                      ·
                        rfl

theorem cell23_1662471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_1662471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662471 prefixEnd_1662471 := by exact prefixLift 1662471
  have htrace : WordTrace (prefixWord ++ tailWord_1662471) baseStart_1662471 baseEnd_1662471 := by
    simpa [prefixWord, tailWord_1662471, baseEnd_1662471] using wordTrace_append hprefix tailTrace_1662471
  have hstable : (prefixWord ++ tailWord_1662471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662471).length < 2 ^ (prefixWord ++ tailWord_1662471).sum := by decide
  have hdescent : baseEnd_1662471 < baseStart_1662471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662475 : List Nat := [1, 1, 1, 1, 8, 2, 2, 1, 1, 1, 4]
def baseStart_1662475 : Nat := 118140960795 + 1662475 * 2 ^ 59
def prefixEnd_1662475 : Nat := 4983230072969 + 3 ^ 40 * 1662475 * 2
def baseEnd_1662475 : Nat := 853648751083488292616923

theorem tailTrace_1662475 : CollatzResearch.WordTrace tailWord_1662475 prefixEnd_1662475 853648751083488292616923 := by
  unfold tailWord_1662475
  simp only [CollatzResearch.WordTrace]
  refine ⟨60635444652144477970436879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40423629768096318646957919 60635444652144477970436879)
  ·
    refine ⟨90953166978216716955655319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60635444652144477970436879 90953166978216716955655319)
    ·
      refine ⟨136429750467325075433482979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90953166978216716955655319 136429750467325075433482979)
      ·
        refine ⟨204644625700987613150224469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136429750467325075433482979 204644625700987613150224469)
        ·
          refine ⟨2398179207433448591604193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 204644625700987613150224469 2398179207433448591604193)
          ·
            refine ⟨1798634405575086443703145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2398179207433448591604193 1798634405575086443703145)
            ·
              refine ⟨1348975804181314832777359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1798634405575086443703145 1348975804181314832777359)
              ·
                refine ⟨2023463706271972249166039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1348975804181314832777359 2023463706271972249166039)
                ·
                  refine ⟨3035195559407958373749059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2023463706271972249166039 3035195559407958373749059)
                  ·
                    refine ⟨4552793339111937560623589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3035195559407958373749059 4552793339111937560623589)
                    ·
                      refine ⟨853648751083488292616923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4552793339111937560623589 853648751083488292616923)
                      ·
                        rfl

theorem cell23_1662475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 1, 1, 4].length) (baseStart_1662475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662475 prefixEnd_1662475 := by exact prefixLift 1662475
  have htrace : WordTrace (prefixWord ++ tailWord_1662475) baseStart_1662475 baseEnd_1662475 := by
    simpa [prefixWord, tailWord_1662475, baseEnd_1662475] using wordTrace_append hprefix tailTrace_1662475
  have hstable : (prefixWord ++ tailWord_1662475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662475).length < 2 ^ (prefixWord ++ tailWord_1662475).sum := by decide
  have hdescent : baseEnd_1662475 < baseStart_1662475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662601 : List Nat := [1, 2, 1, 1, 4, 1, 4, 2, 2, 5]
def baseStart_1662601 : Nat := 118140960795 + 1662601 * 2 ^ 59
def prefixEnd_1662601 : Nat := 4983230072969 + 3 ^ 40 * 1662601 * 2
def baseEnd_1662601 : Nat := 284571149881984933213781

theorem tailTrace_1662601 : CollatzResearch.WordTrace tailWord_1662601 prefixEnd_1662601 284571149881984933213781 := by
  unfold tailWord_1662601
  simp only [CollatzResearch.WordTrace]
  refine ⟨60640040249688001489523657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40426693499792000993015771 60640040249688001489523657)
  ·
    refine ⟨45480030187266001117142743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60640040249688001489523657 45480030187266001117142743)
    ·
      refine ⟨68220045280899001675714115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45480030187266001117142743 68220045280899001675714115)
      ·
        refine ⟨102330067921348502513571173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68220045280899001675714115 102330067921348502513571173)
        ·
          refine ⟨19186887735252844221294595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102330067921348502513571173 19186887735252844221294595)
          ·
            refine ⟨28780331602879266331941893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19186887735252844221294595 28780331602879266331941893)
            ·
              refine ⟨5396312175539862437239105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28780331602879266331941893 5396312175539862437239105)
              ·
                refine ⟨4047234131654896827929329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5396312175539862437239105 4047234131654896827929329)
                ·
                  refine ⟨3035425598741172620946997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4047234131654896827929329 3035425598741172620946997)
                  ·
                    refine ⟨284571149881984933213781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3035425598741172620946997 284571149881984933213781)
                    ·
                      rfl

theorem cell23_1662601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 5].length) (baseStart_1662601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662601 prefixEnd_1662601 := by exact prefixLift 1662601
  have htrace : WordTrace (prefixWord ++ tailWord_1662601) baseStart_1662601 baseEnd_1662601 := by
    simpa [prefixWord, tailWord_1662601, baseEnd_1662601] using wordTrace_append hprefix tailTrace_1662601
  have hstable : (prefixWord ++ tailWord_1662601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662601).length < 2 ^ (prefixWord ++ tailWord_1662601).sum := by decide
  have hdescent : baseEnd_1662601 < baseStart_1662601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662621 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_1662621 : Nat := 118140960795 + 1662621 * 2 ^ 59
def prefixEnd_1662621 : Nat := 4983230072969 + 3 ^ 40 * 1662621 * 2
def baseEnd_1662621 : Nat := 853723719259044721391251

theorem tailTrace_1662621 : CollatzResearch.WordTrace tailWord_1662621 prefixEnd_1662621 853723719259044721391251 := by
  unfold tailWord_1662621
  simp only [CollatzResearch.WordTrace]
  refine ⟨60640769709615544905251717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40427179806410363270167811 60640769709615544905251717)
  ·
    refine ⟨11370144320552914669734697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60640769709615544905251717 11370144320552914669734697)
    ·
      refine ⟨8527608240414686002301023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11370144320552914669734697 8527608240414686002301023)
      ·
        refine ⟨12791412360622029003451535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8527608240414686002301023 12791412360622029003451535)
        ·
          refine ⟨19187118540933043505177303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12791412360622029003451535 19187118540933043505177303)
          ·
            refine ⟨28780677811399565257765955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19187118540933043505177303 28780677811399565257765955)
            ·
              refine ⟨43171016717099347886648933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28780677811399565257765955 43171016717099347886648933)
              ·
                refine ⟨8094565634456127728746675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43171016717099347886648933 8094565634456127728746675)
                ·
                  refine ⟨12141848451684191593120013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8094565634456127728746675 12141848451684191593120013)
                  ·
                    refine ⟨4553193169381571847420005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12141848451684191593120013 4553193169381571847420005)
                    ·
                      refine ⟨853723719259044721391251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4553193169381571847420005 853723719259044721391251)
                      ·
                        rfl

theorem cell23_1662621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_1662621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662621 prefixEnd_1662621 := by exact prefixLift 1662621
  have htrace : WordTrace (prefixWord ++ tailWord_1662621) baseStart_1662621 baseEnd_1662621 := by
    simpa [prefixWord, tailWord_1662621, baseEnd_1662621] using wordTrace_append hprefix tailTrace_1662621
  have hstable : (prefixWord ++ tailWord_1662621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662621).length < 2 ^ (prefixWord ++ tailWord_1662621).sum := by decide
  have hdescent : baseEnd_1662621 < baseStart_1662621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662728 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_1662728 : Nat := 118140960795 + 1662728 * 2 ^ 59
def prefixEnd_1662728 : Nat := 4983230072969 + 3 ^ 40 * 1662728 * 2
def baseEnd_1662728 : Nat := 853778661689075802753259

theorem tailTrace_1662728 : CollatzResearch.WordTrace tailWord_1662728 prefixEnd_1662728 853778661689075802753259 := by
  unfold tailWord_1662728
  simp only [CollatzResearch.WordTrace]
  refine ⟨30322336160113951089698419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40429781546818601452931225 30322336160113951089698419)
  ·
    refine ⟨45483504240170926634547629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30322336160113951089698419 45483504240170926634547629)
    ·
      refine ⟨17056314090064097487955361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45483504240170926634547629 17056314090064097487955361)
      ·
        refine ⟨12792235567548073115966521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17056314090064097487955361 12792235567548073115966521)
        ·
          refine ⟨9594176675661054836974891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12792235567548073115966521 9594176675661054836974891)
          ·
            refine ⟨14391265013491582255462337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9594176675661054836974891 14391265013491582255462337)
            ·
              refine ⟨10793448760118686691596753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14391265013491582255462337 10793448760118686691596753)
              ·
                refine ⟨8095086570089015018697565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10793448760118686691596753 8095086570089015018697565)
                ·
                  refine ⟨3035657463783380632011587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8095086570089015018697565 3035657463783380632011587)
                  ·
                    refine ⟨4553486195675070948017381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3035657463783380632011587 4553486195675070948017381)
                    ·
                      refine ⟨853778661689075802753259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4553486195675070948017381 853778661689075802753259)
                      ·
                        rfl

theorem cell23_1662728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_1662728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662728 prefixEnd_1662728 := by exact prefixLift 1662728
  have htrace : WordTrace (prefixWord ++ tailWord_1662728) baseStart_1662728 baseEnd_1662728 := by
    simpa [prefixWord, tailWord_1662728, baseEnd_1662728] using wordTrace_append hprefix tailTrace_1662728
  have hstable : (prefixWord ++ tailWord_1662728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662728).length < 2 ^ (prefixWord ++ tailWord_1662728).sum := by decide
  have hdescent : baseEnd_1662728 < baseStart_1662728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662751 : List Nat := [1, 1, 2, 4, 2, 1, 1, 11]
def baseStart_1662751 : Nat := 118140960795 + 1662751 * 2 ^ 59
def prefixEnd_1662751 : Nat := 4983230072969 + 3 ^ 40 * 1662751 * 2
def baseEnd_1662751 : Nat := 31621869323856637509839

theorem tailTrace_1662751 : CollatzResearch.WordTrace tailWord_1662751 prefixEnd_1662751 31621869323856637509839 := by
  unfold tailWord_1662751
  simp only [CollatzResearch.WordTrace]
  refine ⟨60645511199144577107484107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40430340799429718071656071 60645511199144577107484107)
  ·
    refine ⟨90968266798716865661226161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60645511199144577107484107 90968266798716865661226161)
    ·
      refine ⟨68226200099037649245919621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90968266798716865661226161 68226200099037649245919621)
      ·
        refine ⟨12792412518569559233609929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68226200099037649245919621 12792412518569559233609929)
        ·
          refine ⟨9594309388927169425207447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12792412518569559233609929 9594309388927169425207447)
          ·
            refine ⟨14391464083390754137811171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9594309388927169425207447 14391464083390754137811171)
            ·
              refine ⟨21587196125086131206716757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14391464083390754137811171 21587196125086131206716757)
              ·
                refine ⟨31621869323856637509839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 21587196125086131206716757 31621869323856637509839)
                ·
                  rfl

theorem cell23_1662751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 11].length) (baseStart_1662751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662751 prefixEnd_1662751 := by exact prefixLift 1662751
  have htrace : WordTrace (prefixWord ++ tailWord_1662751) baseStart_1662751 baseEnd_1662751 := by
    simpa [prefixWord, tailWord_1662751, baseEnd_1662751] using wordTrace_append hprefix tailTrace_1662751
  have hstable : (prefixWord ++ tailWord_1662751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662751).length < 2 ^ (prefixWord ++ tailWord_1662751).sum := by decide
  have hdescent : baseEnd_1662751 < baseStart_1662751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662772 : List Nat := [2, 5, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_1662772 : Nat := 118140960795 + 1662772 * 2 ^ 59
def prefixEnd_1662772 : Nat := 4983230072969 + 3 ^ 40 * 1662772 * 2
def baseEnd_1662772 : Nat := 284600418279291210201019

theorem tailTrace_1662772 : CollatzResearch.WordTrace tailWord_1662772 prefixEnd_1662772 284600418279291210201019 := by
  unfold tailWord_1662772
  simp only [CollatzResearch.WordTrace]
  refine ⟨30323138566034248846999285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40430851421378998462665713 30323138566034248846999285)
  ·
    refine ⟨2842794240565710829406183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30323138566034248846999285 2842794240565710829406183)
    ·
      refine ⟨4264191360848566244109275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2842794240565710829406183 4264191360848566244109275)
      ·
        refine ⟨6396287041272849366163913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4264191360848566244109275 6396287041272849366163913)
        ·
          refine ⟨4797215280954637024622935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6396287041272849366163913 4797215280954637024622935)
          ·
            refine ⟨7195822921431955536934403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4797215280954637024622935 7195822921431955536934403)
            ·
              refine ⟨10793734382147933305401605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7195822921431955536934403 10793734382147933305401605)
              ·
                refine ⟨2023825196652737494762801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10793734382147933305401605 2023825196652737494762801)
                ·
                  refine ⟨1517868897489553121072101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2023825196652737494762801 1517868897489553121072101)
                  ·
                    refine ⟨284600418279291210201019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1517868897489553121072101 284600418279291210201019)
                    ·
                      rfl

theorem cell23_1662772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_1662772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662772 prefixEnd_1662772 := by exact prefixLift 1662772
  have htrace : WordTrace (prefixWord ++ tailWord_1662772) baseStart_1662772 baseEnd_1662772 := by
    simpa [prefixWord, tailWord_1662772, baseEnd_1662772] using wordTrace_append hprefix tailTrace_1662772
  have hstable : (prefixWord ++ tailWord_1662772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662772).length < 2 ^ (prefixWord ++ tailWord_1662772).sum := by decide
  have hdescent : baseEnd_1662772 < baseStart_1662772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662773 : List Nat := [1, 3, 3, 1, 5, 1, 2, 2, 1, 1, 3]
def baseStart_1662773 : Nat := 118140960795 + 1662773 * 2 ^ 59
def prefixEnd_1662773 : Nat := 4983230072969 + 3 ^ 40 * 1662773 * 2
def baseEnd_1662773 : Nat := 853801768318528126690553

theorem tailTrace_1662773 : CollatzResearch.WordTrace tailWord_1662773 prefixEnd_1662773 853801768318528126690553 := by
  unfold tailWord_1662773
  simp only [CollatzResearch.WordTrace]
  refine ⟨60646313605064874864784973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40430875736709916576523315 60646313605064874864784973)
  ·
    refine ⟨22742367601899328074294365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60646313605064874864784973 22742367601899328074294365)
    ·
      refine ⟨8528387850712248027860387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22742367601899328074294365 8528387850712248027860387)
      ·
        refine ⟨12792581776068372041790581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8528387850712248027860387 12792581776068372041790581)
        ·
          refine ⟨1199304541506409878917867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12792581776068372041790581 1199304541506409878917867)
          ·
            refine ⟨1798956812259614818376801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199304541506409878917867 1798956812259614818376801)
            ·
              refine ⟨1349217609194711113782601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1798956812259614818376801 1349217609194711113782601)
              ·
                refine ⟨1011913206896033335336951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1349217609194711113782601 1011913206896033335336951)
                ·
                  refine ⟨1517869810344050003005427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011913206896033335336951 1517869810344050003005427)
                  ·
                    refine ⟨2276804715516075004508141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1517869810344050003005427 2276804715516075004508141)
                    ·
                      refine ⟨853801768318528126690553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2276804715516075004508141 853801768318528126690553)
                      ·
                        rfl

theorem cell23_1662773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_1662773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662773 prefixEnd_1662773 := by exact prefixLift 1662773
  have htrace : WordTrace (prefixWord ++ tailWord_1662773) baseStart_1662773 baseEnd_1662773 := by
    simpa [prefixWord, tailWord_1662773, baseEnd_1662773] using wordTrace_append hprefix tailTrace_1662773
  have hstable : (prefixWord ++ tailWord_1662773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662773).length < 2 ^ (prefixWord ++ tailWord_1662773).sum := by decide
  have hdescent : baseEnd_1662773 < baseStart_1662773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662828 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 2, 6]
def baseStart_1662828 : Nat := 118140960795 + 1662828 * 2 ^ 59
def prefixEnd_1662828 : Nat := 4983230072969 + 3 ^ 40 * 1662828 * 2
def baseEnd_1662828 : Nat := 284610003251508470500933

theorem tailTrace_1662828 : CollatzResearch.WordTrace tailWord_1662828 prefixEnd_1662828 284610003251508470500933 := by
  unfold tailWord_1662828
  simp only [CollatzResearch.WordTrace]
  refine ⟨30324159809932809629018569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40432213079910412838691425 30324159809932809629018569)
  ·
    refine ⟨22743119857449607221763927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30324159809932809629018569 22743119857449607221763927)
    ·
      refine ⟨34114679786174410832645891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22743119857449607221763927 34114679786174410832645891)
      ·
        refine ⟨51172019679261616248968837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34114679786174410832645891 51172019679261616248968837)
        ·
          refine ⟨9594753689861553046681657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51172019679261616248968837 9594753689861553046681657)
          ·
            refine ⟨7196065267396164785011243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9594753689861553046681657 7196065267396164785011243)
            ·
              refine ⟨10794097901094247177516865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7196065267396164785011243 10794097901094247177516865)
              ·
                refine ⟨8095573425820685383137649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10794097901094247177516865 8095573425820685383137649)
                ·
                  refine ⟨6071680069365514037353237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8095573425820685383137649 6071680069365514037353237)
                  ·
                    refine ⟨284610003251508470500933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6071680069365514037353237 284610003251508470500933)
                    ·
                      rfl

theorem cell23_1662828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_1662828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662828 prefixEnd_1662828 := by exact prefixLift 1662828
  have htrace : WordTrace (prefixWord ++ tailWord_1662828) baseStart_1662828 baseEnd_1662828 := by
    simpa [prefixWord, tailWord_1662828, baseEnd_1662828] using wordTrace_append hprefix tailTrace_1662828
  have hstable : (prefixWord ++ tailWord_1662828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662828).length < 2 ^ (prefixWord ++ tailWord_1662828).sum := by decide
  have hdescent : baseEnd_1662828 < baseStart_1662828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662848 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 4]
def baseStart_1662848 : Nat := 118140960795 + 1662848 * 2 ^ 59
def prefixEnd_1662848 : Nat := 4983230072969 + 3 ^ 40 * 1662848 * 2
def baseEnd_1662848 : Nat := 853840279367615333252707

theorem tailTrace_1662848 : CollatzResearch.WordTrace tailWord_1662848 prefixEnd_1662848 853840279367615333252707 := by
  unfold tailWord_1662848
  simp only [CollatzResearch.WordTrace]
  refine ⟨30324524539896581336882599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40432699386528775115843465 30324524539896581336882599)
  ·
    refine ⟨45486786809844872005323899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30324524539896581336882599 45486786809844872005323899)
    ·
      refine ⟨68230180214767308007985849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45486786809844872005323899 68230180214767308007985849)
      ·
        refine ⟨51172635161075481005989387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68230180214767308007985849 51172635161075481005989387)
        ·
          refine ⟨76758952741613221508984081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51172635161075481005989387 76758952741613221508984081)
          ·
            refine ⟨57569214556209916131738061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76758952741613221508984081 57569214556209916131738061)
            ·
              refine ⟨21588455458578718549401773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57569214556209916131738061 21588455458578718549401773)
              ·
                refine ⟨8095670796967019456025665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21588455458578718549401773 8095670796967019456025665)
                ·
                  refine ⟨6071753097725264592019249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8095670796967019456025665 6071753097725264592019249)
                  ·
                    refine ⟨4553814823293948444014437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6071753097725264592019249 4553814823293948444014437)
                    ·
                      refine ⟨853840279367615333252707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4553814823293948444014437 853840279367615333252707)
                      ·
                        rfl

theorem cell23_1662848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_1662848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662848 prefixEnd_1662848 := by exact prefixLift 1662848
  have htrace : WordTrace (prefixWord ++ tailWord_1662848) baseStart_1662848 baseEnd_1662848 := by
    simpa [prefixWord, tailWord_1662848, baseEnd_1662848] using wordTrace_append hprefix tailTrace_1662848
  have hstable : (prefixWord ++ tailWord_1662848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662848).length < 2 ^ (prefixWord ++ tailWord_1662848).sum := by decide
  have hdescent : baseEnd_1662848 < baseStart_1662848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662852 : List Nat := [2, 3, 2, 1, 1, 1, 5, 1, 1, 4, 2]
def baseStart_1662852 : Nat := 118140960795 + 1662852 * 2 ^ 59
def prefixEnd_1662852 : Nat := 4983230072969 + 3 ^ 40 * 1662852 * 2
def baseEnd_1662852 : Nat := 853842333290233317602689

theorem tailTrace_1662852 : CollatzResearch.WordTrace tailWord_1662852 prefixEnd_1662852 853842333290233317602689 := by
  unfold tailWord_1662852
  simp only [CollatzResearch.WordTrace]
  refine ⟨30324597485889335678455405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40432796647852447571273873 30324597485889335678455405)
  ·
    refine ⟨11371724057208500879420777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30324597485889335678455405 11371724057208500879420777)
    ·
      refine ⟨8528793042906375659565583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11371724057208500879420777 8528793042906375659565583)
      ·
        refine ⟨12793189564359563489348375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8528793042906375659565583 12793189564359563489348375)
        ·
          refine ⟨19189784346539345234022563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12793189564359563489348375 19189784346539345234022563)
          ·
            refine ⟨28784676519809017851033845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19189784346539345234022563 28784676519809017851033845)
            ·
              refine ⟨2698563423732095423534423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28784676519809017851033845 2698563423732095423534423)
              ·
                refine ⟨4047845135598143135301635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2698563423732095423534423 4047845135598143135301635)
                ·
                  refine ⟨6071767703397214702952453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4047845135598143135301635 6071767703397214702952453)
                  ·
                    refine ⟨1138456444386977756803585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6071767703397214702952453 1138456444386977756803585)
                    ·
                      refine ⟨853842333290233317602689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1138456444386977756803585 853842333290233317602689)
                      ·
                        rfl

theorem cell23_1662852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_1662852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662852 prefixEnd_1662852 := by exact prefixLift 1662852
  have htrace : WordTrace (prefixWord ++ tailWord_1662852) baseStart_1662852 baseEnd_1662852 := by
    simpa [prefixWord, tailWord_1662852, baseEnd_1662852] using wordTrace_append hprefix tailTrace_1662852
  have hstable : (prefixWord ++ tailWord_1662852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662852).length < 2 ^ (prefixWord ++ tailWord_1662852).sum := by decide
  have hdescent : baseEnd_1662852 < baseStart_1662852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662872 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 2, 1, 5]
def baseStart_1662872 : Nat := 118140960795 + 1662872 * 2 ^ 59
def prefixEnd_1662872 : Nat := 4983230072969 + 3 ^ 40 * 1662872 * 2
def baseEnd_1662872 : Nat := 853852602903323239352597

theorem tailTrace_1662872 : CollatzResearch.WordTrace tailWord_1662872 prefixEnd_1662872 853852602903323239352597 := by
  unfold tailWord_1662872
  simp only [CollatzResearch.WordTrace]
  refine ⟨30324962215853107386319435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40433282954470809848425913 30324962215853107386319435)
  ·
    refine ⟨45487443323779661079479153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30324962215853107386319435 45487443323779661079479153)
    ·
      refine ⟨34115582492834745809609365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45487443323779661079479153 34115582492834745809609365)
      ·
        refine ⟨1599167929351628709825439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34115582492834745809609365 1599167929351628709825439)
        ·
          refine ⟨2398751894027443064738159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599167929351628709825439 2398751894027443064738159)
          ·
            refine ⟨3598127841041164597107239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2398751894027443064738159 3598127841041164597107239)
            ·
              refine ⟨5397191761561746895660859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3598127841041164597107239 5397191761561746895660859)
              ·
                refine ⟨8095787642342620343491289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5397191761561746895660859 8095787642342620343491289)
                ·
                  refine ⟨6071840731756965257618467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8095787642342620343491289 6071840731756965257618467)
                  ·
                    refine ⟨9107761097635447886427701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6071840731756965257618467 9107761097635447886427701)
                    ·
                      refine ⟨853852602903323239352597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9107761097635447886427701 853852602903323239352597)
                      ·
                        rfl

theorem cell23_1662872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_1662872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662872 prefixEnd_1662872 := by exact prefixLift 1662872
  have htrace : WordTrace (prefixWord ++ tailWord_1662872) baseStart_1662872 baseEnd_1662872 := by
    simpa [prefixWord, tailWord_1662872, baseEnd_1662872] using wordTrace_append hprefix tailTrace_1662872
  have hstable : (prefixWord ++ tailWord_1662872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662872).length < 2 ^ (prefixWord ++ tailWord_1662872).sum := by decide
  have hdescent : baseEnd_1662872 < baseStart_1662872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662895 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 2, 5, 2]
def baseStart_1662895 : Nat := 118140960795 + 1662895 * 2 ^ 59
def prefixEnd_1662895 : Nat := 4983230072969 + 3 ^ 40 * 1662895 * 2
def baseEnd_1662895 : Nat := 853864412958376649364991

theorem tailTrace_1662895 : CollatzResearch.WordTrace tailWord_1662895 prefixEnd_1662895 853864412958376649364991 := by
  unfold tailWord_1662895
  simp only [CollatzResearch.WordTrace]
  refine ⟨60650763310622889700726139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40433842207081926467150759 60650763310622889700726139)
  ·
    refine ⟨90976144965934334551089209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60650763310622889700726139 90976144965934334551089209)
    ·
      refine ⟨68232108724450750913316907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90976144965934334551089209 68232108724450750913316907)
      ·
        refine ⟨102348163086676126369975361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68232108724450750913316907 102348163086676126369975361)
        ·
          refine ⟨76761122315007094777481521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102348163086676126369975361 76761122315007094777481521)
          ·
            refine ⟨57570841736255321083111141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76761122315007094777481521 57570841736255321083111141)
            ·
              refine ⟨10794532825547872703083339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57570841736255321083111141 10794532825547872703083339)
              ·
                refine ⟨16191799238321809054625009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10794532825547872703083339 16191799238321809054625009)
                ·
                  refine ⟨12143849428741356790968757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16191799238321809054625009 12143849428741356790968757)
                  ·
                    refine ⟨1138485883944502199153321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12143849428741356790968757 1138485883944502199153321)
                    ·
                      refine ⟨853864412958376649364991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1138485883944502199153321 853864412958376649364991)
                      ·
                        rfl

theorem cell23_1662895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 5, 2].length) (baseStart_1662895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662895 prefixEnd_1662895 := by exact prefixLift 1662895
  have htrace : WordTrace (prefixWord ++ tailWord_1662895) baseStart_1662895 baseEnd_1662895 := by
    simpa [prefixWord, tailWord_1662895, baseEnd_1662895] using wordTrace_append hprefix tailTrace_1662895
  have hstable : (prefixWord ++ tailWord_1662895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662895).length < 2 ^ (prefixWord ++ tailWord_1662895).sum := by decide
  have hdescent : baseEnd_1662895 < baseStart_1662895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662986 : List Nat := [3, 1, 2, 2, 4, 1, 2, 3, 1, 4]
def baseStart_1662986 : Nat := 118140960795 + 1662986 * 2 ^ 59
def prefixEnd_1662986 : Nat := 4983230072969 + 3 ^ 40 * 1662986 * 2
def baseEnd_1662986 : Nat := 284637046565978597775691

theorem tailTrace_1662986 : CollatzResearch.WordTrace tailWord_1662986 prefixEnd_1662986 284637046565978597775691 := by
  unfold tailWord_1662986
  simp only [CollatzResearch.WordTrace]
  refine ⟨15163520588323303060572203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40436054902195474828192541 15163520588323303060572203)
  ·
    refine ⟨22745280882484954590858305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15163520588323303060572203 22745280882484954590858305)
    ·
      refine ⟨17058960661863715943143729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22745280882484954590858305 17058960661863715943143729)
      ·
        refine ⟨12794220496397786957357797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17058960661863715943143729 12794220496397786957357797)
        ·
          refine ⟨2398916343074585054504587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12794220496397786957357797 2398916343074585054504587)
          ·
            refine ⟨3598374514611877581756881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2398916343074585054504587 3598374514611877581756881)
            ·
              refine ⟨2698780885958908186317661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3598374514611877581756881 2698780885958908186317661)
              ·
                refine ⟨1012042832234590569869123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2698780885958908186317661 1012042832234590569869123)
                ·
                  refine ⟨1518064248351885854803685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1012042832234590569869123 1518064248351885854803685)
                  ·
                    refine ⟨284637046565978597775691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1518064248351885854803685 284637046565978597775691)
                    ·
                      rfl

theorem cell23_1662986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_1662986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662986 prefixEnd_1662986 := by exact prefixLift 1662986
  have htrace : WordTrace (prefixWord ++ tailWord_1662986) baseStart_1662986 baseEnd_1662986 := by
    simpa [prefixWord, tailWord_1662986, baseEnd_1662986] using wordTrace_append hprefix tailTrace_1662986
  have hstable : (prefixWord ++ tailWord_1662986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662986).length < 2 ^ (prefixWord ++ tailWord_1662986).sum := by decide
  have hdescent : baseEnd_1662986 < baseStart_1662986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1662999 : List Nat := [1, 1, 3, 5, 2, 2, 1, 2, 6]
def baseStart_1662999 : Nat := 118140960795 + 1662999 * 2 ^ 59
def prefixEnd_1662999 : Nat := 4983230072969 + 3 ^ 40 * 1662999 * 2
def baseEnd_1662999 : Nat := 94879757216271582496057

theorem tailTrace_1662999 : CollatzResearch.WordTrace tailWord_1662999 prefixEnd_1662999 94879757216271582496057 := by
  unfold tailWord_1662999
  simp only [CollatzResearch.WordTrace]
  refine ⟨60654556502246115462512051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40436371001497410308341367 60654556502246115462512051)
  ·
    refine ⟨90981834753369173193768077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60654556502246115462512051 90981834753369173193768077)
    ·
      refine ⟨34118188032513439947663029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90981834753369173193768077 34118188032513439947663029)
      ·
        refine ⟨3198580128048134995093409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34118188032513439947663029 3198580128048134995093409)
        ·
          refine ⟨2398935096036101246320057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3198580128048134995093409 2398935096036101246320057)
          ·
            refine ⟨1799201322027075934740043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2398935096036101246320057 1799201322027075934740043)
            ·
              refine ⟨2698801983040613902110065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799201322027075934740043 2698801983040613902110065)
              ·
                refine ⟨2024101487280460426582549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2698801983040613902110065 2024101487280460426582549)
                ·
                  refine ⟨94879757216271582496057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2024101487280460426582549 94879757216271582496057)
                  ·
                    rfl

theorem cell23_1662999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 6].length) (baseStart_1662999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1662999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1662999 prefixEnd_1662999 := by exact prefixLift 1662999
  have htrace : WordTrace (prefixWord ++ tailWord_1662999) baseStart_1662999 baseEnd_1662999 := by
    simpa [prefixWord, tailWord_1662999, baseEnd_1662999] using wordTrace_append hprefix tailTrace_1662999
  have hstable : (prefixWord ++ tailWord_1662999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1662999).length < 2 ^ (prefixWord ++ tailWord_1662999).sum := by decide
  have hdescent : baseEnd_1662999 < baseStart_1662999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1662999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663016 : List Nat := [2, 1, 5, 3, 1, 1, 3, 1, 6]
def baseStart_1663016 : Nat := 118140960795 + 1663016 * 2 ^ 59
def prefixEnd_1663016 : Nat := 4983230072969 + 3 ^ 40 * 1663016 * 2
def baseEnd_1663016 : Nat := 94880727124174519550215

theorem tailTrace_1663016 : CollatzResearch.WordTrace tailWord_1663016 prefixEnd_1663016 94880727124174519550215 := by
  unfold tailWord_1663016
  simp only [CollatzResearch.WordTrace]
  refine ⟨30327588271592263682940451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40436784362123018243920601 30327588271592263682940451)
  ·
    refine ⟨45491382407388395524410677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30327588271592263682940451 45491382407388395524410677)
    ·
      refine ⟨4264817100692662080413501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45491382407388395524410677 4264817100692662080413501)
      ·
        refine ⟨1599306412759748280155063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4264817100692662080413501 1599306412759748280155063)
        ·
          refine ⟨2398959619139622420232595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599306412759748280155063 2398959619139622420232595)
          ·
            refine ⟨3598439428709433630348893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2398959619139622420232595 3598439428709433630348893)
            ·
              refine ⟨1349414785766037611380835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3598439428709433630348893 1349414785766037611380835)
              ·
                refine ⟨2024122178649056417071253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1349414785766037611380835 2024122178649056417071253)
                ·
                  refine ⟨94880727124174519550215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2024122178649056417071253 94880727124174519550215)
                  ·
                    rfl

theorem cell23_1663016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 6].length) (baseStart_1663016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663016 prefixEnd_1663016 := by exact prefixLift 1663016
  have htrace : WordTrace (prefixWord ++ tailWord_1663016) baseStart_1663016 baseEnd_1663016 := by
    simpa [prefixWord, tailWord_1663016, baseEnd_1663016] using wordTrace_append hprefix tailTrace_1663016
  have hstable : (prefixWord ++ tailWord_1663016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663016).length < 2 ^ (prefixWord ++ tailWord_1663016).sum := by decide
  have hdescent : baseEnd_1663016 < baseStart_1663016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663045 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 3, 2, 4]
def baseStart_1663045 : Nat := 118140960795 + 1663045 * 2 ^ 59
def prefixEnd_1663045 : Nat := 4983230072969 + 3 ^ 40 * 1663045 * 2
def baseEnd_1663045 : Nat := 853941435056551062489301

theorem tailTrace_1663045 : CollatzResearch.WordTrace tailWord_1663045 prefixEnd_1663045 853941435056551062489301 := by
  unfold tailWord_1663045
  simp only [CollatzResearch.WordTrace]
  refine ⟨60656234260079465318686589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40437489506719643545791059 60656234260079465318686589)
  ·
    refine ⟨22746087847529799494507471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60656234260079465318686589 22746087847529799494507471)
    ·
      refine ⟨34119131771294699241761207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22746087847529799494507471 34119131771294699241761207)
      ·
        refine ⟨51178697656942048862641811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34119131771294699241761207 51178697656942048862641811)
        ·
          refine ⟨76768046485413073293962717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51178697656942048862641811 76768046485413073293962717)
          ·
            refine ⟨28788017432029902485236019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76768046485413073293962717 28788017432029902485236019)
            ·
              refine ⟨43182026148044853727854029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28788017432029902485236019 43182026148044853727854029)
              ·
                refine ⟨16193259805516820147945261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43182026148044853727854029 16193259805516820147945261)
                ·
                  refine ⟨6072472427068807555479473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16193259805516820147945261 6072472427068807555479473)
                  ·
                    refine ⟨4554354320301605666609605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6072472427068807555479473 4554354320301605666609605)
                    ·
                      refine ⟨853941435056551062489301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4554354320301605666609605 853941435056551062489301)
                      ·
                        rfl

theorem cell23_1663045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_1663045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663045 prefixEnd_1663045 := by exact prefixLift 1663045
  have htrace : WordTrace (prefixWord ++ tailWord_1663045) baseStart_1663045 baseEnd_1663045 := by
    simpa [prefixWord, tailWord_1663045, baseEnd_1663045] using wordTrace_append hprefix tailTrace_1663045
  have hstable : (prefixWord ++ tailWord_1663045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663045).length < 2 ^ (prefixWord ++ tailWord_1663045).sum := by decide
  have hdescent : baseEnd_1663045 < baseStart_1663045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663069 : List Nat := [1, 4, 4, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1663069 : Nat := 118140960795 + 1663069 * 2 ^ 59
def prefixEnd_1663069 : Nat := 4983230072969 + 3 ^ 40 * 1663069 * 2
def baseEnd_1663069 : Nat := 853953758592258968589191

theorem tailTrace_1663069 : CollatzResearch.WordTrace tailWord_1663069 prefixEnd_1663069 853953758592258968589191 := by
  unfold tailWord_1663069
  simp only [CollatzResearch.WordTrace]
  refine ⟨60657109611992517417560261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40438073074661678278373507 60657109611992517417560261)
  ·
    refine ⟨11373208052248597015792549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60657109611992517417560261 11373208052248597015792549)
    ·
      refine ⟨2132476509796611940461103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11373208052248597015792549 2132476509796611940461103)
      ·
        refine ⟨3198714764694917910691655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2132476509796611940461103 3198714764694917910691655)
        ·
          refine ⟨4798072147042376866037483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3198714764694917910691655 4798072147042376866037483)
          ·
            refine ⟨7197108220563565299056225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4798072147042376866037483 7197108220563565299056225)
            ·
              refine ⟨5397831165422673974292169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7197108220563565299056225 5397831165422673974292169)
              ·
                refine ⟨4048373374067005480719127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5397831165422673974292169 4048373374067005480719127)
                ·
                  refine ⟨6072560061100508221078691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4048373374067005480719127 6072560061100508221078691)
                  ·
                    refine ⟨9108840091650762331618037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6072560061100508221078691 9108840091650762331618037)
                    ·
                      refine ⟨853953758592258968589191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9108840091650762331618037 853953758592258968589191)
                      ·
                        rfl

theorem cell23_1663069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1663069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663069 prefixEnd_1663069 := by exact prefixLift 1663069
  have htrace : WordTrace (prefixWord ++ tailWord_1663069) baseStart_1663069 baseEnd_1663069 := by
    simpa [prefixWord, tailWord_1663069, baseEnd_1663069] using wordTrace_append hprefix tailTrace_1663069
  have hstable : (prefixWord ++ tailWord_1663069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663069).length < 2 ^ (prefixWord ++ tailWord_1663069).sum := by decide
  have hdescent : baseEnd_1663069 < baseStart_1663069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663122 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1663122 : Nat := 118140960795 + 1663122 * 2 ^ 59
def prefixEnd_1663122 : Nat := 4983230072969 + 3 ^ 40 * 1663122 * 2
def baseEnd_1663122 : Nat := 853980973066947261226447

theorem tailTrace_1663122 : CollatzResearch.WordTrace tailWord_1663122 prefixEnd_1663122 853980973066947261226447 := by
  unfold tailWord_1663122
  simp only [CollatzResearch.WordTrace]
  refine ⟨15164760670200126867309905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40439361787200338312826413 15164760670200126867309905)
  ·
    refine ⟨11373570502650095150482429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15164760670200126867309905 11373570502650095150482429)
    ·
      refine ⟨4265088938493785681430911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11373570502650095150482429 4265088938493785681430911)
      ·
        refine ⟨6397633407740678522146367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4265088938493785681430911 6397633407740678522146367)
        ·
          refine ⟨9596450111611017783219551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6397633407740678522146367 9596450111611017783219551)
          ·
            refine ⟨14394675167416526674829327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9596450111611017783219551 14394675167416526674829327)
            ·
              refine ⟨21592012751124790012243991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14394675167416526674829327 21592012751124790012243991)
              ·
                refine ⟨32388019126687185018365987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21592012751124790012243991 32388019126687185018365987)
                ·
                  refine ⟨48582028690030777527548981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32388019126687185018365987 48582028690030777527548981)
                  ·
                    refine ⟨4554565189690385393207717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48582028690030777527548981 4554565189690385393207717)
                    ·
                      refine ⟨853980973066947261226447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4554565189690385393207717 853980973066947261226447)
                      ·
                        rfl

theorem cell23_1663122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1663122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663122 prefixEnd_1663122 := by exact prefixLift 1663122
  have htrace : WordTrace (prefixWord ++ tailWord_1663122) baseStart_1663122 baseEnd_1663122 := by
    simpa [prefixWord, tailWord_1663122, baseEnd_1663122] using wordTrace_append hprefix tailTrace_1663122
  have hstable : (prefixWord ++ tailWord_1663122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663122).length < 2 ^ (prefixWord ++ tailWord_1663122).sum := by decide
  have hdescent : baseEnd_1663122 < baseStart_1663122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663132 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 2, 6]
def baseStart_1663132 : Nat := 118140960795 + 1663132 * 2 ^ 59
def prefixEnd_1663132 : Nat := 4983230072969 + 3 ^ 40 * 1663132 * 2
def baseEnd_1663132 : Nat := 284662035957830740700467

theorem tailTrace_1663132 : CollatzResearch.WordTrace tailWord_1663132 prefixEnd_1663132 284662035957830740700467 := by
  unfold tailWord_1663132
  simp only [CollatzResearch.WordTrace]
  refine ⟨30329703705382139588551825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40439604940509519451402433 30329703705382139588551825)
  ·
    refine ⟨22747277779036604691413869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30329703705382139588551825 22747277779036604691413869)
    ·
      refine ⟨8530229167138726759280201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22747277779036604691413869 8530229167138726759280201)
      ·
        refine ⟨6397671875354045069460151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8530229167138726759280201 6397671875354045069460151)
        ·
          refine ⟨9596507813031067604190227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6397671875354045069460151 9596507813031067604190227)
          ·
            refine ⟨14394761719546601406285341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9596507813031067604190227 14394761719546601406285341)
            ·
              refine ⟨5398035644829975527357003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14394761719546601406285341 5398035644829975527357003)
              ·
                refine ⟨8097053467244963291035505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5398035644829975527357003 8097053467244963291035505)
                ·
                  refine ⟨6072790100433722468276629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8097053467244963291035505 6072790100433722468276629)
                  ·
                    refine ⟨284662035957830740700467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6072790100433722468276629 284662035957830740700467)
                    ·
                      rfl

theorem cell23_1663132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_1663132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663132 prefixEnd_1663132 := by exact prefixLift 1663132
  have htrace : WordTrace (prefixWord ++ tailWord_1663132) baseStart_1663132 baseEnd_1663132 := by
    simpa [prefixWord, tailWord_1663132, baseEnd_1663132] using wordTrace_append hprefix tailTrace_1663132
  have hstable : (prefixWord ++ tailWord_1663132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663132).length < 2 ^ (prefixWord ++ tailWord_1663132).sum := by decide
  have hdescent : baseEnd_1663132 < baseStart_1663132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663139 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 8, 2, 2]
def baseStart_1663139 : Nat := 118140960795 + 1663139 * 2 ^ 59
def prefixEnd_1663139 : Nat := 4983230072969 + 3 ^ 40 * 1663139 * 2
def baseEnd_1663139 : Nat := 853989702238073694713869

theorem tailTrace_1663139 : CollatzResearch.WordTrace tailWord_1663139 prefixEnd_1663139 853989702238073694713869 := by
  unfold tailWord_1663139
  simp only [CollatzResearch.WordTrace]
  refine ⟨60659662721738919372608471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40439775147825946248405647 60659662721738919372608471)
  ·
    refine ⟨90989494082608379058912707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60659662721738919372608471 90989494082608379058912707)
    ·
      refine ⟨136484241123912568588369061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90989494082608379058912707 136484241123912568588369061)
      ·
        refine ⟨25590795210733606610319199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136484241123912568588369061 25590795210733606610319199)
        ·
          refine ⟨38386192816100409915478799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25590795210733606610319199 38386192816100409915478799)
          ·
            refine ⟨57579289224150614873218199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38386192816100409915478799 57579289224150614873218199)
            ·
              refine ⟨86368933836225922309827299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57579289224150614873218199 86368933836225922309827299)
              ·
                refine ⟨129553400754338883464740949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86368933836225922309827299 129553400754338883464740949)
                ·
                  refine ⟨1518203915089908790602433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 129553400754338883464740949 1518203915089908790602433)
                  ·
                    refine ⟨1138652936317431592951825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1518203915089908790602433 1138652936317431592951825)
                    ·
                      refine ⟨853989702238073694713869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1138652936317431592951825 853989702238073694713869)
                      ·
                        rfl

theorem cell23_1663139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_1663139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663139 prefixEnd_1663139 := by exact prefixLift 1663139
  have htrace : WordTrace (prefixWord ++ tailWord_1663139) baseStart_1663139 baseEnd_1663139 := by
    simpa [prefixWord, tailWord_1663139, baseEnd_1663139] using wordTrace_append hprefix tailTrace_1663139
  have hstable : (prefixWord ++ tailWord_1663139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663139).length < 2 ^ (prefixWord ++ tailWord_1663139).sum := by decide
  have hdescent : baseEnd_1663139 < baseStart_1663139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663155 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 7]
def baseStart_1663155 : Nat := 118140960795 + 1663155 * 2 ^ 59
def prefixEnd_1663155 : Nat := 4983230072969 + 3 ^ 40 * 1663155 * 2
def baseEnd_1663155 : Nat := 853997917928545632113795

theorem tailTrace_1663155 : CollatzResearch.WordTrace tailWord_1663155 prefixEnd_1663155 853997917928545632113795 := by
  unfold tailWord_1663155
  simp only [CollatzResearch.WordTrace]
  refine ⟨60660246289680954105190919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40440164193120636070127279 60660246289680954105190919)
  ·
    refine ⟨90990369434521431157786379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60660246289680954105190919 90990369434521431157786379)
    ·
      refine ⟨136485554151782146736679569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90990369434521431157786379 136485554151782146736679569)
      ·
        refine ⟨102364165613836610052509677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136485554151782146736679569 102364165613836610052509677)
        ·
          refine ⟨38386562105188728769691129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102364165613836610052509677 38386562105188728769691129)
          ·
            refine ⟨28789921578891546577268347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38386562105188728769691129 28789921578891546577268347)
            ·
              refine ⟨43184882368337319865902521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28789921578891546577268347 43184882368337319865902521)
              ·
                refine ⟨32388661776252989899426891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43184882368337319865902521 32388661776252989899426891)
                ·
                  refine ⟨48582992664379484849140337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32388661776252989899426891 48582992664379484849140337)
                  ·
                    refine ⟨36437244498284613636855253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48582992664379484849140337 36437244498284613636855253)
                    ·
                      refine ⟨853997917928545632113795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36437244498284613636855253 853997917928545632113795)
                      ·
                        rfl

theorem cell23_1663155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_1663155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663155 prefixEnd_1663155 := by exact prefixLift 1663155
  have htrace : WordTrace (prefixWord ++ tailWord_1663155) baseStart_1663155 baseEnd_1663155 := by
    simpa [prefixWord, tailWord_1663155, baseEnd_1663155] using wordTrace_append hprefix tailTrace_1663155
  have hstable : (prefixWord ++ tailWord_1663155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663155).length < 2 ^ (prefixWord ++ tailWord_1663155).sum := by decide
  have hdescent : baseEnd_1663155 < baseStart_1663155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663190 : List Nat := [5, 2, 1, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_1663190 : Nat := 118140960795 + 1663190 * 2 ^ 59
def prefixEnd_1663190 : Nat := 4983230072969 + 3 ^ 40 * 1663190 * 2
def baseEnd_1663190 : Nat := 854015889751452995176135

theorem tailTrace_1663190 : CollatzResearch.WordTrace tailWord_1663190 prefixEnd_1663190 854015889751452995176135 := by
  unfold tailWord_1663190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3791345177784634692669689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40441015229702770055143349 3791345177784634692669689)
  ·
    refine ⟨2843508883338476019502267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3791345177784634692669689 2843508883338476019502267)
    ·
      refine ⟨4265263325007714029253401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2843508883338476019502267 4265263325007714029253401)
      ·
        refine ⟨3198947493755785521940051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4265263325007714029253401 3198947493755785521940051)
        ·
          refine ⟨4798421240633678282910077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3198947493755785521940051 4798421240633678282910077)
          ·
            refine ⟨1799407965237629356091279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4798421240633678282910077 1799407965237629356091279)
            ·
              refine ⟨2699111947856444034136919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799407965237629356091279 2699111947856444034136919)
              ·
                refine ⟨4048667921784666051205379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2699111947856444034136919 4048667921784666051205379)
                ·
                  refine ⟨6073001882676999076808069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4048667921784666051205379 6073001882676999076808069)
                  ·
                    refine ⟨1138687853001937326901513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6073001882676999076808069 1138687853001937326901513)
                    ·
                      refine ⟨854015889751452995176135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1138687853001937326901513 854015889751452995176135)
                      ·
                        rfl

theorem cell23_1663190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_1663190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663190 prefixEnd_1663190 := by exact prefixLift 1663190
  have htrace : WordTrace (prefixWord ++ tailWord_1663190) baseStart_1663190 baseEnd_1663190 := by
    simpa [prefixWord, tailWord_1663190, baseEnd_1663190] using wordTrace_append hprefix tailTrace_1663190
  have hstable : (prefixWord ++ tailWord_1663190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663190).length < 2 ^ (prefixWord ++ tailWord_1663190).sum := by decide
  have hdescent : baseEnd_1663190 < baseStart_1663190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663192 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 1, 7]
def baseStart_1663192 : Nat := 118140960795 + 1663192 * 2 ^ 59
def prefixEnd_1663192 : Nat := 4983230072969 + 3 ^ 40 * 1663192 * 2
def baseEnd_1663192 : Nat := 284672305570920662450375

theorem tailTrace_1663192 : CollatzResearch.WordTrace tailWord_1663192 prefixEnd_1663192 284672305570920662450375 := by
  unfold tailWord_1663192
  simp only [CollatzResearch.WordTrace]
  refine ⟨30330797895273454712143915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40441063860364606282858553 30330797895273454712143915)
  ·
    refine ⟨45496196842910182068215873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30330797895273454712143915 45496196842910182068215873)
    ·
      refine ⟨34122147632182636551161905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45496196842910182068215873 34122147632182636551161905)
      ·
        refine ⟨25591610724136977413371429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34122147632182636551161905 25591610724136977413371429)
        ·
          refine ⟨4798427010775683265007143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25591610724136977413371429 4798427010775683265007143)
          ·
            refine ⟨7197640516163524897510715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4798427010775683265007143 7197640516163524897510715)
            ·
              refine ⟨10796460774245287346266073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7197640516163524897510715 10796460774245287346266073)
              ·
                refine ⟨8097345580683965509699555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10796460774245287346266073 8097345580683965509699555)
                ·
                  refine ⟨12146018371025948264549333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8097345580683965509699555 12146018371025948264549333)
                  ·
                    refine ⟨284672305570920662450375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12146018371025948264549333 284672305570920662450375)
                    ·
                      rfl

theorem cell23_1663192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_1663192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663192 prefixEnd_1663192 := by exact prefixLift 1663192
  have htrace : WordTrace (prefixWord ++ tailWord_1663192) baseStart_1663192 baseEnd_1663192 := by
    simpa [prefixWord, tailWord_1663192, baseEnd_1663192] using wordTrace_append hprefix tailTrace_1663192
  have hstable : (prefixWord ++ tailWord_1663192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663192).length < 2 ^ (prefixWord ++ tailWord_1663192).sum := by decide
  have hdescent : baseEnd_1663192 < baseStart_1663192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663212 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 4]
def baseStart_1663212 : Nat := 118140960795 + 1663212 * 2 ^ 59
def prefixEnd_1663212 : Nat := 4983230072969 + 3 ^ 40 * 1663212 * 2
def baseEnd_1663212 : Nat := 854027186325851909101033

theorem tailTrace_1663212 : CollatzResearch.WordTrace tailWord_1663212 prefixEnd_1663212 854027186325851909101033 := by
  unfold tailWord_1663212
  simp only [CollatzResearch.WordTrace]
  refine ⟨30331162625237226420007945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40441550166982968560010593 30331162625237226420007945)
  ·
    refine ⟨22748371968927919815005959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30331162625237226420007945 22748371968927919815005959)
    ·
      refine ⟨34122557953391879722508939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22748371968927919815005959 34122557953391879722508939)
      ·
        refine ⟨51183836930087819583763409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34122557953391879722508939 51183836930087819583763409)
        ·
          refine ⟨38387877697565864687822557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51183836930087819583763409 38387877697565864687822557)
          ·
            refine ⟨14395454136587199257933459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38387877697565864687822557 14395454136587199257933459)
            ·
              refine ⟨21593181204880798886900189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14395454136587199257933459 21593181204880798886900189)
              ·
                refine ⟨8097442951830299582587571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21593181204880798886900189 8097442951830299582587571)
                ·
                  refine ⟨12146164427745449373881357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8097442951830299582587571 12146164427745449373881357)
                  ·
                    refine ⟨4554811660404543515205509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12146164427745449373881357 4554811660404543515205509)
                    ·
                      refine ⟨854027186325851909101033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4554811660404543515205509 854027186325851909101033)
                      ·
                        rfl

theorem cell23_1663212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_1663212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663212 prefixEnd_1663212 := by exact prefixLift 1663212
  have htrace : WordTrace (prefixWord ++ tailWord_1663212) baseStart_1663212 baseEnd_1663212 := by
    simpa [prefixWord, tailWord_1663212, baseEnd_1663212] using wordTrace_append hprefix tailTrace_1663212
  have hstable : (prefixWord ++ tailWord_1663212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663212).length < 2 ^ (prefixWord ++ tailWord_1663212).sum := by decide
  have hdescent : baseEnd_1663212 < baseStart_1663212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663213 : List Nat := [1, 5, 1, 2, 3, 2, 1, 3, 5]
def baseStart_1663213 : Nat := 118140960795 + 1663213 * 2 ^ 59
def prefixEnd_1663213 : Nat := 4983230072969 + 3 ^ 40 * 1663213 * 2
def baseEnd_1663213 : Nat := 94891966645167378354281

theorem tailTrace_1663213 : CollatzResearch.WordTrace tailWord_1663213 prefixEnd_1663213 94891966645167378354281 := by
  unfold tailWord_1663213
  simp only [CollatzResearch.WordTrace]
  refine ⟨60662361723470830010802293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40441574482313886673868195 60662361723470830010802293)
  ·
    refine ⟨5687096411575390313512715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60662361723470830010802293 5687096411575390313512715)
    ·
      refine ⟨8530644617363085470269073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5687096411575390313512715 8530644617363085470269073)
      ·
        refine ⟨6397983463022314102701805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8530644617363085470269073 6397983463022314102701805)
        ·
          refine ⟨2399243798633367788513177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6397983463022314102701805 2399243798633367788513177)
          ·
            refine ⟨1799432848975025841384883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2399243798633367788513177 1799432848975025841384883)
            ·
              refine ⟨2699149273462538762077325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799432848975025841384883 2699149273462538762077325)
              ·
                refine ⟨1012180977548452035778997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2699149273462538762077325 1012180977548452035778997)
                ·
                  refine ⟨94891966645167378354281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1012180977548452035778997 94891966645167378354281)
                  ·
                    rfl

theorem cell23_1663213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_1663213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663213 prefixEnd_1663213 := by exact prefixLift 1663213
  have htrace : WordTrace (prefixWord ++ tailWord_1663213) baseStart_1663213 baseEnd_1663213 := by
    simpa [prefixWord, tailWord_1663213, baseEnd_1663213] using wordTrace_append hprefix tailTrace_1663213
  have hstable : (prefixWord ++ tailWord_1663213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663213).length < 2 ^ (prefixWord ++ tailWord_1663213).sum := by decide
  have hdescent : baseEnd_1663213 < baseStart_1663213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663229 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 4, 4, 2]
def baseStart_1663229 : Nat := 118140960795 + 1663229 * 2 ^ 59
def prefixEnd_1663229 : Nat := 4983230072969 + 3 ^ 40 * 1663229 * 2
def baseEnd_1663229 : Nat := 854035915496978342588455

theorem tailTrace_1663229 : CollatzResearch.WordTrace tailWord_1663229 prefixEnd_1663229 854035915496978342588455 := by
  unfold tailWord_1663229
  simp only [CollatzResearch.WordTrace]
  refine ⟨60662945291412864743384741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40441963527608576495589827 60662945291412864743384741)
  ·
    refine ⟨11374302242139912139384639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60662945291412864743384741 11374302242139912139384639)
    ·
      refine ⟨17061453363209868209076959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11374302242139912139384639 17061453363209868209076959)
      ·
        refine ⟨25592180044814802313615439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17061453363209868209076959 25592180044814802313615439)
        ·
          refine ⟨38388270067222203470423159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25592180044814802313615439 38388270067222203470423159)
          ·
            refine ⟨57582405100833305205634739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38388270067222203470423159 57582405100833305205634739)
            ·
              refine ⟨86373607651249957808452109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57582405100833305205634739 86373607651249957808452109)
              ·
                refine ⟨32390102869218734178169541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86373607651249957808452109 32390102869218734178169541)
                ·
                  refine ⟨6073144287978512658406789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32390102869218734178169541 6073144287978512658406789)
                  ·
                    refine ⟨1138714553995971123451273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6073144287978512658406789 1138714553995971123451273)
                    ·
                      refine ⟨854035915496978342588455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1138714553995971123451273 854035915496978342588455)
                      ·
                        rfl

theorem cell23_1663229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_1663229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663229 prefixEnd_1663229 := by exact prefixLift 1663229
  have htrace : WordTrace (prefixWord ++ tailWord_1663229) baseStart_1663229 baseEnd_1663229 := by
    simpa [prefixWord, tailWord_1663229, baseEnd_1663229] using wordTrace_append hprefix tailTrace_1663229
  have hstable : (prefixWord ++ tailWord_1663229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663229).length < 2 ^ (prefixWord ++ tailWord_1663229).sum := by decide
  have hdescent : baseEnd_1663229 < baseStart_1663229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663242 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_1663242 : Nat := 118140960795 + 1663242 * 2 ^ 59
def prefixEnd_1663242 : Nat := 4983230072969 + 3 ^ 40 * 1663242 * 2
def baseEnd_1663242 : Nat := 854042590745486791725895

theorem tailTrace_1663242 : CollatzResearch.WordTrace tailWord_1663242 prefixEnd_1663242 854042590745486791725895 := by
  unfold tailWord_1663242
  simp only [CollatzResearch.WordTrace]
  refine ⟨15165854860091441990901995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40442279626910511975738653 15165854860091441990901995)
  ·
    refine ⟨22748782290137162986352993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15165854860091441990901995 22748782290137162986352993)
    ·
      refine ⟨17061586717602872239764745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22748782290137162986352993 17061586717602872239764745)
      ·
        refine ⟨12796190038202154179823559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17061586717602872239764745 12796190038202154179823559)
        ·
          refine ⟨19194285057303231269735339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12796190038202154179823559 19194285057303231269735339)
          ·
            refine ⟨28791427585954846904603009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19194285057303231269735339 28791427585954846904603009)
            ·
              refine ⟨21593570689466135178452257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28791427585954846904603009 21593570689466135178452257)
              ·
                refine ⟨16195178017099601383839193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21593570689466135178452257 16195178017099601383839193)
                ·
                  refine ⟨12146383512824701037879395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16195178017099601383839193 12146383512824701037879395)
                  ·
                    refine ⟨18219575269237051556819093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12146383512824701037879395 18219575269237051556819093)
                    ·
                      refine ⟨854042590745486791725895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18219575269237051556819093 854042590745486791725895)
                      ·
                        rfl

theorem cell23_1663242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_1663242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663242 prefixEnd_1663242 := by exact prefixLift 1663242
  have htrace : WordTrace (prefixWord ++ tailWord_1663242) baseStart_1663242 baseEnd_1663242 := by
    simpa [prefixWord, tailWord_1663242, baseEnd_1663242] using wordTrace_append hprefix tailTrace_1663242
  have hstable : (prefixWord ++ tailWord_1663242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663242).length < 2 ^ (prefixWord ++ tailWord_1663242).sum := by decide
  have hdescent : baseEnd_1663242 < baseStart_1663242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663266 : List Nat := [3, 3, 1, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_1663266 : Nat := 118140960795 + 1663266 * 2 ^ 59
def prefixEnd_1663266 : Nat := 4983230072969 + 3 ^ 40 * 1663266 * 2
def baseEnd_1663266 : Nat := 854054914281194697825785

theorem tailTrace_1663266 : CollatzResearch.WordTrace tailWord_1663266 prefixEnd_1663266 854054914281194697825785 := by
  unfold tailWord_1663266
  simp only [CollatzResearch.WordTrace]
  refine ⟨15166073698069705015620413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40442863194852546708321101 15166073698069705015620413)
  ·
    refine ⟨5687277636776139380857655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15166073698069705015620413 5687277636776139380857655)
    ·
      refine ⟨8530916455164209071286483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5687277636776139380857655 8530916455164209071286483)
      ·
        refine ⟨12796374682746313606929725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8530916455164209071286483 12796374682746313606929725)
        ·
          refine ⟨4798640506029867602598647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12796374682746313606929725 4798640506029867602598647)
          ·
            refine ⟨7197960759044801403897971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4798640506029867602598647 7197960759044801403897971)
            ·
              refine ⟨10796941138567202105846957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7197960759044801403897971 10796941138567202105846957)
              ·
                refine ⟨4048852926962700789692609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10796941138567202105846957 4048852926962700789692609)
                ·
                  refine ⟨3036639695222025592269457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4048852926962700789692609 3036639695222025592269457)
                  ·
                    refine ⟨2277479771416519194202093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3036639695222025592269457 2277479771416519194202093)
                    ·
                      refine ⟨854054914281194697825785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2277479771416519194202093 854054914281194697825785)
                      ·
                        rfl

theorem cell23_1663266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_1663266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663266 prefixEnd_1663266 := by exact prefixLift 1663266
  have htrace : WordTrace (prefixWord ++ tailWord_1663266) baseStart_1663266 baseEnd_1663266 := by
    simpa [prefixWord, tailWord_1663266, baseEnd_1663266] using wordTrace_append hprefix tailTrace_1663266
  have hstable : (prefixWord ++ tailWord_1663266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663266).length < 2 ^ (prefixWord ++ tailWord_1663266).sum := by decide
  have hdescent : baseEnd_1663266 < baseStart_1663266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663290 : List Nat := [3, 1, 1, 1, 4, 4, 2, 2, 1, 4]
def baseStart_1663290 : Nat := 118140960795 + 1663290 * 2 ^ 59
def prefixEnd_1663290 : Nat := 4983230072969 + 3 ^ 40 * 1663290 * 2
def baseEnd_1663290 : Nat := 284689079272300867975225

theorem tailTrace_1663290 : CollatzResearch.WordTrace tailWord_1663290 prefixEnd_1663290 284689079272300867975225 := by
  unfold tailWord_1663290
  simp only [CollatzResearch.WordTrace]
  refine ⟨15166292536047968040338831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40443446762794581440903549 15166292536047968040338831)
  ·
    refine ⟨22749438804071952060508247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15166292536047968040338831 22749438804071952060508247)
    ·
      refine ⟨34124158206107928090762371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22749438804071952060508247 34124158206107928090762371)
      ·
        refine ⟨51186237309161892136143557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34124158206107928090762371 51186237309161892136143557)
        ·
          refine ⟨9597419495467854775526917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51186237309161892136143557 9597419495467854775526917)
          ·
            refine ⟨1799516155400222770411297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9597419495467854775526917 1799516155400222770411297)
            ·
              refine ⟨1349637116550167077808473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1799516155400222770411297 1349637116550167077808473)
              ·
                refine ⟨1012227837412625308356355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1349637116550167077808473 1012227837412625308356355)
                ·
                  refine ⟨1518341756118937962534533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1012227837412625308356355 1518341756118937962534533)
                  ·
                    refine ⟨284689079272300867975225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1518341756118937962534533 284689079272300867975225)
                    ·
                      rfl

theorem cell23_1663290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 1, 4].length) (baseStart_1663290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663290 prefixEnd_1663290 := by exact prefixLift 1663290
  have htrace : WordTrace (prefixWord ++ tailWord_1663290) baseStart_1663290 baseEnd_1663290 := by
    simpa [prefixWord, tailWord_1663290, baseEnd_1663290] using wordTrace_append hprefix tailTrace_1663290
  have hstable : (prefixWord ++ tailWord_1663290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663290).length < 2 ^ (prefixWord ++ tailWord_1663290).sum := by decide
  have hdescent : baseEnd_1663290 < baseStart_1663290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663319 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 4]
def baseStart_1663319 : Nat := 118140960795 + 1663319 * 2 ^ 59
def prefixEnd_1663319 : Nat := 4983230072969 + 3 ^ 40 * 1663319 * 2
def baseEnd_1663319 : Nat := 854082128755882990463041

theorem tailTrace_1663319 : CollatzResearch.WordTrace tailWord_1663319 prefixEnd_1663319 854082128755882990463041 := by
  unfold tailWord_1663319
  simp only [CollatzResearch.WordTrace]
  refine ⟨60666227861086810114161011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40444151907391206742774007 60666227861086810114161011)
  ·
    refine ⟨90999341791630215171241517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60666227861086810114161011 90999341791630215171241517)
    ·
      refine ⟨34124753171861330689215569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90999341791630215171241517 34124753171861330689215569)
      ·
        refine ⟨25593564878895998016911677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34124753171861330689215569 25593564878895998016911677)
        ·
          refine ⟨9597586829585999256341879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25593564878895998016911677 9597586829585999256341879)
          ·
            refine ⟨14396380244378998884512819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9597586829585999256341879 14396380244378998884512819)
            ·
              refine ⟨21594570366568498326769229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14396380244378998884512819 21594570366568498326769229)
              ·
                refine ⟨8097963887463186872538461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21594570366568498326769229 8097963887463186872538461)
                ·
                  refine ⟨3036736457798695077201923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8097963887463186872538461 3036736457798695077201923)
                  ·
                    refine ⟨4555104686698042615802885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3036736457798695077201923 4555104686698042615802885)
                    ·
                      refine ⟨854082128755882990463041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4555104686698042615802885 854082128755882990463041)
                      ·
                        rfl

theorem cell23_1663319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_1663319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663319 prefixEnd_1663319 := by exact prefixLift 1663319
  have htrace : WordTrace (prefixWord ++ tailWord_1663319) baseStart_1663319 baseEnd_1663319 := by
    simpa [prefixWord, tailWord_1663319, baseEnd_1663319] using wordTrace_append hprefix tailTrace_1663319
  have hstable : (prefixWord ++ tailWord_1663319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663319).length < 2 ^ (prefixWord ++ tailWord_1663319).sum := by decide
  have hdescent : baseEnd_1663319 < baseStart_1663319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663330 : List Nat := [3, 3, 2, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_1663330 : Nat := 118140960795 + 1663330 * 2 ^ 59
def prefixEnd_1663330 : Nat := 4983230072969 + 3 ^ 40 * 1663330 * 2
def baseEnd_1663330 : Nat := 854087777043082447425491

theorem tailTrace_1663330 : CollatzResearch.WordTrace tailWord_1663330 prefixEnd_1663330 854087777043082447425491 := by
  unfold tailWord_1663330
  simp only [CollatzResearch.WordTrace]
  refine ⟨15166657266011739748202861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40444419376031305995207629 15166657266011739748202861)
  ·
    refine ⟨5687496474754402405576073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15166657266011739748202861 5687496474754402405576073)
    ·
      refine ⟨4265622356065801804182055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5687496474754402405576073 4265622356065801804182055)
      ·
        refine ⟨6398433534098702706273083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4265622356065801804182055 6398433534098702706273083)
        ·
          refine ⟨9597650301148054059409625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6398433534098702706273083 9597650301148054059409625)
          ·
            refine ⟨7198237725861040544557219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9597650301148054059409625 7198237725861040544557219)
            ·
              refine ⟨10797356588791560816835829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7198237725861040544557219 10797356588791560816835829)
              ·
                refine ⟨1012252180199208826578359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10797356588791560816835829 1012252180199208826578359)
                ·
                  refine ⟨1518378270298813239867539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1012252180199208826578359 1518378270298813239867539)
                  ·
                    refine ⟨2277567405448219859801309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1518378270298813239867539 2277567405448219859801309)
                    ·
                      refine ⟨854087777043082447425491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2277567405448219859801309 854087777043082447425491)
                      ·
                        rfl

theorem cell23_1663330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_1663330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663330 prefixEnd_1663330 := by exact prefixLift 1663330
  have htrace : WordTrace (prefixWord ++ tailWord_1663330) baseStart_1663330 baseEnd_1663330 := by
    simpa [prefixWord, tailWord_1663330, baseEnd_1663330] using wordTrace_append hprefix tailTrace_1663330
  have hstable : (prefixWord ++ tailWord_1663330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663330).length < 2 ^ (prefixWord ++ tailWord_1663330).sum := by decide
  have hdescent : baseEnd_1663330 < baseStart_1663330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663333 : List Nat := [1, 3, 1, 3, 1, 5, 2, 1, 1, 5]
def baseStart_1663333 : Nat := 118140960795 + 1663333 * 2 ^ 59
def prefixEnd_1663333 : Nat := 4983230072969 + 3 ^ 40 * 1663333 * 2
def baseEnd_1663333 : Nat := 284696439161681978562659

theorem tailTrace_1663333 : CollatzResearch.WordTrace tailWord_1663333 prefixEnd_1663333 284696439161681978562659 := by
  unfold tailWord_1663333
  simp only [CollatzResearch.WordTrace]
  refine ⟨60666738483036090505170653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40444492322024060336780435 60666738483036090505170653)
  ·
    refine ⟨22750026931138533939438995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60666738483036090505170653 22750026931138533939438995)
    ·
      refine ⟨34125040396707800909158493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22750026931138533939438995 34125040396707800909158493)
      ·
        refine ⟨12796890148765425340934435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34125040396707800909158493 12796890148765425340934435)
        ·
          refine ⟨19195335223148138011401653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12796890148765425340934435 19195335223148138011401653)
          ·
            refine ⟨1799562677170137938568905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19195335223148138011401653 1799562677170137938568905)
            ·
              refine ⟨1349672007877603453926679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1799562677170137938568905 1349672007877603453926679)
              ·
                refine ⟨2024508011816405180890019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1349672007877603453926679 2024508011816405180890019)
                ·
                  refine ⟨3036762017724607771335029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2024508011816405180890019 3036762017724607771335029)
                  ·
                    refine ⟨284696439161681978562659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3036762017724607771335029 284696439161681978562659)
                    ·
                      rfl

theorem cell23_1663333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 1, 5].length) (baseStart_1663333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663333 prefixEnd_1663333 := by exact prefixLift 1663333
  have htrace : WordTrace (prefixWord ++ tailWord_1663333) baseStart_1663333 baseEnd_1663333 := by
    simpa [prefixWord, tailWord_1663333, baseEnd_1663333] using wordTrace_append hprefix tailTrace_1663333
  have hstable : (prefixWord ++ tailWord_1663333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663333).length < 2 ^ (prefixWord ++ tailWord_1663333).sum := by decide
  have hdescent : baseEnd_1663333 < baseStart_1663333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663346 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 4, 4]
def baseStart_1663346 : Nat := 118140960795 + 1663346 * 2 ^ 59
def prefixEnd_1663346 : Nat := 4983230072969 + 3 ^ 40 * 1663346 * 2
def baseEnd_1663346 : Nat := 284698664244518128275139

theorem tailTrace_1663346 : CollatzResearch.WordTrace tailWord_1663346 prefixEnd_1663346 284698664244518128275139 := by
  unfold tailWord_1663346
  simp only [CollatzResearch.WordTrace]
  refine ⟨15166803157997248431348473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40444808421325995816929261 15166803157997248431348473)
  ·
    refine ⟨11375102368497936323511355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15166803157997248431348473 11375102368497936323511355)
    ·
      refine ⟨17062653552746904485267033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11375102368497936323511355 17062653552746904485267033)
      ·
        refine ⟨12796990164560178363950275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17062653552746904485267033 12796990164560178363950275)
        ·
          refine ⟨19195485246840267545925413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12796990164560178363950275 19195485246840267545925413)
          ·
            refine ⟨3599153483782550164861015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19195485246840267545925413 3599153483782550164861015)
            ·
              refine ⟨5398730225673825247291523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3599153483782550164861015 5398730225673825247291523)
              ·
                refine ⟨8098095338510737870937285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5398730225673825247291523 8098095338510737870937285)
                ·
                  refine ⟨1518392875970763350800741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8098095338510737870937285 1518392875970763350800741)
                  ·
                    refine ⟨284698664244518128275139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1518392875970763350800741 284698664244518128275139)
                    ·
                      rfl

theorem cell23_1663346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_1663346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663346 prefixEnd_1663346 := by exact prefixLift 1663346
  have htrace : WordTrace (prefixWord ++ tailWord_1663346) baseStart_1663346 baseEnd_1663346 := by
    simpa [prefixWord, tailWord_1663346, baseEnd_1663346] using wordTrace_append hprefix tailTrace_1663346
  have hstable : (prefixWord ++ tailWord_1663346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663346).length < 2 ^ (prefixWord ++ tailWord_1663346).sum := by decide
  have hdescent : baseEnd_1663346 < baseStart_1663346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663363 : List Nat := [1, 1, 1, 3, 7, 1, 1, 1, 1, 6]
def baseStart_1663363 : Nat := 118140960795 + 1663363 * 2 ^ 59
def prefixEnd_1663363 : Nat := 4983230072969 + 3 ^ 40 * 1663363 * 2
def baseEnd_1663363 : Nat := 284701573968226939437613

theorem tailTrace_1663363 : CollatzResearch.WordTrace tailWord_1663363 prefixEnd_1663363 284701573968226939437613 := by
  unfold tailWord_1663363
  simp only [CollatzResearch.WordTrace]
  refine ⟨60667832672927405628762743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40445221781951603752508495 60667832672927405628762743)
  ·
    refine ⟨91001749009391108443144115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60667832672927405628762743 91001749009391108443144115)
    ·
      refine ⟨136502623514086662664716173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91001749009391108443144115 136502623514086662664716173)
      ·
        refine ⟨51188483817782498499268565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136502623514086662664716173 51188483817782498499268565)
        ·
          refine ⟨1199730089479277308576607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 51188483817782498499268565 1199730089479277308576607)
          ·
            refine ⟨1799595134218915962864911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199730089479277308576607 1799595134218915962864911)
            ·
              refine ⟨2699392701328373944297367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799595134218915962864911 2699392701328373944297367)
              ·
                refine ⟨4049089051992560916446051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2699392701328373944297367 4049089051992560916446051)
                ·
                  refine ⟨6073633577988841374669077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4049089051992560916446051 6073633577988841374669077)
                  ·
                    refine ⟨284701573968226939437613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6073633577988841374669077 284701573968226939437613)
                    ·
                      rfl

theorem cell23_1663363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 1, 6].length) (baseStart_1663363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663363 prefixEnd_1663363 := by exact prefixLift 1663363
  have htrace : WordTrace (prefixWord ++ tailWord_1663363) baseStart_1663363 baseEnd_1663363 := by
    simpa [prefixWord, tailWord_1663363, baseEnd_1663363] using wordTrace_append hprefix tailTrace_1663363
  have hstable : (prefixWord ++ tailWord_1663363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663363).length < 2 ^ (prefixWord ++ tailWord_1663363).sum := by decide
  have hdescent : baseEnd_1663363 < baseStart_1663363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663370 : List Nat := [3, 1, 2, 5, 1, 1, 2, 2, 1, 1, 4]
def baseStart_1663370 : Nat := 118140960795 + 1663370 * 2 ^ 59
def prefixEnd_1663370 : Nat := 4983230072969 + 3 ^ 40 * 1663370 * 2
def baseEnd_1663370 : Nat := 854108316269262290925307

theorem tailTrace_1663370 : CollatzResearch.WordTrace tailWord_1663370 prefixEnd_1663370 854108316269262290925307 := by
  unfold tailWord_1663370
  simp only [CollatzResearch.WordTrace]
  refine ⟨15167021995975511456066891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40445391989268030549511709 15167021995975511456066891)
  ·
    refine ⟨22750532993963267184100337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15167021995975511456066891 22750532993963267184100337)
    ·
      refine ⟨17062899745472450388075253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22750532993963267184100337 17062899745472450388075253)
      ·
        refine ⟨1599646851138042223882055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17062899745472450388075253 1599646851138042223882055)
        ·
          refine ⟨2399470276707063335823083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599646851138042223882055 2399470276707063335823083)
          ·
            refine ⟨3599205415060595003734625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399470276707063335823083 3599205415060595003734625)
            ·
              refine ⟨2699404061295446252800969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3599205415060595003734625 2699404061295446252800969)
              ·
                refine ⟨2024553045971584689600727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2699404061295446252800969 2024553045971584689600727)
                ·
                  refine ⟨3036829568957377034401091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2024553045971584689600727 3036829568957377034401091)
                  ·
                    refine ⟨4555244353436065551601637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3036829568957377034401091 4555244353436065551601637)
                    ·
                      refine ⟨854108316269262290925307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4555244353436065551601637 854108316269262290925307)
                      ·
                        rfl

theorem cell23_1663370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_1663370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663370 prefixEnd_1663370 := by exact prefixLift 1663370
  have htrace : WordTrace (prefixWord ++ tailWord_1663370) baseStart_1663370 baseEnd_1663370 := by
    simpa [prefixWord, tailWord_1663370, baseEnd_1663370] using wordTrace_append hprefix tailTrace_1663370
  have hstable : (prefixWord ++ tailWord_1663370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663370).length < 2 ^ (prefixWord ++ tailWord_1663370).sum := by decide
  have hdescent : baseEnd_1663370 < baseStart_1663370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663390 : List Nat := [4, 3, 1, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_1663390 : Nat := 118140960795 + 1663390 * 2 ^ 59
def prefixEnd_1663390 : Nat := 4983230072969 + 3 ^ 40 * 1663390 * 2
def baseEnd_1663390 : Nat := 854118585882352212675215

theorem tailTrace_1663390 : CollatzResearch.WordTrace tailWord_1663390 prefixEnd_1663390 854118585882352212675215 := by
  unfold tailWord_1663390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7583602180478698654999453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40445878295886392826663749 7583602180478698654999453)
  ·
    refine ⟨2843850817679511995624795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7583602180478698654999453 2843850817679511995624795)
    ·
      refine ⟨4265776226519267993437193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2843850817679511995624795 4265776226519267993437193)
      ·
        refine ⟨3199332169889450995077895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4265776226519267993437193 3199332169889450995077895)
        ·
          refine ⟨4798998254834176492616843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3199332169889450995077895 4798998254834176492616843)
          ·
            refine ⟨7198497382251264738925265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4798998254834176492616843 7198497382251264738925265)
            ·
              refine ⟨5398873036688448554193949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7198497382251264738925265 5398873036688448554193949)
              ·
                refine ⟨2024577388758168207822731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5398873036688448554193949 2024577388758168207822731)
                ·
                  refine ⟨3036866083137252311734097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2024577388758168207822731 3036866083137252311734097)
                  ·
                    refine ⟨2277649562352939233800573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3036866083137252311734097 2277649562352939233800573)
                    ·
                      refine ⟨854118585882352212675215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2277649562352939233800573 854118585882352212675215)
                      ·
                        rfl

theorem cell23_1663390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_1663390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663390 prefixEnd_1663390 := by exact prefixLift 1663390
  have htrace : WordTrace (prefixWord ++ tailWord_1663390) baseStart_1663390 baseEnd_1663390 := by
    simpa [prefixWord, tailWord_1663390, baseEnd_1663390] using wordTrace_append hprefix tailTrace_1663390
  have hstable : (prefixWord ++ tailWord_1663390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663390).length < 2 ^ (prefixWord ++ tailWord_1663390).sum := by decide
  have hdescent : baseEnd_1663390 < baseStart_1663390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663393 : List Nat := [1, 2, 3, 5, 2, 1, 9]
def baseStart_1663393 : Nat := 118140960795 + 1663393 * 2 ^ 59
def prefixEnd_1663393 : Nat := 4983230072969 + 3 ^ 40 * 1663393 * 2
def baseEnd_1663393 : Nat := 10544692917584144456021

theorem tailTrace_1663393 : CollatzResearch.WordTrace tailWord_1663393 prefixEnd_1663393 10544692917584144456021 := by
  unfold tailWord_1663393
  simp only [CollatzResearch.WordTrace]
  refine ⟨60668926862818720752354833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40445951241879147168236555 60668926862818720752354833)
  ·
    refine ⟨45501695147114040564266125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60668926862818720752354833 45501695147114040564266125)
    ·
      refine ⟨17063135680167765211599797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45501695147114040564266125 17063135680167765211599797)
      ·
        refine ⟨1599668970015727988587481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17063135680167765211599797 1599668970015727988587481)
        ·
          refine ⟨1199751727511795991440611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1599668970015727988587481 1199751727511795991440611)
          ·
            refine ⟨1799627591267693987160917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199751727511795991440611 1799627591267693987160917)
            ·
              refine ⟨10544692917584144456021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1799627591267693987160917 10544692917584144456021)
              ·
                rfl

theorem cell23_1663393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 9].length) (baseStart_1663393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663393 prefixEnd_1663393 := by exact prefixLift 1663393
  have htrace : WordTrace (prefixWord ++ tailWord_1663393) baseStart_1663393 baseEnd_1663393 := by
    simpa [prefixWord, tailWord_1663393, baseEnd_1663393] using wordTrace_append hprefix tailTrace_1663393
  have hstable : (prefixWord ++ tailWord_1663393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663393).length < 2 ^ (prefixWord ++ tailWord_1663393).sum := by decide
  have hdescent : baseEnd_1663393 < baseStart_1663393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663420 : List Nat := [2, 2, 2, 4, 1, 2, 1, 3, 2, 1, 3]
def baseStart_1663420 : Nat := 118140960795 + 1663420 * 2 ^ 59
def prefixEnd_1663420 : Nat := 4983230072969 + 3 ^ 40 * 1663420 * 2
def baseEnd_1663420 : Nat := 854133990301987095300077

theorem tailTrace_1663420 : CollatzResearch.WordTrace tailWord_1663420 prefixEnd_1663420 854133990301987095300077 := by
  unfold tailWord_1663420
  simp only [CollatzResearch.WordTrace]
  refine ⟨30334955816860452181793857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40446607755813936242391809 30334955816860452181793857)
  ·
    refine ⟨22751216862645339136345393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30334955816860452181793857 22751216862645339136345393)
    ·
      refine ⟨17063412646984004352259045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22751216862645339136345393 17063412646984004352259045)
      ·
        refine ⟨3199389871309500816048571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17063412646984004352259045 3199389871309500816048571)
        ·
          refine ⟨4799084806964251224072857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3199389871309500816048571 4799084806964251224072857)
          ·
            refine ⟨3599313605223188418054643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4799084806964251224072857 3599313605223188418054643)
            ·
              refine ⟨5398970407834782627081965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3599313605223188418054643 5398970407834782627081965)
              ·
                refine ⟨2024613902938043485155737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5398970407834782627081965 2024613902938043485155737)
                ·
                  refine ⟨1518460427203532613866803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2024613902938043485155737 1518460427203532613866803)
                  ·
                    refine ⟨2277690640805298920800205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1518460427203532613866803 2277690640805298920800205)
                    ·
                      refine ⟨854133990301987095300077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2277690640805298920800205 854133990301987095300077)
                      ·
                        rfl

theorem cell23_1663420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_1663420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663420 prefixEnd_1663420 := by exact prefixLift 1663420
  have htrace : WordTrace (prefixWord ++ tailWord_1663420) baseStart_1663420 baseEnd_1663420 := by
    simpa [prefixWord, tailWord_1663420, baseEnd_1663420] using wordTrace_append hprefix tailTrace_1663420
  have hstable : (prefixWord ++ tailWord_1663420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663420).length < 2 ^ (prefixWord ++ tailWord_1663420).sum := by decide
  have hdescent : baseEnd_1663420 < baseStart_1663420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663439 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 4]
def baseStart_1663439 : Nat := 118140960795 + 1663439 * 2 ^ 59
def prefixEnd_1663439 : Nat := 4983230072969 + 3 ^ 40 * 1663439 * 2
def baseEnd_1663439 : Nat := 854143746434422520962489

theorem tailTrace_1663439 : CollatzResearch.WordTrace tailWord_1663439 prefixEnd_1663439 854143746434422520962489 := by
  unfold tailWord_1663439
  simp only [CollatzResearch.WordTrace]
  refine ⟨60670604620652070608529371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40447069747101380405686247 60670604620652070608529371)
  ·
    refine ⟨91005906930978105912794057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60670604620652070608529371 91005906930978105912794057)
    ·
      refine ⟨68254430198233579434595543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91005906930978105912794057 68254430198233579434595543)
      ·
        refine ⟨102381645297350369151893315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68254430198233579434595543 102381645297350369151893315)
        ·
          refine ⟨153572467946025553727839973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102381645297350369151893315 153572467946025553727839973)
          ·
            refine ⟨28794837739879791323969995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153572467946025553727839973 28794837739879791323969995)
            ·
              refine ⟨43192256609819686985954993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28794837739879791323969995 43192256609819686985954993)
              ·
                refine ⟨32394192457364765239466245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43192256609819686985954993 32394192457364765239466245)
                ·
                  refine ⟨6073911085755893482399921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32394192457364765239466245 6073911085755893482399921)
                  ·
                    refine ⟨4555433314316920111799941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6073911085755893482399921 4555433314316920111799941)
                    ·
                      refine ⟨854143746434422520962489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4555433314316920111799941 854143746434422520962489)
                      ·
                        rfl

theorem cell23_1663439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_1663439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663439 prefixEnd_1663439 := by exact prefixLift 1663439
  have htrace : WordTrace (prefixWord ++ tailWord_1663439) baseStart_1663439 baseEnd_1663439 := by
    simpa [prefixWord, tailWord_1663439, baseEnd_1663439] using wordTrace_append hprefix tailTrace_1663439
  have hstable : (prefixWord ++ tailWord_1663439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663439).length < 2 ^ (prefixWord ++ tailWord_1663439).sum := by decide
  have hdescent : baseEnd_1663439 < baseStart_1663439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663477 : List Nat := [1, 3, 5, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_1663477 : Nat := 118140960795 + 1663477 * 2 ^ 59
def prefixEnd_1663477 : Nat := 4983230072969 + 3 ^ 40 * 1663477 * 2
def baseEnd_1663477 : Nat := 854163258699293372287315

theorem tailTrace_1663477 : CollatzResearch.WordTrace tailWord_1663477 prefixEnd_1663477 854163258699293372287315 := by
  unfold tailWord_1663477
  simp only [CollatzResearch.WordTrace]
  refine ⟨60671990594514403098412685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40447993729676268732275123 60671990594514403098412685)
  ·
    refine ⟨22751996472942901161904757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60671990594514403098412685 22751996472942901161904757)
    ·
      refine ⟨2132999669338396983928571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22751996472942901161904757 2132999669338396983928571)
      ·
        refine ⟨3199499504007595475892857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2132999669338396983928571 3199499504007595475892857)
        ·
          refine ⟨2399624628005696606919643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3199499504007595475892857 2399624628005696606919643)
          ·
            refine ⟨3599436942008544910379465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399624628005696606919643 3599436942008544910379465)
            ·
              refine ⟨2699577706506408682784599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3599436942008544910379465 2699577706506408682784599)
              ·
                refine ⟨4049366559759613024176899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2699577706506408682784599 4049366559759613024176899)
                ·
                  refine ⟨6074049839639419536265349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4049366559759613024176899 6074049839639419536265349)
                  ·
                    refine ⟨1138884344932391163049753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6074049839639419536265349 1138884344932391163049753)
                    ·
                      refine ⟨854163258699293372287315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1138884344932391163049753 854163258699293372287315)
                      ·
                        rfl

theorem cell23_1663477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_1663477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663477 prefixEnd_1663477 := by exact prefixLift 1663477
  have htrace : WordTrace (prefixWord ++ tailWord_1663477) baseStart_1663477 baseEnd_1663477 := by
    simpa [prefixWord, tailWord_1663477, baseEnd_1663477] using wordTrace_append hprefix tailTrace_1663477
  have hstable : (prefixWord ++ tailWord_1663477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663477).length < 2 ^ (prefixWord ++ tailWord_1663477).sum := by decide
  have hdescent : baseEnd_1663477 < baseStart_1663477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663494 : List Nat := [6, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_1663494 : Nat := 118140960795 + 1663494 * 2 ^ 59
def prefixEnd_1663494 : Nat := 4983230072969 + 3 ^ 40 * 1663494 * 2
def baseEnd_1663494 : Nat := 854171987870419805774737

theorem tailTrace_1663494 : CollatzResearch.WordTrace tailWord_1663494 prefixEnd_1663494 854171987870419805774737 := by
  unfold tailWord_1663494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1896019082357900468805673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40448407090301876667854357 1896019082357900468805673)
  ·
    refine ⟨1422014311768425351604255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1896019082357900468805673 1422014311768425351604255)
    ·
      refine ⟨2133021467652638027406383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1422014311768425351604255 2133021467652638027406383)
      ·
        refine ⟨3199532201478957041109575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2133021467652638027406383 3199532201478957041109575)
        ·
          refine ⟨4799298302218435561664363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3199532201478957041109575 4799298302218435561664363)
          ·
            refine ⟨7198947453327653342496545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4799298302218435561664363 7198947453327653342496545)
            ·
              refine ⟨5399210589995740006872409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7198947453327653342496545 5399210589995740006872409)
              ·
                refine ⟨4049407942496805005154307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5399210589995740006872409 4049407942496805005154307)
                ·
                  refine ⟨6074111913745207507731461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4049407942496805005154307 6074111913745207507731461)
                  ·
                    refine ⟨1138895983827226407699649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6074111913745207507731461 1138895983827226407699649)
                    ·
                      refine ⟨854171987870419805774737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1138895983827226407699649 854171987870419805774737)
                      ·
                        rfl

theorem cell23_1663494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_1663494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663494 prefixEnd_1663494 := by exact prefixLift 1663494
  have htrace : WordTrace (prefixWord ++ tailWord_1663494) baseStart_1663494 baseEnd_1663494 := by
    simpa [prefixWord, tailWord_1663494, baseEnd_1663494] using wordTrace_append hprefix tailTrace_1663494
  have hstable : (prefixWord ++ tailWord_1663494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663494).length < 2 ^ (prefixWord ++ tailWord_1663494).sum := by decide
  have hdescent : baseEnd_1663494 < baseStart_1663494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663511 : List Nat := [1, 1, 3, 6, 2, 1, 1, 2, 2, 2, 2]
def baseStart_1663511 : Nat := 118140960795 + 1663511 * 2 ^ 59
def prefixEnd_1663511 : Nat := 4983230072969 + 3 ^ 40 * 1663511 * 2
def baseEnd_1663511 : Nat := 854180717041546239262159

theorem tailTrace_1663511 : CollatzResearch.WordTrace tailWord_1663511 prefixEnd_1663511 854180717041546239262159 := by
  unfold tailWord_1663511
  simp only [CollatzResearch.WordTrace]
  refine ⟨60673230676391226905150387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40448820450927484603433591 60673230676391226905150387)
  ·
    refine ⟨91009846014586840357725581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60673230676391226905150387 91009846014586840357725581)
    ·
      refine ⟨34128692255470065134147093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91009846014586840357725581 34128692255470065134147093)
      ·
        refine ⟨1599782449475159303163145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34128692255470065134147093 1599782449475159303163145)
        ·
          refine ⟨1199836837106369477372359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1599782449475159303163145 1199836837106369477372359)
          ·
            refine ⟨1799755255659554216058539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199836837106369477372359 1799755255659554216058539)
            ·
              refine ⟨2699632883489331324087809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799755255659554216058539 2699632883489331324087809)
              ·
                refine ⟨2024724662616998493065857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2699632883489331324087809 2024724662616998493065857)
                ·
                  refine ⟨1518543496962748869799393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2024724662616998493065857 1518543496962748869799393)
                  ·
                    refine ⟨1138907622722061652349545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1518543496962748869799393 1138907622722061652349545)
                    ·
                      refine ⟨854180717041546239262159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1138907622722061652349545 854180717041546239262159)
                      ·
                        rfl

theorem cell23_1663511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_1663511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663511 prefixEnd_1663511 := by exact prefixLift 1663511
  have htrace : WordTrace (prefixWord ++ tailWord_1663511) baseStart_1663511 baseEnd_1663511 := by
    simpa [prefixWord, tailWord_1663511, baseEnd_1663511] using wordTrace_append hprefix tailTrace_1663511
  have hstable : (prefixWord ++ tailWord_1663511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663511).length < 2 ^ (prefixWord ++ tailWord_1663511).sum := by decide
  have hdescent : baseEnd_1663511 < baseStart_1663511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663536 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 3]
def baseStart_1663536 : Nat := 118140960795 + 1663536 * 2 ^ 59
def prefixEnd_1663536 : Nat := 4983230072969 + 3 ^ 40 * 1663536 * 2
def baseEnd_1663536 : Nat := 854193554057908641449543

theorem tailTrace_1663536 : CollatzResearch.WordTrace tailWord_1663536 prefixEnd_1663536 854193554057908641449543 := by
  unfold tailWord_1663536
  simp only [CollatzResearch.WordTrace]
  refine ⟨30337071250650328087405231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40449428334200437449873641 30337071250650328087405231)
  ·
    refine ⟨45505606875975492131107847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30337071250650328087405231 45505606875975492131107847)
    ·
      refine ⟨68258410313963238196661771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45505606875975492131107847 68258410313963238196661771)
      ·
        refine ⟨102387615470944857294992657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68258410313963238196661771 102387615470944857294992657)
        ·
          refine ⟨76790711603208642971244493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102387615470944857294992657 76790711603208642971244493)
          ·
            refine ⟨28796516851203241114216685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76790711603208642971244493 28796516851203241114216685)
            ·
              refine ⟨10798693819201215417831257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28796516851203241114216685 10798693819201215417831257)
              ·
                refine ⟨8099020364400911563373443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10798693819201215417831257 8099020364400911563373443)
                ·
                  refine ⟨12148530546601367345060165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8099020364400911563373443 12148530546601367345060165)
                  ·
                    refine ⟨2277849477487756377198781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12148530546601367345060165 2277849477487756377198781)
                    ·
                      refine ⟨854193554057908641449543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2277849477487756377198781 854193554057908641449543)
                      ·
                        rfl

theorem cell23_1663536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 3].length) (baseStart_1663536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663536 prefixEnd_1663536 := by exact prefixLift 1663536
  have htrace : WordTrace (prefixWord ++ tailWord_1663536) baseStart_1663536 baseEnd_1663536 := by
    simpa [prefixWord, tailWord_1663536, baseEnd_1663536] using wordTrace_append hprefix tailTrace_1663536
  have hstable : (prefixWord ++ tailWord_1663536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663536).length < 2 ^ (prefixWord ++ tailWord_1663536).sum := by decide
  have hdescent : baseEnd_1663536 < baseStart_1663536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663553 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_1663553 : Nat := 118140960795 + 1663553 * 2 ^ 59
def prefixEnd_1663553 : Nat := 4983230072969 + 3 ^ 40 * 1663553 * 2
def baseEnd_1663553 : Nat := 854202283229035074936965

theorem tailTrace_1663553 : CollatzResearch.WordTrace tailWord_1663553 prefixEnd_1663553 854202283229035074936965 := by
  unfold tailWord_1663553
  simp only [CollatzResearch.WordTrace]
  refine ⟨60674762542239068078179313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40449841694826045385452875 60674762542239068078179313)
  ·
    refine ⟨45506071906679301058634485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60674762542239068078179313 45506071906679301058634485)
    ·
      refine ⟨4266194241251184474246983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45506071906679301058634485 4266194241251184474246983)
      ·
        refine ⟨6399291361876776711370475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4266194241251184474246983 6399291361876776711370475)
        ·
          refine ⟨9598937042815165067055713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6399291361876776711370475 9598937042815165067055713)
          ·
            refine ⟨7199202782111373800291785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9598937042815165067055713 7199202782111373800291785)
            ·
              refine ⟨5399402086583530350218839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7199202782111373800291785 5399402086583530350218839)
              ·
                refine ⟨8099103129875295525328259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5399402086583530350218839 8099103129875295525328259)
                ·
                  refine ⟨12148654694812943287992389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8099103129875295525328259 12148654694812943287992389)
                  ·
                    refine ⟨2277872755277426866498573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12148654694812943287992389 2277872755277426866498573)
                    ·
                      refine ⟨854202283229035074936965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2277872755277426866498573 854202283229035074936965)
                      ·
                        rfl

theorem cell23_1663553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_1663553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663553 prefixEnd_1663553 := by exact prefixLift 1663553
  have htrace : WordTrace (prefixWord ++ tailWord_1663553) baseStart_1663553 baseEnd_1663553 := by
    simpa [prefixWord, tailWord_1663553, baseEnd_1663553] using wordTrace_append hprefix tailTrace_1663553
  have hstable : (prefixWord ++ tailWord_1663553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663553).length < 2 ^ (prefixWord ++ tailWord_1663553).sum := by decide
  have hdescent : baseEnd_1663553 < baseStart_1663553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663593 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 6, 3, 2]
def baseStart_1663593 : Nat := 118140960795 + 1663593 * 2 ^ 59
def prefixEnd_1663593 : Nat := 4983230072969 + 3 ^ 40 * 1663593 * 2
def baseEnd_1663593 : Nat := 854222822455214918436781

theorem tailTrace_1663593 : CollatzResearch.WordTrace tailWord_1663593 prefixEnd_1663593 854222822455214918436781 := by
  unfold tailWord_1663593
  simp only [CollatzResearch.WordTrace]
  refine ⟨60676221462094154909635433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40450814308062769939756955 60676221462094154909635433)
  ·
    refine ⟨45507166096570616182226575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60676221462094154909635433 45507166096570616182226575)
    ·
      refine ⟨68260749144855924273339863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45507166096570616182226575 68260749144855924273339863)
      ·
        refine ⟨102391123717283886410009795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68260749144855924273339863 102391123717283886410009795)
        ·
          refine ⟨153586685575925829615014693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102391123717283886410009795 153586685575925829615014693)
          ·
            refine ⟨28797503545486093052815255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153586685575925829615014693 28797503545486093052815255)
            ·
              refine ⟨43196255318229139579222883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28797503545486093052815255 43196255318229139579222883)
              ·
                refine ⟨64794382977343709368834325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43196255318229139579222883 64794382977343709368834325)
                ·
                  refine ⟨3037236702062986376664109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64794382977343709368834325 3037236702062986376664109)
                  ·
                    refine ⟨1138963763273619891249041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3037236702062986376664109 1138963763273619891249041)
                    ·
                      refine ⟨854222822455214918436781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1138963763273619891249041 854222822455214918436781)
                      ·
                        rfl

theorem cell23_1663593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 3, 2].length) (baseStart_1663593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663593 prefixEnd_1663593 := by exact prefixLift 1663593
  have htrace : WordTrace (prefixWord ++ tailWord_1663593) baseStart_1663593 baseEnd_1663593 := by
    simpa [prefixWord, tailWord_1663593, baseEnd_1663593] using wordTrace_append hprefix tailTrace_1663593
  have hstable : (prefixWord ++ tailWord_1663593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663593).length < 2 ^ (prefixWord ++ tailWord_1663593).sum := by decide
  have hdescent : baseEnd_1663593 < baseStart_1663593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663616 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 3, 6]
def baseStart_1663616 : Nat := 118140960795 + 1663616 * 2 ^ 59
def prefixEnd_1663616 : Nat := 4983230072969 + 3 ^ 40 * 1663616 * 2
def baseEnd_1663616 : Nat := 284744877503422776149725

theorem tailTrace_1663616 : CollatzResearch.WordTrace tailWord_1663616 prefixEnd_1663616 284744877503422776149725 := by
  unfold tailWord_1663616
  simp only [CollatzResearch.WordTrace]
  refine ⟨30338530170505414918861351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40451373560673886558481801 30338530170505414918861351)
  ·
    refine ⟨45507795255758122378292027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30338530170505414918861351 45507795255758122378292027)
    ·
      refine ⟨68261692883637183567438041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45507795255758122378292027 68261692883637183567438041)
      ·
        refine ⟨51196269662727887675578531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68261692883637183567438041 51196269662727887675578531)
        ·
          refine ⟨76794404494091831513367797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51196269662727887675578531 76794404494091831513367797)
          ·
            refine ⟨7199475421321109204378231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76794404494091831513367797 7199475421321109204378231)
            ·
              refine ⟨10799213131981663806567347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7199475421321109204378231 10799213131981663806567347)
              ·
                refine ⟨16198819697972495709851021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10799213131981663806567347 16198819697972495709851021)
                ·
                  refine ⟨6074557386739685891194133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16198819697972495709851021 6074557386739685891194133)
                  ·
                    refine ⟨284744877503422776149725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6074557386739685891194133 284744877503422776149725)
                    ·
                      rfl

theorem cell23_1663616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 3, 6].length) (baseStart_1663616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663616 prefixEnd_1663616 := by exact prefixLift 1663616
  have htrace : WordTrace (prefixWord ++ tailWord_1663616) baseStart_1663616 baseEnd_1663616 := by
    simpa [prefixWord, tailWord_1663616, baseEnd_1663616] using wordTrace_append hprefix tailTrace_1663616
  have hstable : (prefixWord ++ tailWord_1663616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663616).length < 2 ^ (prefixWord ++ tailWord_1663616).sum := by decide
  have hdescent : baseEnd_1663616 < baseStart_1663616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663617 : List Nat := [1, 2, 4, 2, 1, 1, 2, 5, 1, 1, 3]
def baseStart_1663617 : Nat := 118140960795 + 1663617 * 2 ^ 59
def prefixEnd_1663617 : Nat := 4983230072969 + 3 ^ 40 * 1663617 * 2
def baseEnd_1663617 : Nat := 854235145990922824536671

theorem tailTrace_1663617 : CollatzResearch.WordTrace tailWord_1663617 prefixEnd_1663617 854235145990922824536671 := by
  unfold tailWord_1663617
  simp only [CollatzResearch.WordTrace]
  refine ⟨60677096814007207008509105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40451397876004804672339403 60677096814007207008509105)
  ·
    refine ⟨45507822610505405256381829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60677096814007207008509105 45507822610505405256381829)
    ·
      refine ⟨8532716739469763485571593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45507822610505405256381829 8532716739469763485571593)
      ·
        refine ⟨6399537554602322614178695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8532716739469763485571593 6399537554602322614178695)
        ·
          refine ⟨9599306331903483921268043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6399537554602322614178695 9599306331903483921268043)
          ·
            refine ⟨14398959497855225881902065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9599306331903483921268043 14398959497855225881902065)
            ·
              refine ⟨10799219623391419411426549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14398959497855225881902065 10799219623391419411426549)
              ·
                refine ⟨1012426839692945569821239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10799219623391419411426549 1012426839692945569821239)
                ·
                  refine ⟨1518640259539418354731859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1012426839692945569821239 1518640259539418354731859)
                  ·
                    refine ⟨2277960389309127532097789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1518640259539418354731859 2277960389309127532097789)
                    ·
                      refine ⟨854235145990922824536671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2277960389309127532097789 854235145990922824536671)
                      ·
                        rfl

theorem cell23_1663617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_1663617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663617 prefixEnd_1663617 := by exact prefixLift 1663617
  have htrace : WordTrace (prefixWord ++ tailWord_1663617) baseStart_1663617 baseEnd_1663617 := by
    simpa [prefixWord, tailWord_1663617, baseEnd_1663617] using wordTrace_append hprefix tailTrace_1663617
  have hstable : (prefixWord ++ tailWord_1663617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663617).length < 2 ^ (prefixWord ++ tailWord_1663617).sum := by decide
  have hdescent : baseEnd_1663617 < baseStart_1663617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663634 : List Nat := [3, 2, 3, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_1663634 : Nat := 118140960795 + 1663634 * 2 ^ 59
def prefixEnd_1663634 : Nat := 4983230072969 + 3 ^ 40 * 1663634 * 2
def baseEnd_1663634 : Nat := 854243875162049258024093

theorem tailTrace_1663634 : CollatzResearch.WordTrace tailWord_1663634 prefixEnd_1663634 854243875162049258024093 := by
  unfold tailWord_1663634
  simp only [CollatzResearch.WordTrace]
  refine ⟨15169429213736404727969489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40451811236630412607918637 15169429213736404727969489)
  ·
    refine ⟨11377071910302303545977117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15169429213736404727969489 11377071910302303545977117)
    ·
      refine ⟨4266401966363363829741419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11377071910302303545977117 4266401966363363829741419)
      ·
        refine ⟨6399602949545045744612129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4266401966363363829741419 6399602949545045744612129)
        ·
          refine ⟨4799702212158784308459097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6399602949545045744612129 4799702212158784308459097)
          ·
            refine ⟨3599776659119088231344323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4799702212158784308459097 3599776659119088231344323)
            ·
              refine ⟨5399664988678632347016485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3599776659119088231344323 5399664988678632347016485)
              ·
                refine ⟨1012437185377243565065591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5399664988678632347016485 1012437185377243565065591)
                ·
                  refine ⟨1518655778065865347598387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1012437185377243565065591 1518655778065865347598387)
                  ·
                    refine ⟨2277983667098798021397581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1518655778065865347598387 2277983667098798021397581)
                    ·
                      refine ⟨854243875162049258024093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2277983667098798021397581 854243875162049258024093)
                      ·
                        rfl

theorem cell23_1663634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_1663634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663634 prefixEnd_1663634 := by exact prefixLift 1663634
  have htrace : WordTrace (prefixWord ++ tailWord_1663634) baseStart_1663634 baseEnd_1663634 := by
    simpa [prefixWord, tailWord_1663634, baseEnd_1663634] using wordTrace_append hprefix tailTrace_1663634
  have hstable : (prefixWord ++ tailWord_1663634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663634).length < 2 ^ (prefixWord ++ tailWord_1663634).sum := by decide
  have hdescent : baseEnd_1663634 < baseStart_1663634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663663 : List Nat := [1, 1, 2, 1, 2, 6, 3, 7]
def baseStart_1663663 : Nat := 118140960795 + 1663663 * 2 ^ 59
def prefixEnd_1663663 : Nat := 4983230072969 + 3 ^ 40 * 1663663 * 2
def baseEnd_1663663 : Nat := 31639213559297394243017

theorem tailTrace_1663663 : CollatzResearch.WordTrace tailWord_1663663 prefixEnd_1663663 31639213559297394243017 := by
  unfold tailWord_1663663
  simp only [CollatzResearch.WordTrace]
  refine ⟨60678774571840556864683643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40452516381227037909789095 60678774571840556864683643)
  ·
    refine ⟨91018161857760835297025465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60678774571840556864683643 91018161857760835297025465)
    ·
      refine ⟨68263621393320626472769099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91018161857760835297025465 68263621393320626472769099)
      ·
        refine ⟨102395432089980939709153649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68263621393320626472769099 102395432089980939709153649)
        ·
          refine ⟨76796574067485704781865237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102395432089980939709153649 76796574067485704781865237)
          ·
            refine ⟨3599839409413392411649933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 76796574067485704781865237 3599839409413392411649933)
            ·
              refine ⟨1349939778530022154368725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3599839409413392411649933 1349939778530022154368725)
              ·
                refine ⟨31639213559297394243017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1349939778530022154368725 31639213559297394243017)
                ·
                  rfl

theorem cell23_1663663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 7].length) (baseStart_1663663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663663 prefixEnd_1663663 := by exact prefixLift 1663663
  have htrace : WordTrace (prefixWord ++ tailWord_1663663) baseStart_1663663 baseEnd_1663663 := by
    simpa [prefixWord, tailWord_1663663, baseEnd_1663663] using wordTrace_append hprefix tailTrace_1663663
  have hstable : (prefixWord ++ tailWord_1663663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663663).length < 2 ^ (prefixWord ++ tailWord_1663663).sum := by decide
  have hdescent : baseEnd_1663663 < baseStart_1663663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663674 : List Nat := [3, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2]
def baseStart_1663674 : Nat := 118140960795 + 1663674 * 2 ^ 59
def prefixEnd_1663674 : Nat := 4983230072969 + 3 ^ 40 * 1663674 * 2
def baseEnd_1663674 : Nat := 854264414388229101523909

theorem tailTrace_1663674 : CollatzResearch.WordTrace tailWord_1663674 prefixEnd_1663674 854264414388229101523909 := by
  unfold tailWord_1663674
  simp only [CollatzResearch.WordTrace]
  refine ⟨15169793943700176435833519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40452783849867137162222717 15169793943700176435833519)
  ·
    refine ⟨22754690915550264653750279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15169793943700176435833519 22754690915550264653750279)
    ·
      refine ⟨34132036373325396980625419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22754690915550264653750279 34132036373325396980625419)
      ·
        refine ⟨51198054559988095470938129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34132036373325396980625419 51198054559988095470938129)
        ·
          refine ⟨38398540919991071603203597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51198054559988095470938129 38398540919991071603203597)
          ·
            refine ⟨14399452844996651851201349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38398540919991071603203597 14399452844996651851201349)
            ·
              refine ⟨2699897408436872222100253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14399452844996651851201349 2699897408436872222100253)
              ·
                refine ⟨1012461528163827083287595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2699897408436872222100253 1012461528163827083287595)
                ·
                  refine ⟨1518692292245740624931393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1012461528163827083287595 1518692292245740624931393)
                  ·
                    refine ⟨1139019219184305468698545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1518692292245740624931393 1139019219184305468698545)
                    ·
                      refine ⟨854264414388229101523909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1139019219184305468698545 854264414388229101523909)
                      ·
                        rfl

theorem cell23_1663674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2].length) (baseStart_1663674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663674 prefixEnd_1663674 := by exact prefixLift 1663674
  have htrace : WordTrace (prefixWord ++ tailWord_1663674) baseStart_1663674 baseEnd_1663674 := by
    simpa [prefixWord, tailWord_1663674, baseEnd_1663674] using wordTrace_append hprefix tailTrace_1663674
  have hstable : (prefixWord ++ tailWord_1663674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663674).length < 2 ^ (prefixWord ++ tailWord_1663674).sum := by decide
  have hdescent : baseEnd_1663674 < baseStart_1663674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663677 : List Nat := [1, 4, 1, 2, 1, 3, 4, 1, 1, 2, 3]
def baseStart_1663677 : Nat := 118140960795 + 1663677 * 2 ^ 59
def prefixEnd_1663677 : Nat := 4983230072969 + 3 ^ 40 * 1663677 * 2
def baseEnd_1663677 : Nat := 854265954830192589786395

theorem tailTrace_1663677 : CollatzResearch.WordTrace tailWord_1663677 prefixEnd_1663677 854265954830192589786395 := by
  unfold tailWord_1663677
  simp only [CollatzResearch.WordTrace]
  refine ⟨60679285193789837255693285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40452856795859891503795523 60679285193789837255693285)
  ·
    refine ⟨11377365973835594485442491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60679285193789837255693285 11377365973835594485442491)
    ·
      refine ⟨17066048960753391728163737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11377365973835594485442491 17066048960753391728163737)
      ·
        refine ⟨12799536720565043796122803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17066048960753391728163737 12799536720565043796122803)
        ·
          refine ⟨19199305080847565694184205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12799536720565043796122803 19199305080847565694184205)
          ·
            refine ⟨7199739405317837135319077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19199305080847565694184205 7199739405317837135319077)
            ·
              refine ⟨1349951138497094462872327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7199739405317837135319077 1349951138497094462872327)
              ·
                refine ⟨2024926707745641694308491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1349951138497094462872327 2024926707745641694308491)
                ·
                  refine ⟨3037390061618462541462737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2024926707745641694308491 3037390061618462541462737)
                  ·
                    refine ⟨2278042546213846906097053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3037390061618462541462737 2278042546213846906097053)
                    ·
                      refine ⟨854265954830192589786395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2278042546213846906097053 854265954830192589786395)
                      ·
                        rfl

theorem cell23_1663677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_1663677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663677 prefixEnd_1663677 := by exact prefixLift 1663677
  have htrace : WordTrace (prefixWord ++ tailWord_1663677) baseStart_1663677 baseEnd_1663677 := by
    simpa [prefixWord, tailWord_1663677, baseEnd_1663677] using wordTrace_append hprefix tailTrace_1663677
  have hstable : (prefixWord ++ tailWord_1663677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663677).length < 2 ^ (prefixWord ++ tailWord_1663677).sum := by decide
  have hdescent : baseEnd_1663677 < baseStart_1663677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663717 : List Nat := [1, 3, 1, 4, 1, 2, 1, 4, 1, 3, 2]
def baseStart_1663717 : Nat := 118140960795 + 1663717 * 2 ^ 59
def prefixEnd_1663717 : Nat := 4983230072969 + 3 ^ 40 * 1663717 * 2
def baseEnd_1663717 : Nat := 854286494056372433286211

theorem tailTrace_1663717 : CollatzResearch.WordTrace tailWord_1663717 prefixEnd_1663717 854286494056372433286211 := by
  unfold tailWord_1663717
  simp only [CollatzResearch.WordTrace]
  refine ⟨60680744113644924087149405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40453829409096616058099603 60680744113644924087149405)
  ·
    refine ⟨22755279042616846532681027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60680744113644924087149405 22755279042616846532681027)
    ·
      refine ⟨34132918563925269799021541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22755279042616846532681027 34132918563925269799021541)
      ·
        refine ⟨6399922230735988087316539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34132918563925269799021541 6399922230735988087316539)
        ·
          refine ⟨9599883346103982130974809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6399922230735988087316539 9599883346103982130974809)
          ·
            refine ⟨7199912509577986598231107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9599883346103982130974809 7199912509577986598231107)
            ·
              refine ⟨10799868764366979897346661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7199912509577986598231107 10799868764366979897346661)
              ·
                refine ⟨2024975393318808730752499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10799868764366979897346661 2024975393318808730752499)
                ·
                  refine ⟨3037463089978213096128749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2024975393318808730752499 3037463089978213096128749)
                  ·
                    refine ⟨1139048658741829911048281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3037463089978213096128749 1139048658741829911048281)
                    ·
                      refine ⟨854286494056372433286211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1139048658741829911048281 854286494056372433286211)
                      ·
                        rfl

theorem cell23_1663717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_1663717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663717 prefixEnd_1663717 := by exact prefixLift 1663717
  have htrace : WordTrace (prefixWord ++ tailWord_1663717) baseStart_1663717 baseEnd_1663717 := by
    simpa [prefixWord, tailWord_1663717, baseEnd_1663717] using wordTrace_append hprefix tailTrace_1663717
  have hstable : (prefixWord ++ tailWord_1663717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663717).length < 2 ^ (prefixWord ++ tailWord_1663717).sum := by decide
  have hdescent : baseEnd_1663717 < baseStart_1663717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663747 : List Nat := [1, 1, 1, 3, 2, 2, 1, 6, 2, 2, 2]
def baseStart_1663747 : Nat := 118140960795 + 1663747 * 2 ^ 59
def prefixEnd_1663747 : Nat := 4983230072969 + 3 ^ 40 * 1663747 * 2
def baseEnd_1663747 : Nat := 854301898476007315911073

theorem tailTrace_1663747 : CollatzResearch.WordTrace tailWord_1663747 prefixEnd_1663747 854301898476007315911073 := by
  unfold tailWord_1663747
  simp only [CollatzResearch.WordTrace]
  refine ⟨60681838303536239210741495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40454558869024159473827663 60681838303536239210741495)
  ·
    refine ⟨91022757455304358816112243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60681838303536239210741495 91022757455304358816112243)
    ·
      refine ⟨136534136182956538224168365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91022757455304358816112243 136534136182956538224168365)
      ·
        refine ⟨51200301068608701834063137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136534136182956538224168365 51200301068608701834063137)
        ·
          refine ⟨38400225801456526375547353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51200301068608701834063137 38400225801456526375547353)
          ·
            refine ⟨28800169351092394781660515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38400225801456526375547353 28800169351092394781660515)
            ·
              refine ⟨43200254026638592172490773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28800169351092394781660515 43200254026638592172490773)
              ·
                refine ⟨2025011907498684008085505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43200254026638592172490773 2025011907498684008085505)
                ·
                  refine ⟨1518758930624013006064129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2025011907498684008085505 1518758930624013006064129)
                  ·
                    refine ⟨1139069197968009754548097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1518758930624013006064129 1139069197968009754548097)
                    ·
                      refine ⟨854301898476007315911073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1139069197968009754548097 854301898476007315911073)
                      ·
                        rfl

theorem cell23_1663747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 2, 2].length) (baseStart_1663747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663747 prefixEnd_1663747 := by exact prefixLift 1663747
  have htrace : WordTrace (prefixWord ++ tailWord_1663747) baseStart_1663747 baseEnd_1663747 := by
    simpa [prefixWord, tailWord_1663747, baseEnd_1663747] using wordTrace_append hprefix tailTrace_1663747
  have hstable : (prefixWord ++ tailWord_1663747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663747).length < 2 ^ (prefixWord ++ tailWord_1663747).sum := by decide
  have hdescent : baseEnd_1663747 < baseStart_1663747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663753 : List Nat := [1, 2, 1, 1, 3, 2, 5, 1, 7]
def baseStart_1663753 : Nat := 118140960795 + 1663753 * 2 ^ 59
def prefixEnd_1663753 : Nat := 4983230072969 + 3 ^ 40 * 1663753 * 2
def baseEnd_1663753 : Nat := 94922775484437143604005

theorem tailTrace_1663753 : CollatzResearch.WordTrace tailWord_1663753 prefixEnd_1663753 94922775484437143604005 := by
  unfold tailWord_1663753
  simp only [CollatzResearch.WordTrace]
  refine ⟨60682057141514502235459913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40454704761009668156973275 60682057141514502235459913)
  ·
    refine ⟨45511542856135876676594935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60682057141514502235459913 45511542856135876676594935)
    ·
      refine ⟨68267314284203815014892403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45511542856135876676594935 68267314284203815014892403)
      ·
        refine ⟨102400971426305722522338605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68267314284203815014892403 102400971426305722522338605)
        ·
          refine ⟨38400364284864645945876977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102400971426305722522338605 38400364284864645945876977)
          ·
            refine ⟨28800273213648484459407733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38400364284864645945876977 28800273213648484459407733)
            ·
              refine ⟨2700025613779545418069475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28800273213648484459407733 2700025613779545418069475)
              ·
                refine ⟨4050038420669318127104213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2700025613779545418069475 4050038420669318127104213)
                ·
                  refine ⟨94922775484437143604005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4050038420669318127104213 94922775484437143604005)
                  ·
                    rfl

theorem cell23_1663753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 7].length) (baseStart_1663753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663753 prefixEnd_1663753 := by exact prefixLift 1663753
  have htrace : WordTrace (prefixWord ++ tailWord_1663753) baseStart_1663753 baseEnd_1663753 := by
    simpa [prefixWord, tailWord_1663753, baseEnd_1663753] using wordTrace_append hprefix tailTrace_1663753
  have hstable : (prefixWord ++ tailWord_1663753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663753).length < 2 ^ (prefixWord ++ tailWord_1663753).sum := by decide
  have hdescent : baseEnd_1663753 < baseStart_1663753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663763 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 3]
def baseStart_1663763 : Nat := 118140960795 + 1663763 * 2 ^ 59
def prefixEnd_1663763 : Nat := 4983230072969 + 3 ^ 40 * 1663763 * 2
def baseEnd_1663763 : Nat := 854310114166479253310999

theorem tailTrace_1663763 : CollatzResearch.WordTrace tailWord_1663763 prefixEnd_1663763 854310114166479253310999 := by
  unfold tailWord_1663763
  simp only [CollatzResearch.WordTrace]
  refine ⟨60682421871478273943323943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40454947914318849295549295 60682421871478273943323943)
  ·
    refine ⟨91023632807217410914985915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60682421871478273943323943 91023632807217410914985915)
    ·
      refine ⟨136535449210826116372478873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91023632807217410914985915 136535449210826116372478873)
      ·
        refine ⟨102401586908119587279359155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136535449210826116372478873 102401586908119587279359155)
        ·
          refine ⟨153602380362179380919038733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102401586908119587279359155 153602380362179380919038733)
          ·
            refine ⟨57600892635817267844639525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153602380362179380919038733 57600892635817267844639525)
            ·
              refine ⟨10800167369215737720869911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57600892635817267844639525 10800167369215737720869911)
              ·
                refine ⟨16200251053823606581304867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10800167369215737720869911 16200251053823606581304867)
                ·
                  refine ⟨24300376580735409871957301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16200251053823606581304867 24300376580735409871957301)
                  ·
                    refine ⟨2278160304443944675495997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24300376580735409871957301 2278160304443944675495997)
                    ·
                      refine ⟨854310114166479253310999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2278160304443944675495997 854310114166479253310999)
                      ·
                        rfl

theorem cell23_1663763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 3].length) (baseStart_1663763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663763 prefixEnd_1663763 := by exact prefixLift 1663763
  have htrace : WordTrace (prefixWord ++ tailWord_1663763) baseStart_1663763 baseEnd_1663763 := by
    simpa [prefixWord, tailWord_1663763, baseEnd_1663763] using wordTrace_append hprefix tailTrace_1663763
  have hstable : (prefixWord ++ tailWord_1663763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663763).length < 2 ^ (prefixWord ++ tailWord_1663763).sum := by decide
  have hdescent : baseEnd_1663763 < baseStart_1663763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663793 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 3, 2, 5]
def baseStart_1663793 : Nat := 118140960795 + 1663793 * 2 ^ 59
def prefixEnd_1663793 : Nat := 4983230072969 + 3 ^ 40 * 1663793 * 2
def baseEnd_1663793 : Nat := 854325518586114135935861

theorem tailTrace_1663793 : CollatzResearch.WordTrace tailWord_1663793 prefixEnd_1663793 854325518586114135935861 := by
  unfold tailWord_1663793
  simp only [CollatzResearch.WordTrace]
  refine ⟨60683516061369589066916033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40455677374246392711277355 60683516061369589066916033)
  ·
    refine ⟨45512637046027191800187025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60683516061369589066916033 45512637046027191800187025)
    ·
      refine ⟨34134477784520393850140269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45512637046027191800187025 34134477784520393850140269)
      ·
        refine ⟨12800429169195147693802601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34134477784520393850140269 12800429169195147693802601)
        ·
          refine ⟨9600321876896360770351951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12800429169195147693802601 9600321876896360770351951)
          ·
            refine ⟨14400482815344541155527927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9600321876896360770351951 14400482815344541155527927)
            ·
              refine ⟨21600724223016811733291891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14400482815344541155527927 21600724223016811733291891)
              ·
                refine ⟨32401086334525217599937837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21600724223016811733291891 32401086334525217599937837)
                ·
                  refine ⟨12150407375446956599976689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32401086334525217599937837 12150407375446956599976689)
                  ·
                    refine ⟨9112805531585217449982517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12150407375446956599976689 9112805531585217449982517)
                    ·
                      refine ⟨854325518586114135935861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9112805531585217449982517 854325518586114135935861)
                      ·
                        rfl

theorem cell23_1663793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_1663793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663793 prefixEnd_1663793 := by exact prefixLift 1663793
  have htrace : WordTrace (prefixWord ++ tailWord_1663793) baseStart_1663793 baseEnd_1663793 := by
    simpa [prefixWord, tailWord_1663793, baseEnd_1663793] using wordTrace_append hprefix tailTrace_1663793
  have hstable : (prefixWord ++ tailWord_1663793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663793).length < 2 ^ (prefixWord ++ tailWord_1663793).sum := by decide
  have hdescent : baseEnd_1663793 < baseStart_1663793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663798 : List Nat := [5, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_1663798 : Nat := 118140960795 + 1663798 * 2 ^ 59
def prefixEnd_1663798 : Nat := 4983230072969 + 3 ^ 40 * 1663798 * 2
def baseEnd_1663798 : Nat := 854328085989386616373339

theorem tailTrace_1663798 : CollatzResearch.WordTrace tailWord_1663798 prefixEnd_1663798 854328085989386616373339 := by
  unfold tailWord_1663798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3792731151646967182553003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40455798950900983280565365 3792731151646967182553003)
  ·
    refine ⟨5689096727470450773829505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3792731151646967182553003 5689096727470450773829505)
    ·
      refine ⟨4266822545602838080372129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5689096727470450773829505 4266822545602838080372129)
      ·
        refine ⟨3200116909202128560279097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4266822545602838080372129 3200116909202128560279097)
        ·
          refine ⟨2400087681901596420209323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3200116909202128560279097 2400087681901596420209323)
          ·
            refine ⟨3600131522852394630313985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2400087681901596420209323 3600131522852394630313985)
            ·
              refine ⟨2700098642139295972735489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3600131522852394630313985 2700098642139295972735489)
              ·
                refine ⟨2025073981604471979551617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2700098642139295972735489 2025073981604471979551617)
                ·
                  refine ⟨1518805486203353984663713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2025073981604471979551617 1518805486203353984663713)
                  ·
                    refine ⟨1139104114652515488497785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1518805486203353984663713 1139104114652515488497785)
                    ·
                      refine ⟨854328085989386616373339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1139104114652515488497785 854328085989386616373339)
                      ·
                        rfl

theorem cell23_1663798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_1663798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663798 prefixEnd_1663798 := by exact prefixLift 1663798
  have htrace : WordTrace (prefixWord ++ tailWord_1663798) baseStart_1663798 baseEnd_1663798 := by
    simpa [prefixWord, tailWord_1663798, baseEnd_1663798] using wordTrace_append hprefix tailTrace_1663798
  have hstable : (prefixWord ++ tailWord_1663798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663798).length < 2 ^ (prefixWord ++ tailWord_1663798).sum := by decide
  have hdescent : baseEnd_1663798 < baseStart_1663798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663840 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 3]
def baseStart_1663840 : Nat := 118140960795 + 1663840 * 2 ^ 59
def prefixEnd_1663840 : Nat := 4983230072969 + 3 ^ 40 * 1663840 * 2
def baseEnd_1663840 : Nat := 854349652176875452048145

theorem tailTrace_1663840 : CollatzResearch.WordTrace tailWord_1663840 prefixEnd_1663840 854349652176875452048145 := by
  unfold tailWord_1663840
  simp only [CollatzResearch.WordTrace]
  refine ⟨30342615146099658046938487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40456820194799544062584649 30342615146099658046938487)
  ·
    refine ⟨45513922719149487070407731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30342615146099658046938487 45513922719149487070407731)
    ·
      refine ⟨68270884078724230605611597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45513922719149487070407731 68270884078724230605611597)
      ·
        refine ⟨25601581529521586477104349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68270884078724230605611597 25601581529521586477104349)
        ·
          refine ⟨9600593073570594928914131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25601581529521586477104349 9600593073570594928914131)
          ·
            refine ⟨14400889610355892393371197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9600593073570594928914131 14400889610355892393371197)
            ·
              refine ⟨5400333603883459647514199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14400889610355892393371197 5400333603883459647514199)
              ·
                refine ⟨8100500405825189471271299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5400333603883459647514199 8100500405825189471271299)
                ·
                  refine ⟨12150750608737784206906949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8100500405825189471271299 12150750608737784206906949)
                  ·
                    refine ⟨2278265739138334538795053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12150750608737784206906949 2278265739138334538795053)
                    ·
                      refine ⟨854349652176875452048145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2278265739138334538795053 854349652176875452048145)
                      ·
                        rfl

theorem cell23_1663840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_1663840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663840 prefixEnd_1663840 := by exact prefixLift 1663840
  have htrace : WordTrace (prefixWord ++ tailWord_1663840) baseStart_1663840 baseEnd_1663840 := by
    simpa [prefixWord, tailWord_1663840, baseEnd_1663840] using wordTrace_append hprefix tailTrace_1663840
  have hstable : (prefixWord ++ tailWord_1663840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663840).length < 2 ^ (prefixWord ++ tailWord_1663840).sum := by decide
  have hdescent : baseEnd_1663840 < baseStart_1663840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663877 : List Nat := [1, 3, 1, 1, 3, 4, 3, 1, 6]
def baseStart_1663877 : Nat := 118140960795 + 1663877 * 2 ^ 59
def prefixEnd_1663877 : Nat := 4983230072969 + 3 ^ 40 * 1663877 * 2
def baseEnd_1663877 : Nat := 94929850106787978587275

theorem tailTrace_1663877 : CollatzResearch.WordTrace tailWord_1663877 prefixEnd_1663877 94929850106787978587275 := by
  unfold tailWord_1663877
  simp only [CollatzResearch.WordTrace]
  refine ⟨60686579793065271412973885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40457719862043514275315923 60686579793065271412973885)
  ·
    refine ⟨22757467422399476779865207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60686579793065271412973885 22757467422399476779865207)
    ·
      refine ⟨34136201133599215169797811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22757467422399476779865207 34136201133599215169797811)
      ·
        refine ⟨51204301700398822754696717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34136201133599215169797811 51204301700398822754696717)
        ·
          refine ⟨19201613137649558533011269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51204301700398822754696717 19201613137649558533011269)
          ·
            refine ⟨3600302463309292224939613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19201613137649558533011269 3600302463309292224939613)
            ·
              refine ⟨1350113423740984584352355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3600302463309292224939613 1350113423740984584352355)
              ·
                refine ⟨2025170135611476876528533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350113423740984584352355 2025170135611476876528533)
                ·
                  refine ⟨94929850106787978587275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2025170135611476876528533 94929850106787978587275)
                  ·
                    rfl

theorem cell23_1663877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 6].length) (baseStart_1663877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663877 prefixEnd_1663877 := by exact prefixLift 1663877
  have htrace : WordTrace (prefixWord ++ tailWord_1663877) baseStart_1663877 baseEnd_1663877 := by
    simpa [prefixWord, tailWord_1663877, baseEnd_1663877] using wordTrace_append hprefix tailTrace_1663877
  have hstable : (prefixWord ++ tailWord_1663877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663877).length < 2 ^ (prefixWord ++ tailWord_1663877).sum := by decide
  have hdescent : baseEnd_1663877 < baseStart_1663877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663883 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 7]
def baseStart_1663883 : Nat := 118140960795 + 1663883 * 2 ^ 59
def prefixEnd_1663883 : Nat := 4983230072969 + 3 ^ 40 * 1663883 * 2
def baseEnd_1663883 : Nat := 854371731845018783810447

theorem tailTrace_1663883 : CollatzResearch.WordTrace tailWord_1663883 prefixEnd_1663883 854371731845018783810447 := by
  unfold tailWord_1663883
  simp only [CollatzResearch.WordTrace]
  refine ⟨60686798631043534437692303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40457865754029022958461535 60686798631043534437692303)
  ·
    refine ⟨91030197946565301656538455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60686798631043534437692303 91030197946565301656538455)
    ·
      refine ⟨136545296919847952484807683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91030197946565301656538455 136545296919847952484807683)
      ·
        refine ⟨204817945379771928727211525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136545296919847952484807683 204817945379771928727211525)
        ·
          refine ⟨38403364758707236636352161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204817945379771928727211525 38403364758707236636352161)
          ·
            refine ⟨28802523569030427477264121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38403364758707236636352161 28802523569030427477264121)
            ·
              refine ⟨21601892676772820607948091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28802523569030427477264121 21601892676772820607948091)
              ·
                refine ⟨32402839015159230911922137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21601892676772820607948091 32402839015159230911922137)
                ·
                  refine ⟨24302129261369423183941603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32402839015159230911922137 24302129261369423183941603)
                  ·
                    refine ⟨36453193892054134775912405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24302129261369423183941603 36453193892054134775912405)
                    ·
                      refine ⟨854371731845018783810447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36453193892054134775912405 854371731845018783810447)
                      ·
                        rfl

theorem cell23_1663883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 7].length) (baseStart_1663883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663883 prefixEnd_1663883 := by exact prefixLift 1663883
  have htrace : WordTrace (prefixWord ++ tailWord_1663883) baseStart_1663883 baseEnd_1663883 := by
    simpa [prefixWord, tailWord_1663883, baseEnd_1663883] using wordTrace_append hprefix tailTrace_1663883
  have hstable : (prefixWord ++ tailWord_1663883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663883).length < 2 ^ (prefixWord ++ tailWord_1663883).sum := by decide
  have hdescent : baseEnd_1663883 < baseStart_1663883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663894 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 8]
def baseStart_1663894 : Nat := 118140960795 + 1663894 * 2 ^ 59
def prefixEnd_1663894 : Nat := 4983230072969 + 3 ^ 40 * 1663894 * 2
def baseEnd_1663894 : Nat := 94930820014690915641433

theorem tailTrace_1663894 : CollatzResearch.WordTrace tailWord_1663894 prefixEnd_1663894 94930820014690915641433 := by
  unfold tailWord_1663894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3792949989625230207271421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40458133222669122210895157 3792949989625230207271421)
  ·
    refine ⟨1422356246109461327726783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3792949989625230207271421 1422356246109461327726783)
    ·
      refine ⟨2133534369164191991590175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1422356246109461327726783 2133534369164191991590175)
      ·
        refine ⟨3200301553746287987385263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2133534369164191991590175 3200301553746287987385263)
        ·
          refine ⟨4800452330619431981077895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3200301553746287987385263 4800452330619431981077895)
          ·
            refine ⟨7200678495929147971616843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4800452330619431981077895 7200678495929147971616843)
            ·
              refine ⟨10801017743893721957425265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7200678495929147971616843 10801017743893721957425265)
              ·
                refine ⟨8100763307920291468068949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10801017743893721957425265 8100763307920291468068949)
                ·
                  refine ⟨94930820014690915641433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8100763307920291468068949 94930820014690915641433)
                  ·
                    rfl

theorem cell23_1663894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_1663894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663894 prefixEnd_1663894 := by exact prefixLift 1663894
  have htrace : WordTrace (prefixWord ++ tailWord_1663894) baseStart_1663894 baseEnd_1663894 := by
    simpa [prefixWord, tailWord_1663894, baseEnd_1663894] using wordTrace_append hprefix tailTrace_1663894
  have hstable : (prefixWord ++ tailWord_1663894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663894).length < 2 ^ (prefixWord ++ tailWord_1663894).sum := by decide
  have hdescent : baseEnd_1663894 < baseStart_1663894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663897 : List Nat := [1, 2, 1, 2, 1, 3, 1, 5, 2, 3, 2]
def baseStart_1663897 : Nat := 118140960795 + 1663897 * 2 ^ 59
def prefixEnd_1663897 : Nat := 4983230072969 + 3 ^ 40 * 1663897 * 2
def baseEnd_1663897 : Nat := 854378920574181729035383

theorem tailTrace_1663897 : CollatzResearch.WordTrace tailWord_1663897 prefixEnd_1663897 854378920574181729035383 := by
  unfold tailWord_1663897
  simp only [CollatzResearch.WordTrace]
  refine ⟨60687309252992814828701945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40458206168661876552467963 60687309252992814828701945)
  ·
    refine ⟨45515481939744611121526459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60687309252992814828701945 45515481939744611121526459)
    ·
      refine ⟨68273222909616916682289689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45515481939744611121526459 68273222909616916682289689)
      ·
        refine ⟨51204917182212687511717267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68273222909616916682289689 51204917182212687511717267)
        ·
          refine ⟨76807375773319031267575901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51204917182212687511717267 76807375773319031267575901)
          ·
            refine ⟨28802765914994636725340963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76807375773319031267575901 28802765914994636725340963)
            ·
              refine ⟨43204148872491955088011445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28802765914994636725340963 43204148872491955088011445)
              ·
                refine ⟨4050388956796120789501073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43204148872491955088011445 4050388956796120789501073)
                ·
                  refine ⟨3037791717597090592125805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4050388956796120789501073 3037791717597090592125805)
                  ·
                    refine ⟨1139171894098908972047177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3037791717597090592125805 1139171894098908972047177)
                    ·
                      refine ⟨854378920574181729035383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1139171894098908972047177 854378920574181729035383)
                      ·
                        rfl

theorem cell23_1663897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 3, 2].length) (baseStart_1663897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663897 prefixEnd_1663897 := by exact prefixLift 1663897
  have htrace : WordTrace (prefixWord ++ tailWord_1663897) baseStart_1663897 baseEnd_1663897 := by
    simpa [prefixWord, tailWord_1663897, baseEnd_1663897] using wordTrace_append hprefix tailTrace_1663897
  have hstable : (prefixWord ++ tailWord_1663897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663897).length < 2 ^ (prefixWord ++ tailWord_1663897).sum := by decide
  have hdescent : baseEnd_1663897 < baseStart_1663897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663898 : List Nat := [3, 1, 1, 4, 4, 1, 1, 3, 1, 4]
def baseStart_1663898 : Nat := 118140960795 + 1663898 * 2 ^ 59
def prefixEnd_1663898 : Nat := 4983230072969 + 3 ^ 40 * 1663898 * 2
def baseEnd_1663898 : Nat := 284793144684945408374293

theorem tailTrace_1663898 : CollatzResearch.WordTrace tailWord_1663898 prefixEnd_1663898 284793144684945408374293 := by
  unfold tailWord_1663898
  simp only [CollatzResearch.WordTrace]
  refine ⟨15171836431497297999872087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40458230483992794666325565 15171836431497297999872087)
  ·
    refine ⟨22757754647245946999808131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15171836431497297999872087 22757754647245946999808131)
    ·
      refine ⟨34136631970868920499712197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22757754647245946999808131 34136631970868920499712197)
      ·
        refine ⟨6400618494537922593696037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34136631970868920499712197 6400618494537922593696037)
        ·
          refine ⟨1200115967725860486318007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6400618494537922593696037 1200115967725860486318007)
          ·
            refine ⟨1800173951588790729477011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1200115967725860486318007 1800173951588790729477011)
            ·
              refine ⟨2700260927383186094215517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800173951588790729477011 2700260927383186094215517)
              ·
                refine ⟨1012597847768694785330819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2700260927383186094215517 1012597847768694785330819)
                ·
                  refine ⟨1518896771653042177996229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1012597847768694785330819 1518896771653042177996229)
                  ·
                    refine ⟨284793144684945408374293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1518896771653042177996229 284793144684945408374293)
                    ·
                      rfl

theorem cell23_1663898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 1, 4].length) (baseStart_1663898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663898 prefixEnd_1663898 := by exact prefixLift 1663898
  have htrace : WordTrace (prefixWord ++ tailWord_1663898) baseStart_1663898 baseEnd_1663898 := by
    simpa [prefixWord, tailWord_1663898, baseEnd_1663898] using wordTrace_append hprefix tailTrace_1663898
  have hstable : (prefixWord ++ tailWord_1663898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663898).length < 2 ^ (prefixWord ++ tailWord_1663898).sum := by decide
  have hdescent : baseEnd_1663898 < baseStart_1663898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663921 : List Nat := [1, 2, 2, 4, 3, 2, 1, 1, 3, 1, 3]
def baseStart_1663921 : Nat := 118140960795 + 1663921 * 2 ^ 59
def prefixEnd_1663921 : Nat := 4983230072969 + 3 ^ 40 * 1663921 * 2
def baseEnd_1663921 : Nat := 854391244109889635135273

theorem tailTrace_1663921 : CollatzResearch.WordTrace tailWord_1663921 prefixEnd_1663921 854391244109889635135273 := by
  unfold tailWord_1663921
  simp only [CollatzResearch.WordTrace]
  refine ⟨60688184604905866927575617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40458789736603911285050411 60688184604905866927575617)
  ·
    refine ⟨45516138453679400195681713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60688184604905866927575617 45516138453679400195681713)
    ·
      refine ⟨34137103840259550146761285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45516138453679400195681713 34137103840259550146761285)
      ·
        refine ⟨6400706970048665652517741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34137103840259550146761285 6400706970048665652517741)
        ·
          refine ⟨2400265113768249619694153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6400706970048665652517741 2400265113768249619694153)
          ·
            refine ⟨1800198835326187214770615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2400265113768249619694153 1800198835326187214770615)
            ·
              refine ⟨2700298252989280822155923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800198835326187214770615 2700298252989280822155923)
              ·
                refine ⟨4050447379483921233233885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2700298252989280822155923 4050447379483921233233885)
                ·
                  refine ⟨1518917767306470462462707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4050447379483921233233885 1518917767306470462462707)
                  ·
                    refine ⟨2278376650959705693694061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1518917767306470462462707 2278376650959705693694061)
                    ·
                      refine ⟨854391244109889635135273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2278376650959705693694061 854391244109889635135273)
                      ·
                        rfl

theorem cell23_1663921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_1663921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663921 prefixEnd_1663921 := by exact prefixLift 1663921
  have htrace : WordTrace (prefixWord ++ tailWord_1663921) baseStart_1663921 baseEnd_1663921 := by
    simpa [prefixWord, tailWord_1663921, baseEnd_1663921] using wordTrace_append hprefix tailTrace_1663921
  have hstable : (prefixWord ++ tailWord_1663921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663921).length < 2 ^ (prefixWord ++ tailWord_1663921).sum := by decide
  have hdescent : baseEnd_1663921 < baseStart_1663921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663930 : List Nat := [3, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5]
def baseStart_1663930 : Nat := 118140960795 + 1663930 * 2 ^ 59
def prefixEnd_1663930 : Nat := 4983230072969 + 3 ^ 40 * 1663930 * 2
def baseEnd_1663930 : Nat := 854395865435780099922731

theorem tailTrace_1663930 : CollatzResearch.WordTrace tailWord_1663930 prefixEnd_1663930 854395865435780099922731 := by
  unfold tailWord_1663930
  simp only [CollatzResearch.WordTrace]
  refine ⟨15172128215468315366163311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40459008574582174309768829 15172128215468315366163311)
  ·
    refine ⟨22758192323202473049244967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15172128215468315366163311 22758192323202473049244967)
    ·
      refine ⟨34137288484803709573867451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22758192323202473049244967 34137288484803709573867451)
      ·
        refine ⟨51205932727205564360801177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34137288484803709573867451 51205932727205564360801177)
        ·
          refine ⟨38404449545404173270600883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51205932727205564360801177 38404449545404173270600883)
          ·
            refine ⟨57606674318106259905901325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38404449545404173270600883 57606674318106259905901325)
            ·
              refine ⟨21602502869289847464712997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57606674318106259905901325 21602502869289847464712997)
              ·
                refine ⟨4050469287991846399633687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21602502869289847464712997 4050469287991846399633687)
                ·
                  refine ⟨6075703931987769599450531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4050469287991846399633687 6075703931987769599450531)
                  ·
                    refine ⟨9113555897981654399175797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6075703931987769599450531 9113555897981654399175797)
                    ·
                      refine ⟨854395865435780099922731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9113555897981654399175797 854395865435780099922731)
                      ·
                        rfl

theorem cell23_1663930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_1663930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663930 prefixEnd_1663930 := by exact prefixLift 1663930
  have htrace : WordTrace (prefixWord ++ tailWord_1663930) baseStart_1663930 baseEnd_1663930 := by
    simpa [prefixWord, tailWord_1663930, baseEnd_1663930] using wordTrace_append hprefix tailTrace_1663930
  have hstable : (prefixWord ++ tailWord_1663930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663930).length < 2 ^ (prefixWord ++ tailWord_1663930).sum := by decide
  have hdescent : baseEnd_1663930 < baseStart_1663930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663947 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 3]
def baseStart_1663947 : Nat := 118140960795 + 1663947 * 2 ^ 59
def prefixEnd_1663947 : Nat := 4983230072969 + 3 ^ 40 * 1663947 * 2
def baseEnd_1663947 : Nat := 854404594606906533410153

theorem tailTrace_1663947 : CollatzResearch.WordTrace tailWord_1663947 prefixEnd_1663947 854404594606906533410153 := by
  unfold tailWord_1663947
  simp only [CollatzResearch.WordTrace]
  refine ⟨60689132902811673368022095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40459421935207782245348063 60689132902811673368022095)
  ·
    refine ⟨91033699354217510052033143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60689132902811673368022095 91033699354217510052033143)
    ·
      refine ⟨136550549031326265078049715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91033699354217510052033143 136550549031326265078049715)
      ·
        refine ⟨204825823546989397617074573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136550549031326265078049715 204825823546989397617074573)
        ·
          refine ⟨76809683830121024106402965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204825823546989397617074573 76809683830121024106402965)
          ·
            refine ⟨3600453929536923004987639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 76809683830121024106402965 3600453929536923004987639)
            ·
              refine ⟨5400680894305384507481459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3600453929536923004987639 5400680894305384507481459)
              ·
                refine ⟨8101021341458076761222189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5400680894305384507481459 8101021341458076761222189)
                ·
                  refine ⟨3037883003046778785458321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8101021341458076761222189 3037883003046778785458321)
                  ·
                    refine ⟨2278412252285084089093741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3037883003046778785458321 2278412252285084089093741)
                    ·
                      refine ⟨854404594606906533410153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2278412252285084089093741 854404594606906533410153)
                      ·
                        rfl

theorem cell23_1663947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 3].length) (baseStart_1663947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663947 prefixEnd_1663947 := by exact prefixLift 1663947
  have htrace : WordTrace (prefixWord ++ tailWord_1663947) baseStart_1663947 baseEnd_1663947 := by
    simpa [prefixWord, tailWord_1663947, baseEnd_1663947] using wordTrace_append hprefix tailTrace_1663947
  have hstable : (prefixWord ++ tailWord_1663947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663947).length < 2 ^ (prefixWord ++ tailWord_1663947).sum := by decide
  have hdescent : baseEnd_1663947 < baseStart_1663947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663950 : List Nat := [4, 1, 1, 1, 2, 3, 2, 9]
def baseStart_1663950 : Nat := 118140960795 + 1663950 * 2 ^ 59
def prefixEnd_1663950 : Nat := 4983230072969 + 3 ^ 40 * 1663950 * 2
def baseEnd_1663950 : Nat := 31644671668476667469357

theorem tailTrace_1663950 : CollatzResearch.WordTrace tailWord_1663950 prefixEnd_1663950 31644671668476667469357 := by
  unfold tailWord_1663950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7586155290225100610047663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40459494881200536586920869 7586155290225100610047663)
  ·
    refine ⟨11379232935337650915071495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7586155290225100610047663 11379232935337650915071495)
    ·
      refine ⟨17068849403006476372607243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11379232935337650915071495 17068849403006476372607243)
      ·
        refine ⟨25603274104509714558910865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17068849403006476372607243 25603274104509714558910865)
        ·
          refine ⟨19202455578382285919183149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25603274104509714558910865 19202455578382285919183149)
          ·
            refine ⟨7200920841893357219693681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19202455578382285919183149 7200920841893357219693681)
            ·
              refine ⟨5400690631420017914770261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7200920841893357219693681 5400690631420017914770261)
              ·
                refine ⟨31644671668476667469357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5400690631420017914770261 31644671668476667469357)
                ·
                  rfl

theorem cell23_1663950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 9].length) (baseStart_1663950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663950 prefixEnd_1663950 := by exact prefixLift 1663950
  have htrace : WordTrace (prefixWord ++ tailWord_1663950) baseStart_1663950 baseEnd_1663950 := by
    simpa [prefixWord, tailWord_1663950, baseEnd_1663950] using wordTrace_append hprefix tailTrace_1663950
  have hstable : (prefixWord ++ tailWord_1663950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663950).length < 2 ^ (prefixWord ++ tailWord_1663950).sum := by decide
  have hdescent : baseEnd_1663950 < baseStart_1663950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1663978 : List Nat := [3, 1, 3, 1, 2, 3, 1, 4, 1, 2, 2]
def baseStart_1663978 : Nat := 118140960795 + 1663978 * 2 ^ 59
def prefixEnd_1663978 : Nat := 4983230072969 + 3 ^ 40 * 1663978 * 2
def baseEnd_1663978 : Nat := 854420512507195912122511

theorem tailTrace_1663978 : CollatzResearch.WordTrace tailWord_1663978 prefixEnd_1663978 854420512507195912122511 := by
  unfold tailWord_1663978
  simp only [CollatzResearch.WordTrace]
  refine ⟨15172565891424841415600147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40460175710466243774933725 15172565891424841415600147)
  ·
    refine ⟨22758848837137262123400221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15172565891424841415600147 22758848837137262123400221)
    ·
      refine ⟨8534568313926473296275083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22758848837137262123400221 8534568313926473296275083)
      ·
        refine ⟨12801852470889709944412625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8534568313926473296275083 12801852470889709944412625)
        ·
          refine ⟨9601389353167282458309469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12801852470889709944412625 9601389353167282458309469)
          ·
            refine ⟨3600521007437730921866051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9601389353167282458309469 3600521007437730921866051)
            ·
              refine ⟨5400781511156596382799077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3600521007437730921866051 5400781511156596382799077)
              ·
                refine ⟨1012646533341861821774827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5400781511156596382799077 1012646533341861821774827)
                ·
                  refine ⟨1518969800012792732662241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1012646533341861821774827 1518969800012792732662241)
                  ·
                    refine ⟨1139227350009594549496681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1518969800012792732662241 1139227350009594549496681)
                    ·
                      refine ⟨854420512507195912122511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1139227350009594549496681 854420512507195912122511)
                      ·
                        rfl

theorem cell23_1663978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_1663978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1663978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1663978 prefixEnd_1663978 := by exact prefixLift 1663978
  have htrace : WordTrace (prefixWord ++ tailWord_1663978) baseStart_1663978 baseEnd_1663978 := by
    simpa [prefixWord, tailWord_1663978, baseEnd_1663978] using wordTrace_append hprefix tailTrace_1663978
  have hstable : (prefixWord ++ tailWord_1663978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1663978).length < 2 ^ (prefixWord ++ tailWord_1663978).sum := by decide
  have hdescent : baseEnd_1663978 < baseStart_1663978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1663978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664021 : List Nat := [1, 3, 2, 1, 4, 2, 1, 3, 1, 3, 2]
def baseStart_1664021 : Nat := 118140960795 + 1664021 * 2 ^ 59
def prefixEnd_1664021 : Nat := 4983230072969 + 3 ^ 40 * 1664021 * 2
def baseEnd_1664021 : Nat := 854442592175339243884813

theorem tailTrace_1664021 : CollatzResearch.WordTrace tailWord_1664021 prefixEnd_1664021 854442592175339243884813 := by
  unfold tailWord_1664021
  simp only [CollatzResearch.WordTrace]
  refine ⟨60691831904543584006215917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40461221269695722670810611 60691831904543584006215917)
  ·
    refine ⟨22759436964203844002330969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60691831904543584006215917 22759436964203844002330969)
    ·
      refine ⟨17069577723152883001748227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22759436964203844002330969 17069577723152883001748227)
      ·
        refine ⟨25604366584729324502622341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17069577723152883001748227 25604366584729324502622341)
        ·
          refine ⟨4800818734636748344241689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25604366584729324502622341 4800818734636748344241689)
          ·
            refine ⟨3600614050977561258181267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4800818734636748344241689 3600614050977561258181267)
            ·
              refine ⟨5400921076466341887271901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3600614050977561258181267 5400921076466341887271901)
              ·
                refine ⟨2025345403674878207726963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5400921076466341887271901 2025345403674878207726963)
                ·
                  refine ⟨3038018105512317311590445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2025345403674878207726963 3038018105512317311590445)
                  ·
                    refine ⟨1139256789567118991846417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3038018105512317311590445 1139256789567118991846417)
                    ·
                      refine ⟨854442592175339243884813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1139256789567118991846417 854442592175339243884813)
                      ·
                        rfl

theorem cell23_1664021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_1664021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664021 prefixEnd_1664021 := by exact prefixLift 1664021
  have htrace : WordTrace (prefixWord ++ tailWord_1664021) baseStart_1664021 baseEnd_1664021 := by
    simpa [prefixWord, tailWord_1664021, baseEnd_1664021] using wordTrace_append hprefix tailTrace_1664021
  have hstable : (prefixWord ++ tailWord_1664021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664021).length < 2 ^ (prefixWord ++ tailWord_1664021).sum := by decide
  have hdescent : baseEnd_1664021 < baseStart_1664021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664028 : List Nat := [2, 2, 3, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_1664028 : Nat := 118140960795 + 1664028 * 2 ^ 59
def prefixEnd_1664028 : Nat := 4983230072969 + 3 ^ 40 * 1664028 * 2
def baseEnd_1664028 : Nat := 854446186539920716497281

theorem tailTrace_1664028 : CollatzResearch.WordTrace tailWord_1664028 prefixEnd_1664028 854446186539920716497281 := by
  unfold tailWord_1664028
  simp only [CollatzResearch.WordTrace]
  refine ⟨30346043607759112100860369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40461391477012149467813825 30346043607759112100860369)
  ·
    refine ⟨22759532705819334075645277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30346043607759112100860369 22759532705819334075645277)
    ·
      refine ⟨8534824764682250278366979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22759532705819334075645277 8534824764682250278366979)
      ·
        refine ⟨12802237147023375417550469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8534824764682250278366979 12802237147023375417550469)
        ·
          refine ⟨2400419465066882890790713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12802237147023375417550469 2400419465066882890790713)
          ·
            refine ⟨1800314598800162168093035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2400419465066882890790713 1800314598800162168093035)
            ·
              refine ⟨2700471898200243252139553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800314598800162168093035 2700471898200243252139553)
              ·
                refine ⟨2025353923650182439104665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2700471898200243252139553 2025353923650182439104665)
                ·
                  refine ⟨1519015442737636829328499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2025353923650182439104665 1519015442737636829328499)
                  ·
                    refine ⟨2278523164106455243992749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1519015442737636829328499 2278523164106455243992749)
                    ·
                      refine ⟨854446186539920716497281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2278523164106455243992749 854446186539920716497281)
                      ·
                        rfl

theorem cell23_1664028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_1664028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664028 prefixEnd_1664028 := by exact prefixLift 1664028
  have htrace : WordTrace (prefixWord ++ tailWord_1664028) baseStart_1664028 baseEnd_1664028 := by
    simpa [prefixWord, tailWord_1664028, baseEnd_1664028] using wordTrace_append hprefix tailTrace_1664028
  have hstable : (prefixWord ++ tailWord_1664028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664028).length < 2 ^ (prefixWord ++ tailWord_1664028).sum := by decide
  have hdescent : baseEnd_1664028 < baseStart_1664028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664057 : List Nat := [1, 2, 1, 5, 2, 1, 2, 2, 7]
def baseStart_1664057 : Nat := 118140960795 + 1664057 * 2 ^ 59
def prefixEnd_1664057 : Nat := 4983230072969 + 3 ^ 40 * 1664057 * 2
def baseEnd_1664057 : Nat := 94940119719877900337183

theorem tailTrace_1664057 : CollatzResearch.WordTrace tailWord_1664057 prefixEnd_1664057 94940119719877900337183 := by
  unfold tailWord_1664057
  simp only [CollatzResearch.WordTrace]
  refine ⟨60693144932413162154526425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40462096621608774769684283 60693144932413162154526425)
  ·
    refine ⟨45519858699309871615894819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60693144932413162154526425 45519858699309871615894819)
    ·
      refine ⟨68279788048964807423842229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45519858699309871615894819 68279788048964807423842229)
      ·
        refine ⟨6401230129590450695985209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68279788048964807423842229 6401230129590450695985209)
        ·
          refine ⟨4800922597192838021988907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6401230129590450695985209 4800922597192838021988907)
          ·
            refine ⟨7201383895789257032983361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4800922597192838021988907 7201383895789257032983361)
            ·
              refine ⟨5401037921841942774737521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7201383895789257032983361 5401037921841942774737521)
              ·
                refine ⟨4050778441381457081053141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5401037921841942774737521 4050778441381457081053141)
                ·
                  refine ⟨94940119719877900337183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4050778441381457081053141 94940119719877900337183)
                  ·
                    rfl

theorem cell23_1664057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 7].length) (baseStart_1664057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664057 prefixEnd_1664057 := by exact prefixLift 1664057
  have htrace : WordTrace (prefixWord ++ tailWord_1664057) baseStart_1664057 baseEnd_1664057 := by
    simpa [prefixWord, tailWord_1664057, baseEnd_1664057] using wordTrace_append hprefix tailTrace_1664057
  have hstable : (prefixWord ++ tailWord_1664057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664057).length < 2 ^ (prefixWord ++ tailWord_1664057).sum := by decide
  have hdescent : baseEnd_1664057 < baseStart_1664057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664074 : List Nat := [3, 1, 2, 1, 1, 2, 5, 3, 5]
def baseStart_1664074 : Nat := 118140960795 + 1664074 * 2 ^ 59
def prefixEnd_1664074 : Nat := 4983230072969 + 3 ^ 40 * 1664074 * 2
def baseEnd_1664074 : Nat := 94941089627780837391341

theorem tailTrace_1664074 : CollatzResearch.WordTrace tailWord_1664074 prefixEnd_1664074 94941089627780837391341 := by
  unfold tailWord_1664074
  simp only [CollatzResearch.WordTrace]
  refine ⟨15173441243337893514473819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40462509982234382705263517 15173441243337893514473819)
  ·
    refine ⟨22760161865006840271710729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15173441243337893514473819 22760161865006840271710729)
    ·
      refine ⟨17070121398755130203783047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22760161865006840271710729 17070121398755130203783047)
      ·
        refine ⟨25605182098132695305674571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17070121398755130203783047 25605182098132695305674571)
        ·
          refine ⟨38407773147199042958511857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25605182098132695305674571 38407773147199042958511857)
          ·
            refine ⟨28805829860399282218883893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38407773147199042958511857 28805829860399282218883893)
            ·
              refine ⟨2700546549412432708020365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28805829860399282218883893 2700546549412432708020365)
              ·
                refine ⟨1012704956029662265507637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2700546549412432708020365 1012704956029662265507637)
                ·
                  refine ⟨94941089627780837391341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1012704956029662265507637 94941089627780837391341)
                  ·
                    rfl

theorem cell23_1664074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 5].length) (baseStart_1664074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664074 prefixEnd_1664074 := by exact prefixLift 1664074
  have htrace : WordTrace (prefixWord ++ tailWord_1664074) baseStart_1664074 baseEnd_1664074 := by
    simpa [prefixWord, tailWord_1664074, baseEnd_1664074] using wordTrace_append hprefix tailTrace_1664074
  have hstable : (prefixWord ++ tailWord_1664074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664074).length < 2 ^ (prefixWord ++ tailWord_1664074).sum := by decide
  have hdescent : baseEnd_1664074 < baseStart_1664074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664080 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 7]
def baseStart_1664080 : Nat := 118140960795 + 1664080 * 2 ^ 59
def prefixEnd_1664080 : Nat := 4983230072969 + 3 ^ 40 * 1664080 * 2
def baseEnd_1664080 : Nat := 854472887533954513047041

theorem tailTrace_1664080 : CollatzResearch.WordTrace tailWord_1664080 prefixEnd_1664080 854472887533954513047041 := by
  unfold tailWord_1664080
  simp only [CollatzResearch.WordTrace]
  refine ⟨30346991905664918541306847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40462655874219891388409129 30346991905664918541306847)
  ·
    refine ⟨45520487858497377811960271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30346991905664918541306847 45520487858497377811960271)
    ·
      refine ⟨68280731787746066717940407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45520487858497377811960271 68280731787746066717940407)
      ·
        refine ⟨102421097681619100076910611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68280731787746066717940407 102421097681619100076910611)
        ·
          refine ⟨153631646522428650115365917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102421097681619100076910611 153631646522428650115365917)
          ·
            refine ⟨57611867445910743793262219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153631646522428650115365917 57611867445910743793262219)
            ·
              refine ⟨86417801168866115689893329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57611867445910743793262219 86417801168866115689893329)
              ·
                refine ⟨64813350876649586767419997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86417801168866115689893329 64813350876649586767419997)
                ·
                  refine ⟨24305006578743595037782499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64813350876649586767419997 24305006578743595037782499)
                  ·
                    refine ⟨36457509868115392556673749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24305006578743595037782499 36457509868115392556673749)
                    ·
                      refine ⟨854472887533954513047041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36457509868115392556673749 854472887533954513047041)
                      ·
                        rfl

theorem cell23_1664080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_1664080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664080 prefixEnd_1664080 := by exact prefixLift 1664080
  have htrace : WordTrace (prefixWord ++ tailWord_1664080) baseStart_1664080 baseEnd_1664080 := by
    simpa [prefixWord, tailWord_1664080, baseEnd_1664080] using wordTrace_append hprefix tailTrace_1664080
  have hstable : (prefixWord ++ tailWord_1664080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664080).length < 2 ^ (prefixWord ++ tailWord_1664080).sum := by decide
  have hdescent : baseEnd_1664080 < baseStart_1664080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664124 : List Nat := [2, 2, 2, 1, 1, 3, 4, 1, 2, 1, 4]
def baseStart_1664124 : Nat := 118140960795 + 1664124 * 2 ^ 59
def prefixEnd_1664124 : Nat := 4983230072969 + 3 ^ 40 * 1664124 * 2
def baseEnd_1664124 : Nat := 854495480682752340896839

theorem tailTrace_1664124 : CollatzResearch.WordTrace tailWord_1664124 prefixEnd_1664124 854495480682752340896839 := by
  unfold tailWord_1664124
  simp only [CollatzResearch.WordTrace]
  refine ⟨30347794311585216298607713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40463725748780288398143617 30347794311585216298607713)
  ·
    refine ⟨22760845733688912223955785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30347794311585216298607713 22760845733688912223955785)
    ·
      refine ⟨17070634300266684167966839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22760845733688912223955785 17070634300266684167966839)
      ·
        refine ⟨25605951450400026251950259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17070634300266684167966839 25605951450400026251950259)
        ·
          refine ⟨38408927175600039377925389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25605951450400026251950259 38408927175600039377925389)
          ·
            refine ⟨14403347690850014766722021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38408927175600039377925389 14403347690850014766722021)
            ·
              refine ⟨2700627692034377768760379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14403347690850014766722021 2700627692034377768760379)
              ·
                refine ⟨4050941538051566653140569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2700627692034377768760379 4050941538051566653140569)
                ·
                  refine ⟨3038206153538674989855427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4050941538051566653140569 3038206153538674989855427)
                  ·
                    refine ⟨4557309230308012484783141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3038206153538674989855427 4557309230308012484783141)
                    ·
                      refine ⟨854495480682752340896839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4557309230308012484783141 854495480682752340896839)
                      ·
                        rfl

theorem cell23_1664124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_1664124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664124 prefixEnd_1664124 := by exact prefixLift 1664124
  have htrace : WordTrace (prefixWord ++ tailWord_1664124) baseStart_1664124 baseEnd_1664124 := by
    simpa [prefixWord, tailWord_1664124, baseEnd_1664124] using wordTrace_append hprefix tailTrace_1664124
  have hstable : (prefixWord ++ tailWord_1664124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664124).length < 2 ^ (prefixWord ++ tailWord_1664124).sum := by decide
  have hdescent : baseEnd_1664124 < baseStart_1664124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664147 : List Nat := [1, 1, 1, 2, 1, 2, 5, 4, 6]
def baseStart_1664147 : Nat := 118140960795 + 1664147 * 2 ^ 59
def prefixEnd_1664147 : Nat := 4983230072969 + 3 ^ 40 * 1664147 * 2
def baseEnd_1664147 : Nat := 94945254526422861212137

theorem tailTrace_1664147 : CollatzResearch.WordTrace tailWord_1664147 prefixEnd_1664147 94945254526422861212137 := by
  unfold tailWord_1664147
  simp only [CollatzResearch.WordTrace]
  refine ⟨60696427502087107525302695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40464285001391405016868463 60696427502087107525302695)
  ·
    refine ⟨91044641253130661287954043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60696427502087107525302695 91044641253130661287954043)
    ·
      refine ⟨136566961879695991931931065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91044641253130661287954043 136566961879695991931931065)
      ·
        refine ⟨102425221409771993948948299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136566961879695991931931065 102425221409771993948948299)
        ·
          refine ⟨153637832114657990923422449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102425221409771993948948299 153637832114657990923422449)
          ·
            refine ⟨115228374085993493192566837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153637832114657990923422449 115228374085993493192566837)
            ·
              refine ⟨10802660070561889986803141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115228374085993493192566837 10802660070561889986803141)
              ·
                refine ⟨2025498763230354372525589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10802660070561889986803141 2025498763230354372525589)
                ·
                  refine ⟨94945254526422861212137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2025498763230354372525589 94945254526422861212137)
                  ·
                    rfl

theorem cell23_1664147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 6].length) (baseStart_1664147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664147 prefixEnd_1664147 := by exact prefixLift 1664147
  have htrace : WordTrace (prefixWord ++ tailWord_1664147) baseStart_1664147 baseEnd_1664147 := by
    simpa [prefixWord, tailWord_1664147, baseEnd_1664147] using wordTrace_append hprefix tailTrace_1664147
  have hstable : (prefixWord ++ tailWord_1664147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664147).length < 2 ^ (prefixWord ++ tailWord_1664147).sum := by decide
  have hdescent : baseEnd_1664147 < baseStart_1664147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664158 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_1664158 : Nat := 118140960795 + 1664158 * 2 ^ 59
def prefixEnd_1664158 : Nat := 4983230072969 + 3 ^ 40 * 1664158 * 2
def baseEnd_1664158 : Nat := 854512939025005207871683

theorem tailTrace_1664158 : CollatzResearch.WordTrace tailWord_1664158 prefixEnd_1664158 854512939025005207871683 := by
  unfold tailWord_1664158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7587103588130907050494141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40464552470031504269302085 7587103588130907050494141)
  ·
    refine ⟨2845163845549090143935303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7587103588130907050494141 2845163845549090143935303)
    ·
      refine ⟨4267745768323635215902955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2845163845549090143935303 4267745768323635215902955)
      ·
        refine ⟨6401618652485452823854433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4267745768323635215902955 6401618652485452823854433)
        ·
          refine ⟨4801213989364089617890825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6401618652485452823854433 4801213989364089617890825)
          ·
            refine ⟨3600910492023067213418119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4801213989364089617890825 3600910492023067213418119)
            ·
              refine ⟨5401365738034600820127179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3600910492023067213418119 5401365738034600820127179)
              ·
                refine ⟨8102048607051901230190769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5401365738034600820127179 8102048607051901230190769)
                ·
                  refine ⟨6076536455288925922643077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8102048607051901230190769 6076536455288925922643077)
                  ·
                    refine ⟨1139350585366673610495577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6076536455288925922643077 1139350585366673610495577)
                    ·
                      refine ⟨854512939025005207871683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1139350585366673610495577 854512939025005207871683)
                      ·
                        rfl

theorem cell23_1664158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_1664158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664158 prefixEnd_1664158 := by exact prefixLift 1664158
  have htrace : WordTrace (prefixWord ++ tailWord_1664158) baseStart_1664158 baseEnd_1664158 := by
    simpa [prefixWord, tailWord_1664158, baseEnd_1664158] using wordTrace_append hprefix tailTrace_1664158
  have hstable : (prefixWord ++ tailWord_1664158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664158).length < 2 ^ (prefixWord ++ tailWord_1664158).sum := by decide
  have hdescent : baseEnd_1664158 < baseStart_1664158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664164 : List Nat := [2, 3, 1, 2, 3, 1, 2, 3, 6]
def baseStart_1664164 : Nat := 118140960795 + 1664164 * 2 ^ 59
def prefixEnd_1664164 : Nat := 4983230072969 + 3 ^ 40 * 1664164 * 2
def baseEnd_1664164 : Nat := 94946224434325798266295

theorem tailTrace_1664164 : CollatzResearch.WordTrace tailWord_1664164 prefixEnd_1664164 94946224434325798266295 := by
  unfold tailWord_1664164
  simp only [CollatzResearch.WordTrace]
  refine ⟨30348523771512759714335773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40464698362017012952447697 30348523771512759714335773)
  ·
    refine ⟨11380696414317284892875915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30348523771512759714335773 11380696414317284892875915)
    ·
      refine ⟨17071044621475927339313873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11380696414317284892875915 17071044621475927339313873)
      ·
        refine ⟨12803283466106945504485405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17071044621475927339313873 12803283466106945504485405)
        ·
          refine ⟨4801231299790104564182027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12803283466106945504485405 4801231299790104564182027)
          ·
            refine ⟨7201846949685156846273041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4801231299790104564182027 7201846949685156846273041)
            ·
              refine ⟨5401385212263867634704781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7201846949685156846273041 5401385212263867634704781)
              ·
                refine ⟨2025519454598950363014293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5401385212263867634704781 2025519454598950363014293)
                ·
                  refine ⟨94946224434325798266295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2025519454598950363014293 94946224434325798266295)
                  ·
                    rfl

theorem cell23_1664164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_1664164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664164 prefixEnd_1664164 := by exact prefixLift 1664164
  have htrace : WordTrace (prefixWord ++ tailWord_1664164) baseStart_1664164 baseEnd_1664164 := by
    simpa [prefixWord, tailWord_1664164, baseEnd_1664164] using wordTrace_append hprefix tailTrace_1664164
  have hstable : (prefixWord ++ tailWord_1664164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664164).length < 2 ^ (prefixWord ++ tailWord_1664164).sum := by decide
  have hdescent : baseEnd_1664164 < baseStart_1664164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664224 : List Nat := [2, 1, 1, 3, 1, 4, 3, 1, 1, 6]
def baseStart_1664224 : Nat := 118140960795 + 1664224 * 2 ^ 59
def prefixEnd_1664224 : Nat := 4983230072969 + 3 ^ 40 * 1664224 * 2
def baseEnd_1664224 : Nat := 284848942916067316548793

theorem tailTrace_1664224 : CollatzResearch.WordTrace tailWord_1664224 prefixEnd_1664224 284848942916067316548793 := by
  unfold tailWord_1664224
  simp only [CollatzResearch.WordTrace]
  refine ⟨30349617961404074837927863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40466157281872099783903817 30349617961404074837927863)
  ·
    refine ⟨45524426942106112256891795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30349617961404074837927863 45524426942106112256891795)
    ·
      refine ⟨68286640413159168385337693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45524426942106112256891795 68286640413159168385337693)
      ·
        refine ⟨25607490154934688144501635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68286640413159168385337693 25607490154934688144501635)
        ·
          refine ⟨38411235232402032216752453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25607490154934688144501635 38411235232402032216752453)
          ·
            refine ⟨7202106606075381040641085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38411235232402032216752453 7202106606075381040641085)
            ·
              refine ⟨2700789977278267890240407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7202106606075381040641085 2700789977278267890240407)
              ·
                refine ⟨4051184965917401835360611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2700789977278267890240407 4051184965917401835360611)
                ·
                  refine ⟨6076777448876102753040917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4051184965917401835360611 6076777448876102753040917)
                  ·
                    refine ⟨284848942916067316548793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6076777448876102753040917 284848942916067316548793)
                    ·
                      rfl

theorem cell23_1664224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 1, 6].length) (baseStart_1664224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664224 prefixEnd_1664224 := by exact prefixLift 1664224
  have htrace : WordTrace (prefixWord ++ tailWord_1664224) baseStart_1664224 baseEnd_1664224 := by
    simpa [prefixWord, tailWord_1664224, baseEnd_1664224] using wordTrace_append hprefix tailTrace_1664224
  have hstable : (prefixWord ++ tailWord_1664224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664224).length < 2 ^ (prefixWord ++ tailWord_1664224).sum := by decide
  have hdescent : baseEnd_1664224 < baseStart_1664224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664242 : List Nat := [3, 2, 1, 3, 3, 2, 1, 3, 1, 1, 3]
def baseStart_1664242 : Nat := 118140960795 + 1664242 * 2 ^ 59
def prefixEnd_1664242 : Nat := 4983230072969 + 3 ^ 40 * 1664242 * 2
def baseEnd_1664242 : Nat := 854556071399982879221297

theorem tailTrace_1664242 : CollatzResearch.WordTrace tailWord_1664242 prefixEnd_1664242 854556071399982879221297 := by
  unfold tailWord_1664242
  simp only [CollatzResearch.WordTrace]
  refine ⟨15174973109185734687502745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40466594957828625833340653 15174973109185734687502745)
  ·
    refine ⟨11381229831889301015627059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15174973109185734687502745 11381229831889301015627059)
    ·
      refine ⟨17071844747833951523440589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11381229831889301015627059 17071844747833951523440589)
      ·
        refine ⟨6401941780437731821290221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17071844747833951523440589 6401941780437731821290221)
        ·
          refine ⟨2400728167664149432983833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6401941780437731821290221 2400728167664149432983833)
          ·
            refine ⟨1800546125748112074737875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2400728167664149432983833 1800546125748112074737875)
            ·
              refine ⟨2700819188622168112106813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800546125748112074737875 2700819188622168112106813)
              ·
                refine ⟨1012807195733313042040055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2700819188622168112106813 1012807195733313042040055)
                ·
                  refine ⟨1519210793599969563060083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1012807195733313042040055 1519210793599969563060083)
                  ·
                    refine ⟨2278816190399954344590125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1519210793599969563060083 2278816190399954344590125)
                    ·
                      refine ⟨854556071399982879221297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2278816190399954344590125 854556071399982879221297)
                      ·
                        rfl

theorem cell23_1664242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_1664242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664242 prefixEnd_1664242 := by exact prefixLift 1664242
  have htrace : WordTrace (prefixWord ++ tailWord_1664242) baseStart_1664242 baseEnd_1664242 := by
    simpa [prefixWord, tailWord_1664242, baseEnd_1664242] using wordTrace_append hprefix tailTrace_1664242
  have hstable : (prefixWord ++ tailWord_1664242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664242).length < 2 ^ (prefixWord ++ tailWord_1664242).sum := by decide
  have hdescent : baseEnd_1664242 < baseStart_1664242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664254 : List Nat := [4, 2, 2, 1, 1, 2, 11]
def baseStart_1664254 : Nat := 118140960795 + 1664254 * 2 ^ 59
def prefixEnd_1664254 : Nat := 4983230072969 + 3 ^ 40 * 1664254 * 2
def baseEnd_1664254 : Nat := 10550151026763417682361

theorem tailTrace_1664254 : CollatzResearch.WordTrace tailWord_1664254 prefixEnd_1664254 10550151026763417682361 := by
  unfold tailWord_1664254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7587541264087433099930977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40466886741799643199631877 7587541264087433099930977)
  ·
    refine ⟨5690655948065574824948233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7587541264087433099930977 5690655948065574824948233)
    ·
      refine ⟨4267991961049181118711175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5690655948065574824948233 4267991961049181118711175)
      ·
        refine ⟨6401987941573771678066763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4267991961049181118711175 6401987941573771678066763)
        ·
          refine ⟨9602981912360657517100145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6401987941573771678066763 9602981912360657517100145)
          ·
            refine ⟨7202236434270493137825109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9602981912360657517100145 7202236434270493137825109)
            ·
              refine ⟨10550151026763417682361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7202236434270493137825109 10550151026763417682361)
              ·
                rfl

theorem cell23_1664254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 11].length) (baseStart_1664254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664254 prefixEnd_1664254 := by exact prefixLift 1664254
  have htrace : WordTrace (prefixWord ++ tailWord_1664254) baseStart_1664254 baseEnd_1664254 := by
    simpa [prefixWord, tailWord_1664254, baseEnd_1664254] using wordTrace_append hprefix tailTrace_1664254
  have hstable : (prefixWord ++ tailWord_1664254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664254).length < 2 ^ (prefixWord ++ tailWord_1664254).sum := by decide
  have hdescent : baseEnd_1664254 < baseStart_1664254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664285 : List Nat := [1, 4, 2, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_1664285 : Nat := 118140960795 + 1664285 * 2 ^ 59
def prefixEnd_1664285 : Nat := 4983230072969 + 3 ^ 40 * 1664285 * 2
def baseEnd_1664285 : Nat := 854578151068126210983599

theorem tailTrace_1664285 : CollatzResearch.WordTrace tailWord_1664285 prefixEnd_1664285 854578151068126210983599 := by
  unfold tailWord_1664285
  simp only [CollatzResearch.WordTrace]
  refine ⟨60701460775587157093826309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40467640517058104729217539 60701460775587157093826309)
  ·
    refine ⟨11381523895422591955092433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60701460775587157093826309 11381523895422591955092433)
    ·
      refine ⟨8536142921566943966319325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11381523895422591955092433 8536142921566943966319325)
      ·
        refine ⟨3201053595587603987369747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8536142921566943966319325 3201053595587603987369747)
        ·
          refine ⟨4801580393381405981054621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3201053595587603987369747 4801580393381405981054621)
          ·
            refine ⟨1800592647518027242895483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4801580393381405981054621 1800592647518027242895483)
            ·
              refine ⟨2700888971277040864343225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800592647518027242895483 2700888971277040864343225)
              ·
                refine ⟨2025666728457780648257419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2700888971277040864343225 2025666728457780648257419)
                ·
                  refine ⟨3038500092686670972386129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2025666728457780648257419 3038500092686670972386129)
                  ·
                    refine ⟨2278875069515003229289597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3038500092686670972386129 2278875069515003229289597)
                    ·
                      refine ⟨854578151068126210983599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2278875069515003229289597 854578151068126210983599)
                      ·
                        rfl

theorem cell23_1664285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_1664285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664285 prefixEnd_1664285 := by exact prefixLift 1664285
  have htrace : WordTrace (prefixWord ++ tailWord_1664285) baseStart_1664285 baseEnd_1664285 := by
    simpa [prefixWord, tailWord_1664285, baseEnd_1664285] using wordTrace_append hprefix tailTrace_1664285
  have hstable : (prefixWord ++ tailWord_1664285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664285).length < 2 ^ (prefixWord ++ tailWord_1664285).sum := by decide
  have hdescent : baseEnd_1664285 < baseStart_1664285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664298 : List Nat := [3, 1, 4, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_1664298 : Nat := 118140960795 + 1664298 * 2 ^ 59
def prefixEnd_1664298 : Nat := 4983230072969 + 3 ^ 40 * 1664298 * 2
def baseEnd_1664298 : Nat := 854584826316634660121039

theorem tailTrace_1664298 : CollatzResearch.WordTrace tailWord_1664298 prefixEnd_1664298 854584826316634660121039 := by
  unfold tailWord_1664298
  simp only [CollatzResearch.WordTrace]
  refine ⟨15175483731135015078512387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40467956616360040209366365 15175483731135015078512387)
  ·
    refine ⟨22763225596702522617768581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15175483731135015078512387 22763225596702522617768581)
    ·
      refine ⟨4268104799381722990831609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22763225596702522617768581 4268104799381722990831609)
      ·
        refine ⟨3201078599536292243123707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4268104799381722990831609 3201078599536292243123707)
        ·
          refine ⟨4801617899304438364685561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3201078599536292243123707 4801617899304438364685561)
          ·
            refine ⟨3601213424478328773514171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4801617899304438364685561 3601213424478328773514171)
            ·
              refine ⟨5401820136717493160271257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3601213424478328773514171 5401820136717493160271257)
              ·
                refine ⟨4051365102538119870203443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5401820136717493160271257 4051365102538119870203443)
                ·
                  refine ⟨6077047653807179805305165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4051365102538119870203443 6077047653807179805305165)
                  ·
                    refine ⟨2278892870177692426989437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6077047653807179805305165 2278892870177692426989437)
                    ·
                      refine ⟨854584826316634660121039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2278892870177692426989437 854584826316634660121039)
                      ·
                        rfl

theorem cell23_1664298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_1664298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664298 prefixEnd_1664298 := by exact prefixLift 1664298
  have htrace : WordTrace (prefixWord ++ tailWord_1664298) baseStart_1664298 baseEnd_1664298 := by
    simpa [prefixWord, tailWord_1664298, baseEnd_1664298] using wordTrace_append hprefix tailTrace_1664298
  have hstable : (prefixWord ++ tailWord_1664298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664298).length < 2 ^ (prefixWord ++ tailWord_1664298).sum := by decide
  have hdescent : baseEnd_1664298 < baseStart_1664298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664314 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 2, 6]
def baseStart_1664314 : Nat := 118140960795 + 1664314 * 2 ^ 59
def prefixEnd_1664314 : Nat := 4983230072969 + 3 ^ 40 * 1664314 * 2
def baseEnd_1664314 : Nat := 284864347335702199173655

theorem tailTrace_1664314 : CollatzResearch.WordTrace tailWord_1664314 prefixEnd_1664314 284864347335702199173655 := by
  unfold tailWord_1664314
  simp only [CollatzResearch.WordTrace]
  refine ⟨15175629623120523761657999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40468345661654730031087997 15175629623120523761657999)
  ·
    refine ⟨22763444434680785642486999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15175629623120523761657999 22763444434680785642486999)
    ·
      refine ⟨34145166652021178463730499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22763444434680785642486999 34145166652021178463730499)
      ·
        refine ⟨51217749978031767695595749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34145166652021178463730499 51217749978031767695595749)
        ·
          refine ⟨9603328120880956442924203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51217749978031767695595749 9603328120880956442924203)
          ·
            refine ⟨14404992181321434664386305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9603328120880956442924203 14404992181321434664386305)
            ·
              refine ⟨10803744135991075998289729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14404992181321434664386305 10803744135991075998289729)
              ·
                refine ⟨8102808101993306998717297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10803744135991075998289729 8102808101993306998717297)
                ·
                  refine ⟨6077106076494980249037973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8102808101993306998717297 6077106076494980249037973)
                  ·
                    refine ⟨284864347335702199173655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6077106076494980249037973 284864347335702199173655)
                    ·
                      rfl

theorem cell23_1664314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_1664314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664314 prefixEnd_1664314 := by exact prefixLift 1664314
  have htrace : WordTrace (prefixWord ++ tailWord_1664314) baseStart_1664314 baseEnd_1664314 := by
    simpa [prefixWord, tailWord_1664314, baseEnd_1664314] using wordTrace_append hprefix tailTrace_1664314
  have hstable : (prefixWord ++ tailWord_1664314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664314).length < 2 ^ (prefixWord ++ tailWord_1664314).sum := by decide
  have hdescent : baseEnd_1664314 < baseStart_1664314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664321 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1664321 : Nat := 118140960795 + 1664321 * 2 ^ 59
def prefixEnd_1664321 : Nat := 4983230072969 + 3 ^ 40 * 1664321 * 2
def baseEnd_1664321 : Nat := 854596636371688070133433

theorem tailTrace_1664321 : CollatzResearch.WordTrace tailWord_1664321 prefixEnd_1664321 854596636371688070133433 := by
  unfold tailWord_1664321
  simp only [CollatzResearch.WordTrace]
  refine ⟨60702773803456735242136817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40468515868971156828091211 60702773803456735242136817)
  ·
    refine ⟨45527080352592551431602613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60702773803456735242136817 45527080352592551431602613)
    ·
      refine ⟨4268163783055551696712745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45527080352592551431602613 4268163783055551696712745)
      ·
        refine ⟨3201122837291663772534559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4268163783055551696712745 3201122837291663772534559)
        ·
          refine ⟨4801684255937495658801839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3201122837291663772534559 4801684255937495658801839)
          ·
            refine ⟨7202526383906243488202759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4801684255937495658801839 7202526383906243488202759)
            ·
              refine ⟨10803789575859365232304139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7202526383906243488202759 10803789575859365232304139)
              ·
                refine ⟨16205684363789047848456209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10803789575859365232304139 16205684363789047848456209)
                ·
                  refine ⟨12154263272841785886342157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16205684363789047848456209 12154263272841785886342157)
                  ·
                    refine ⟨4557848727315669707378309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12154263272841785886342157 4557848727315669707378309)
                    ·
                      refine ⟨854596636371688070133433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4557848727315669707378309 854596636371688070133433)
                      ·
                        rfl

theorem cell23_1664321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1664321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664321 prefixEnd_1664321 := by exact prefixLift 1664321
  have htrace : WordTrace (prefixWord ++ tailWord_1664321) baseStart_1664321 baseEnd_1664321 := by
    simpa [prefixWord, tailWord_1664321, baseEnd_1664321] using wordTrace_append hprefix tailTrace_1664321
  have hstable : (prefixWord ++ tailWord_1664321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664321).length < 2 ^ (prefixWord ++ tailWord_1664321).sum := by decide
  have hdescent : baseEnd_1664321 < baseStart_1664321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664338 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2]
def baseStart_1664338 : Nat := 118140960795 + 1664338 * 2 ^ 59
def prefixEnd_1664338 : Nat := 4983230072969 + 3 ^ 40 * 1664338 * 2
def baseEnd_1664338 : Nat := 854605365542814503620855

theorem tailTrace_1664338 : CollatzResearch.WordTrace tailWord_1664338 prefixEnd_1664338 854605365542814503620855 := by
  unfold tailWord_1664338
  simp only [CollatzResearch.WordTrace]
  refine ⟨15175848461098786786376417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40468929229596764763670445 15175848461098786786376417)
  ·
    refine ⟨11381886345824090089782313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15175848461098786786376417 11381886345824090089782313)
    ·
      refine ⟨8536414759368067567336735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11381886345824090089782313 8536414759368067567336735)
      ·
        refine ⟨12804622139052101351005103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8536414759368067567336735 12804622139052101351005103)
        ·
          refine ⟨19206933208578152026507655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12804622139052101351005103 19206933208578152026507655)
          ·
            refine ⟨28810399812867228039761483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19206933208578152026507655 28810399812867228039761483)
            ·
              refine ⟨43215599719300842059642225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28810399812867228039761483 43215599719300842059642225)
              ·
                refine ⟨32411699789475631544731669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43215599719300842059642225 32411699789475631544731669)
                ·
                  refine ⟨1519298427631670228659297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32411699789475631544731669 1519298427631670228659297)
                  ·
                    refine ⟨1139473820723752671494473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1519298427631670228659297 1139473820723752671494473)
                    ·
                      refine ⟨854605365542814503620855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1139473820723752671494473 854605365542814503620855)
                      ·
                        rfl

theorem cell23_1664338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_1664338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664338 prefixEnd_1664338 := by exact prefixLift 1664338
  have htrace : WordTrace (prefixWord ++ tailWord_1664338) baseStart_1664338 baseEnd_1664338 := by
    simpa [prefixWord, tailWord_1664338, baseEnd_1664338] using wordTrace_append hprefix tailTrace_1664338
  have hstable : (prefixWord ++ tailWord_1664338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664338).length < 2 ^ (prefixWord ++ tailWord_1664338).sum := by decide
  have hdescent : baseEnd_1664338 < baseStart_1664338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664344 : List Nat := [2, 1, 2, 2, 1, 1, 5, 2, 7]
def baseStart_1664344 : Nat := 118140960795 + 1664344 * 2 ^ 59
def prefixEnd_1664344 : Nat := 4983230072969 + 3 ^ 40 * 1664344 * 2
def baseEnd_1664344 : Nat := 94956494047415720016203

theorem tailTrace_1664344 : CollatzResearch.WordTrace tailWord_1664344 prefixEnd_1664344 94956494047415720016203 := by
  unfold tailWord_1664344
  simp only [CollatzResearch.WordTrace]
  refine ⟨30351806341186705085112043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40469075121582273446816057 30351806341186705085112043)
  ·
    refine ⟨45527709511780057627668065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30351806341186705085112043 45527709511780057627668065)
    ·
      refine ⟨34145782133835043220751049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45527709511780057627668065 34145782133835043220751049)
      ·
        refine ⟨25609336600376282415563287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34145782133835043220751049 25609336600376282415563287)
        ·
          refine ⟨38414004900564423623344931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25609336600376282415563287 38414004900564423623344931)
          ·
            refine ⟨57621007350846635435017397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38414004900564423623344931 57621007350846635435017397)
            ·
              refine ⟨5401969439141872072032881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57621007350846635435017397 5401969439141872072032881)
              ·
                refine ⟨4051477079356404054024661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5401969439141872072032881 4051477079356404054024661)
                ·
                  refine ⟨94956494047415720016203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4051477079356404054024661 94956494047415720016203)
                  ·
                    rfl

theorem cell23_1664344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 7].length) (baseStart_1664344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664344 prefixEnd_1664344 := by exact prefixLift 1664344
  have htrace : WordTrace (prefixWord ++ tailWord_1664344) baseStart_1664344 baseEnd_1664344 := by
    simpa [prefixWord, tailWord_1664344, baseEnd_1664344] using wordTrace_append hprefix tailTrace_1664344
  have hstable : (prefixWord ++ tailWord_1664344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664344).length < 2 ^ (prefixWord ++ tailWord_1664344).sum := by decide
  have hdescent : baseEnd_1664344 < baseStart_1664344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664359 : List Nat := [1, 1, 5, 1, 5, 1, 2, 1, 1, 3, 2]
def baseStart_1664359 : Nat := 118140960795 + 1664359 * 2 ^ 59
def prefixEnd_1664359 : Nat := 4983230072969 + 3 ^ 40 * 1664359 * 2
def baseEnd_1664359 : Nat := 854616148636558921458259

theorem tailTrace_1664359 : CollatzResearch.WordTrace tailWord_1664359 prefixEnd_1664359 854616148636558921458259 := by
  unfold tailWord_1664359
  simp only [CollatzResearch.WordTrace]
  refine ⟨60704159777319067732020131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40469439851546045154680087 60704159777319067732020131)
  ·
    refine ⟨91056239665978601598030197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60704159777319067732020131 91056239665978601598030197)
    ·
      refine ⟨8536522468685493899815331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91056239665978601598030197 8536522468685493899815331)
      ·
        refine ⟨12804783703028240849722997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8536522468685493899815331 12804783703028240849722997)
        ·
          refine ⟨1200448472158897579661531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12804783703028240849722997 1200448472158897579661531)
          ·
            refine ⟨1800672708238346369492297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1200448472158897579661531 1800672708238346369492297)
            ·
              refine ⟨1350504531178759777119223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1800672708238346369492297 1350504531178759777119223)
              ·
                refine ⟨2025756796768139665678835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350504531178759777119223 2025756796768139665678835)
                ·
                  refine ⟨3038635195152209498518253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2025756796768139665678835 3038635195152209498518253)
                  ·
                    refine ⟨1139488198182078561944345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3038635195152209498518253 1139488198182078561944345)
                    ·
                      refine ⟨854616148636558921458259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1139488198182078561944345 854616148636558921458259)
                      ·
                        rfl

theorem cell23_1664359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_1664359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664359 prefixEnd_1664359 := by exact prefixLift 1664359
  have htrace : WordTrace (prefixWord ++ tailWord_1664359) baseStart_1664359 baseEnd_1664359 := by
    simpa [prefixWord, tailWord_1664359, baseEnd_1664359] using wordTrace_append hprefix tailTrace_1664359
  have hstable : (prefixWord ++ tailWord_1664359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664359).length < 2 ^ (prefixWord ++ tailWord_1664359).sum := by decide
  have hdescent : baseEnd_1664359 < baseStart_1664359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664384 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 5]
def baseStart_1664384 : Nat := 118140960795 + 1664384 * 2 ^ 59
def prefixEnd_1664384 : Nat := 4983230072969 + 3 ^ 40 * 1664384 * 2
def baseEnd_1664384 : Nat := 854628985652921323645643

theorem tailTrace_1664384 : CollatzResearch.WordTrace tailWord_1664384 prefixEnd_1664384 854628985652921323645643 := by
  unfold tailWord_1664384
  simp only [CollatzResearch.WordTrace]
  refine ⟨30352535801114248500840103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40470047734818998001120137 30352535801114248500840103)
  ·
    refine ⟨45528803701671372751260155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30352535801114248500840103 45528803701671372751260155)
    ·
      refine ⟨68293205552507059126890233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45528803701671372751260155 68293205552507059126890233)
      ·
        refine ⟨51219904164380294345167675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68293205552507059126890233 51219904164380294345167675)
        ·
          refine ⟨76829856246570441517751513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51219904164380294345167675 76829856246570441517751513)
          ·
            refine ⟨57622392184927831138313635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76829856246570441517751513 57622392184927831138313635)
            ·
              refine ⟨86433588277391746707470453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57622392184927831138313635 86433588277391746707470453)
              ·
                refine ⟨8103148901005476253825355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86433588277391746707470453 8103148901005476253825355)
                ·
                  refine ⟨12154723351508214380738033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8103148901005476253825355 12154723351508214380738033)
                  ·
                    refine ⟨9116042513631160785553525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12154723351508214380738033 9116042513631160785553525)
                    ·
                      refine ⟨854628985652921323645643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9116042513631160785553525 854628985652921323645643)
                      ·
                        rfl

theorem cell23_1664384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_1664384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664384 prefixEnd_1664384 := by exact prefixLift 1664384
  have htrace : WordTrace (prefixWord ++ tailWord_1664384) baseStart_1664384 baseEnd_1664384 := by
    simpa [prefixWord, tailWord_1664384, baseEnd_1664384] using wordTrace_append hprefix tailTrace_1664384
  have hstable : (prefixWord ++ tailWord_1664384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664384).length < 2 ^ (prefixWord ++ tailWord_1664384).sum := by decide
  have hdescent : baseEnd_1664384 < baseStart_1664384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664412 : List Nat := [2, 2, 3, 4, 1, 2, 1, 3, 5]
def baseStart_1664412 : Nat := 118140960795 + 1664412 * 2 ^ 59
def prefixEnd_1664412 : Nat := 4983230072969 + 3 ^ 40 * 1664412 * 2
def baseEnd_1664412 : Nat := 94960373679027468232835

theorem tailTrace_1664412 : CollatzResearch.WordTrace tailWord_1664412 prefixEnd_1664412 94960373679027468232835 := by
  unfold tailWord_1664412
  simp only [CollatzResearch.WordTrace]
  refine ⟨30353046423063528891849745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40470728564084705189132993 30353046423063528891849745)
  ·
    refine ⟨22764784817297646668887309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30353046423063528891849745 22764784817297646668887309)
    ·
      refine ⟨8536794306486617500832741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22764784817297646668887309 8536794306486617500832741)
      ·
        refine ⟨1600648932466240781406139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8536794306486617500832741 1600648932466240781406139)
        ·
          refine ⟨2400973398699361172109209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1600648932466240781406139 2400973398699361172109209)
          ·
            refine ⟨1800730049024520879081907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2400973398699361172109209 1800730049024520879081907)
            ·
              refine ⟨2701095073536781318622861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800730049024520879081907 2701095073536781318622861)
              ·
                refine ⟨1012910652576292994483573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2701095073536781318622861 1012910652576292994483573)
                ·
                  refine ⟨94960373679027468232835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1012910652576292994483573 94960373679027468232835)
                  ·
                    rfl

theorem cell23_1664412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 5].length) (baseStart_1664412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664412 prefixEnd_1664412 := by exact prefixLift 1664412
  have htrace : WordTrace (prefixWord ++ tailWord_1664412) baseStart_1664412 baseEnd_1664412 := by
    simpa [prefixWord, tailWord_1664412, baseEnd_1664412] using wordTrace_append hprefix tailTrace_1664412
  have hstable : (prefixWord ++ tailWord_1664412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664412).length < 2 ^ (prefixWord ++ tailWord_1664412).sum := by decide
  have hdescent : baseEnd_1664412 < baseStart_1664412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664464 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 2, 9]
def baseStart_1664464 : Nat := 118140960795 + 1664464 * 2 ^ 59
def prefixEnd_1664464 : Nat := 4983230072969 + 3 ^ 40 * 1664464 * 2
def baseEnd_1664464 : Nat := 284890021368427003548425

theorem tailTrace_1664464 : CollatzResearch.WordTrace tailWord_1664464 prefixEnd_1664464 284890021368427003548425 := by
  unfold tailWord_1664464
  simp only [CollatzResearch.WordTrace]
  refine ⟨30353994720969335332296223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40471992961292447109728297 30353994720969335332296223)
  ·
    refine ⟨45530992081454002998444335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30353994720969335332296223 45530992081454002998444335)
    ·
      refine ⟨68296488122181004497666503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45530992081454002998444335 68296488122181004497666503)
      ·
        refine ⟨102444732183271506746499755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68296488122181004497666503 102444732183271506746499755)
        ·
          refine ⟨153667098274907260119749633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102444732183271506746499755 153667098274907260119749633)
          ·
            refine ⟨115250323706180445089812225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153667098274907260119749633 115250323706180445089812225)
            ·
              refine ⟨86437742779635333817359169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115250323706180445089812225 86437742779635333817359169)
              ·
                refine ⟨64828307084726500363019377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86437742779635333817359169 64828307084726500363019377)
                ·
                  refine ⟨48621230313544875272264533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64828307084726500363019377 48621230313544875272264533)
                  ·
                    refine ⟨284890021368427003548425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 48621230313544875272264533 284890021368427003548425)
                    ·
                      rfl

theorem cell23_1664464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 9].length) (baseStart_1664464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664464 prefixEnd_1664464 := by exact prefixLift 1664464
  have htrace : WordTrace (prefixWord ++ tailWord_1664464) baseStart_1664464 baseEnd_1664464 := by
    simpa [prefixWord, tailWord_1664464, baseEnd_1664464] using wordTrace_append hprefix tailTrace_1664464
  have hstable : (prefixWord ++ tailWord_1664464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664464).length < 2 ^ (prefixWord ++ tailWord_1664464).sum := by decide
  have hdescent : baseEnd_1664464 < baseStart_1664464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664498 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 3, 5]
def baseStart_1664498 : Nat := 118140960795 + 1664498 * 2 ^ 59
def prefixEnd_1664498 : Nat := 4983230072969 + 3 ^ 40 * 1664498 * 2
def baseEnd_1664498 : Nat := 284895840815844625873373

theorem tailTrace_1664498 : CollatzResearch.WordTrace tailWord_1664498 prefixEnd_1664498 284895840815844625873373 := by
  unfold tailWord_1664498
  simp only [CollatzResearch.WordTrace]
  refine ⟨15177307380953873617832537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40472819682543662980886765 15177307380953873617832537)
  ·
    refine ⟨11382980535715405213374403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15177307380953873617832537 11382980535715405213374403)
    ·
      refine ⟨17074470803573107820061605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11382980535715405213374403 17074470803573107820061605)
      ·
        refine ⟨3201463275669957716261551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17074470803573107820061605 3201463275669957716261551)
        ·
          refine ⟨4802194913504936574392327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3201463275669957716261551 4802194913504936574392327)
          ·
            refine ⟨7203292370257404861588491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4802194913504936574392327 7203292370257404861588491)
            ·
              refine ⟨10804938555386107292382737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7203292370257404861588491 10804938555386107292382737)
              ·
                refine ⟨8103703916539580469287053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10804938555386107292382737 8103703916539580469287053)
                ·
                  refine ⟨3038888968702342675982645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8103703916539580469287053 3038888968702342675982645)
                  ·
                    refine ⟨284895840815844625873373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3038888968702342675982645 284895840815844625873373)
                    ·
                      rfl

theorem cell23_1664498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_1664498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664498 prefixEnd_1664498 := by exact prefixLift 1664498
  have htrace : WordTrace (prefixWord ++ tailWord_1664498) baseStart_1664498 baseEnd_1664498 := by
    simpa [prefixWord, tailWord_1664498, baseEnd_1664498] using wordTrace_append hprefix tailTrace_1664498
  have hstable : (prefixWord ++ tailWord_1664498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664498).length < 2 ^ (prefixWord ++ tailWord_1664498).sum := by decide
  have hdescent : baseEnd_1664498 < baseStart_1664498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664522 : List Nat := [3, 1, 2, 2, 2, 4, 1, 1, 2, 3, 2]
def baseStart_1664522 : Nat := 118140960795 + 1664522 * 2 ^ 59
def prefixEnd_1664522 : Nat := 4983230072969 + 3 ^ 40 * 1664522 * 2
def baseEnd_1664522 : Nat := 854699845983241783720009

theorem tailTrace_1664522 : CollatzResearch.WordTrace tailWord_1664522 prefixEnd_1664522 854699845983241783720009 := by
  unfold tailWord_1664522
  simp only [CollatzResearch.WordTrace]
  refine ⟨15177526218932136642550955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40473403250485697713469213 15177526218932136642550955)
  ·
    refine ⟨22766289328398204963826433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15177526218932136642550955 22766289328398204963826433)
    ·
      refine ⟨17074716996298653722869825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22766289328398204963826433 17074716996298653722869825)
      ·
        refine ⟨12806037747223990292152369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17074716996298653722869825 12806037747223990292152369)
        ·
          refine ⟨9604528310417992719114277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12806037747223990292152369 9604528310417992719114277)
          ·
            refine ⟨1800849058203373634833927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9604528310417992719114277 1800849058203373634833927)
            ·
              refine ⟨2701273587305060452250891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800849058203373634833927 2701273587305060452250891)
              ·
                refine ⟨4051910380957590678376337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2701273587305060452250891 4051910380957590678376337)
                ·
                  refine ⟨3038932785718193008782253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4051910380957590678376337 3038932785718193008782253)
                  ·
                    refine ⟨1139599794644322378293345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3038932785718193008782253 1139599794644322378293345)
                    ·
                      refine ⟨854699845983241783720009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1139599794644322378293345 854699845983241783720009)
                      ·
                        rfl

theorem cell23_1664522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_1664522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664522 prefixEnd_1664522 := by exact prefixLift 1664522
  have htrace : WordTrace (prefixWord ++ tailWord_1664522) baseStart_1664522 baseEnd_1664522 := by
    simpa [prefixWord, tailWord_1664522, baseEnd_1664522] using wordTrace_append hprefix tailTrace_1664522
  have hstable : (prefixWord ++ tailWord_1664522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664522).length < 2 ^ (prefixWord ++ tailWord_1664522).sum := by decide
  have hdescent : baseEnd_1664522 < baseStart_1664522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664532 : List Nat := [2, 4, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_1664532 : Nat := 118140960795 + 1664532 * 2 ^ 59
def prefixEnd_1664532 : Nat := 4983230072969 + 3 ^ 40 * 1664532 * 2
def baseEnd_1664532 : Nat := 284901660263262248198321

theorem tailTrace_1664532 : CollatzResearch.WordTrace tailWord_1664532 prefixEnd_1664532 284901660263262248198321 := by
  unfold tailWord_1664532
  simp only [CollatzResearch.WordTrace]
  refine ⟨30355234802846159139033925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40473646403794878852045233 30355234802846159139033925)
  ·
    refine ⟨5691606525533654838568861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30355234802846159139033925 5691606525533654838568861)
    ·
      refine ⟨2134352447075120564463323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5691606525533654838568861 2134352447075120564463323)
      ·
        refine ⟨3201528670612680846694985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2134352447075120564463323 3201528670612680846694985)
        ·
          refine ⟨2401146502959510635021239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3201528670612680846694985 2401146502959510635021239)
          ·
            refine ⟨3601719754439265952531859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401146502959510635021239 3601719754439265952531859)
            ·
              refine ⟨5402579631658898928797789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3601719754439265952531859 5402579631658898928797789)
              ·
                refine ⟨2025967361872087098299171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5402579631658898928797789 2025967361872087098299171)
                ·
                  refine ⟨3038951042808130647448757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2025967361872087098299171 3038951042808130647448757)
                  ·
                    refine ⟨284901660263262248198321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3038951042808130647448757 284901660263262248198321)
                    ·
                      rfl

theorem cell23_1664532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_1664532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664532 prefixEnd_1664532 := by exact prefixLift 1664532
  have htrace : WordTrace (prefixWord ++ tailWord_1664532) baseStart_1664532 baseEnd_1664532 := by
    simpa [prefixWord, tailWord_1664532, baseEnd_1664532] using wordTrace_append hprefix tailTrace_1664532
  have hstable : (prefixWord ++ tailWord_1664532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664532).length < 2 ^ (prefixWord ++ tailWord_1664532).sum := by decide
  have hdescent : baseEnd_1664532 < baseStart_1664532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664541 : List Nat := [1, 4, 2, 2, 1, 1, 12]
def baseStart_1664541 : Nat := 118140960795 + 1664541 * 2 ^ 59
def prefixEnd_1664541 : Nat := 4983230072969 + 3 ^ 40 * 1664541 * 2
def baseEnd_1664541 : Nat := 10551970396489842091141

theorem tailTrace_1664541 : CollatzResearch.WordTrace tailWord_1664541 prefixEnd_1664541 10551970396489842091141 := by
  unfold tailWord_1664541
  simp only [CollatzResearch.WordTrace]
  refine ⟨60710797862659712815145477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40473865241773141876763651 60710797862659712815145477)
  ·
    refine ⟨11383274599248696152839777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60710797862659712815145477 11383274599248696152839777)
    ·
      refine ⟨8537455949436522114629833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11383274599248696152839777 8537455949436522114629833)
      ·
        refine ⟨6403091962077391585972375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8537455949436522114629833 6403091962077391585972375)
        ·
          refine ⟨9604637943116087378958563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6403091962077391585972375 9604637943116087378958563)
          ·
            refine ⟨14406956914674131068437845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9604637943116087378958563 14406956914674131068437845)
            ·
              refine ⟨10551970396489842091141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 14406956914674131068437845 10551970396489842091141)
              ·
                rfl

theorem cell23_1664541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 12].length) (baseStart_1664541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664541 prefixEnd_1664541 := by exact prefixLift 1664541
  have htrace : WordTrace (prefixWord ++ tailWord_1664541) baseStart_1664541 baseEnd_1664541 := by
    simpa [prefixWord, tailWord_1664541, baseEnd_1664541] using wordTrace_append hprefix tailTrace_1664541
  have hstable : (prefixWord ++ tailWord_1664541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664541).length < 2 ^ (prefixWord ++ tailWord_1664541).sum := by decide
  have hdescent : baseEnd_1664541 < baseStart_1664541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664545 : List Nat := [1, 2, 3, 2, 2, 2, 3, 2, 2, 4]
def baseStart_1664545 : Nat := 118140960795 + 1664545 * 2 ^ 59
def prefixEnd_1664545 : Nat := 4983230072969 + 3 ^ 40 * 1664545 * 2
def baseEnd_1664545 : Nat := 284903885346098397910801

theorem tailTrace_1664545 : CollatzResearch.WordTrace tailWord_1664545 prefixEnd_1664545 284903885346098397910801 := by
  unfold tailWord_1664545
  simp only [CollatzResearch.WordTrace]
  refine ⟨60710943754645221498291089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40473962503096814332194059 60710943754645221498291089)
  ·
    refine ⟨45533207815983916123718317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60710943754645221498291089 45533207815983916123718317)
    ·
      refine ⟨17074952930993968546394369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45533207815983916123718317 17074952930993968546394369)
      ·
        refine ⟨12806214698245476409795777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17074952930993968546394369 12806214698245476409795777)
        ·
          refine ⟨9604661023684107307346833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12806214698245476409795777 9604661023684107307346833)
          ·
            refine ⟨7203495767763080480510125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9604661023684107307346833 7203495767763080480510125)
            ·
              refine ⟨2701310912911155180191297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7203495767763080480510125 2701310912911155180191297)
              ·
                refine ⟨2025983184683366385143473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2701310912911155180191297 2025983184683366385143473)
                ·
                  refine ⟨1519487388512524788857605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2025983184683366385143473 1519487388512524788857605)
                  ·
                    refine ⟨284903885346098397910801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1519487388512524788857605 284903885346098397910801)
                    ·
                      rfl

theorem cell23_1664545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_1664545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664545 prefixEnd_1664545 := by exact prefixLift 1664545
  have htrace : WordTrace (prefixWord ++ tailWord_1664545) baseStart_1664545 baseEnd_1664545 := by
    simpa [prefixWord, tailWord_1664545, baseEnd_1664545] using wordTrace_append hprefix tailTrace_1664545
  have hstable : (prefixWord ++ tailWord_1664545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664545).length < 2 ^ (prefixWord ++ tailWord_1664545).sum := by decide
  have hdescent : baseEnd_1664545 < baseStart_1664545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664565 : List Nat := [1, 3, 3, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_1664565 : Nat := 118140960795 + 1664565 * 2 ^ 59
def prefixEnd_1664565 : Nat := 4983230072969 + 3 ^ 40 * 1664565 * 2
def baseEnd_1664565 : Nat := 854721925651385115482311

theorem tailTrace_1664565 : CollatzResearch.WordTrace tailWord_1664565 prefixEnd_1664565 854721925651385115482311 := by
  unfold tailWord_1664565
  simp only [CollatzResearch.WordTrace]
  refine ⟨60711673214572764914019149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40474448809715176609346099 60711673214572764914019149)
  ·
    refine ⟨22766877455464786842757181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60711673214572764914019149 22766877455464786842757181)
    ·
      refine ⟨8537579045799295066033943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22766877455464786842757181 8537579045799295066033943)
      ·
        refine ⟨12806368568698942599050915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8537579045799295066033943 12806368568698942599050915)
        ·
          refine ⟨19209552853048413898576373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12806368568698942599050915 19209552853048413898576373)
          ·
            refine ⟨1800895579973288802991535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19209552853048413898576373 1800895579973288802991535)
            ·
              refine ⟨2701343369959933204487303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800895579973288802991535 2701343369959933204487303)
              ·
                refine ⟨4052015054939899806730955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2701343369959933204487303 4052015054939899806730955)
                ·
                  refine ⟨6078022582409849710096433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052015054939899806730955 6078022582409849710096433)
                  ·
                    refine ⟨4558516936807387282572325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6078022582409849710096433 4558516936807387282572325)
                    ·
                      refine ⟨854721925651385115482311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4558516936807387282572325 854721925651385115482311)
                      ·
                        rfl

theorem cell23_1664565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_1664565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664565 prefixEnd_1664565 := by exact prefixLift 1664565
  have htrace : WordTrace (prefixWord ++ tailWord_1664565) baseStart_1664565 baseEnd_1664565 := by
    simpa [prefixWord, tailWord_1664565, baseEnd_1664565] using wordTrace_append hprefix tailTrace_1664565
  have hstable : (prefixWord ++ tailWord_1664565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664565).length < 2 ^ (prefixWord ++ tailWord_1664565).sum := by decide
  have hdescent : baseEnd_1664565 < baseStart_1664565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664572 : List Nat := [2, 2, 2, 2, 4, 1, 2, 2, 1, 2, 3]
def baseStart_1664572 : Nat := 118140960795 + 1664572 * 2 ^ 59
def prefixEnd_1664572 : Nat := 4983230072969 + 3 ^ 40 * 1664572 * 2
def baseEnd_1664572 : Nat := 854725520015966588094779

theorem tailTrace_1664572 : CollatzResearch.WordTrace tailWord_1664572 prefixEnd_1664572 854725520015966588094779 := by
  unfold tailWord_1664572
  simp only [CollatzResearch.WordTrace]
  refine ⟨30355964262773702554761985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40474619017031603406349313 30355964262773702554761985)
  ·
    refine ⟨22766973197080276916071489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30355964262773702554761985 22766973197080276916071489)
    ·
      refine ⟨17075229897810207687053617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22766973197080276916071489 17075229897810207687053617)
      ·
        refine ⟨12806422423357655765290213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17075229897810207687053617 12806422423357655765290213)
        ·
          refine ⟨2401204204379560455991915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12806422423357655765290213 2401204204379560455991915)
          ·
            refine ⟨3601806306569340683987873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401204204379560455991915 3601806306569340683987873)
            ·
              refine ⟨2701354729927005512990905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3601806306569340683987873 2701354729927005512990905)
              ·
                refine ⟨2026016047445254134743179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2701354729927005512990905 2026016047445254134743179)
                ·
                  refine ⟨3039024071167881202114769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2026016047445254134743179 3039024071167881202114769)
                  ·
                    refine ⟨2279268053375910901586077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3039024071167881202114769 2279268053375910901586077)
                    ·
                      refine ⟨854725520015966588094779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2279268053375910901586077 854725520015966588094779)
                      ·
                        rfl

theorem cell23_1664572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_1664572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664572 prefixEnd_1664572 := by exact prefixLift 1664572
  have htrace : WordTrace (prefixWord ++ tailWord_1664572) baseStart_1664572 baseEnd_1664572 := by
    simpa [prefixWord, tailWord_1664572, baseEnd_1664572] using wordTrace_append hprefix tailTrace_1664572
  have hstable : (prefixWord ++ tailWord_1664572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664572).length < 2 ^ (prefixWord ++ tailWord_1664572).sum := by decide
  have hdescent : baseEnd_1664572 < baseStart_1664572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664581 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 1, 4, 5]
def baseStart_1664581 : Nat := 118140960795 + 1664581 * 2 ^ 59
def prefixEnd_1664581 : Nat := 4983230072969 + 3 ^ 40 * 1664581 * 2
def baseEnd_1664581 : Nat := 854730141341857052882237

theorem tailTrace_1664581 : CollatzResearch.WordTrace tailWord_1664581 prefixEnd_1664581 854730141341857052882237 := by
  unfold tailWord_1664581
  simp only [CollatzResearch.WordTrace]
  refine ⟨60712256782514799646601597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40474837855009866431067731 60712256782514799646601597)
  ·
    refine ⟨22767096293443049867475599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60712256782514799646601597 22767096293443049867475599)
    ·
      refine ⟨34150644440164574801213399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22767096293443049867475599 34150644440164574801213399)
      ·
        refine ⟨51225966660246862201820099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34150644440164574801213399 51225966660246862201820099)
        ·
          refine ⟨76838949990370293302730149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51225966660246862201820099 76838949990370293302730149)
          ·
            refine ⟨14407303123194429994261903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76838949990370293302730149 14407303123194429994261903)
            ·
              refine ⟨21610954684791644991392855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14407303123194429994261903 21610954684791644991392855)
              ·
                refine ⟨32416432027187467487089283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21610954684791644991392855 32416432027187467487089283)
                ·
                  refine ⟨48624648040781201230633925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32416432027187467487089283 48624648040781201230633925)
                  ·
                    refine ⟨9117121507646475230743861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48624648040781201230633925 9117121507646475230743861)
                    ·
                      refine ⟨854730141341857052882237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9117121507646475230743861 854730141341857052882237)
                      ·
                        rfl

theorem cell23_1664581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_1664581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664581 prefixEnd_1664581 := by exact prefixLift 1664581
  have htrace : WordTrace (prefixWord ++ tailWord_1664581) baseStart_1664581 baseEnd_1664581 := by
    simpa [prefixWord, tailWord_1664581, baseEnd_1664581] using wordTrace_append hprefix tailTrace_1664581
  have hstable : (prefixWord ++ tailWord_1664581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664581).length < 2 ^ (prefixWord ++ tailWord_1664581).sum := by decide
  have hdescent : baseEnd_1664581 < baseStart_1664581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664591 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 4]
def baseStart_1664591 : Nat := 118140960795 + 1664591 * 2 ^ 59
def prefixEnd_1664591 : Nat := 4983230072969 + 3 ^ 40 * 1664591 * 2
def baseEnd_1664591 : Nat := 854735276148402013757191

theorem tailTrace_1664591 : CollatzResearch.WordTrace tailWord_1664591 prefixEnd_1664591 854735276148402013757191 := by
  unfold tailWord_1664591
  simp only [CollatzResearch.WordTrace]
  refine ⟨60712621512478571354465627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40475081008319047569643751 60712621512478571354465627)
  ·
    refine ⟨91068932268717857031698441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60712621512478571354465627 91068932268717857031698441)
    ·
      refine ⟨68301699201538392773773831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91068932268717857031698441 68301699201538392773773831)
      ·
        refine ⟨102452548802307589160660747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68301699201538392773773831 102452548802307589160660747)
        ·
          refine ⟨153678823203461383740991121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102452548802307589160660747 153678823203461383740991121)
          ·
            refine ⟨115259117402596037805743341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153678823203461383740991121 115259117402596037805743341)
            ·
              refine ⟨43222169025973514177153753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115259117402596037805743341 43222169025973514177153753)
              ·
                refine ⟨32416626769480135632865315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43222169025973514177153753 32416626769480135632865315)
                ·
                  refine ⟨48624940154220203449297973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32416626769480135632865315 48624940154220203449297973)
                  ·
                    refine ⟨4558588139458144073371685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48624940154220203449297973 4558588139458144073371685)
                    ·
                      refine ⟨854735276148402013757191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4558588139458144073371685 854735276148402013757191)
                      ·
                        rfl

theorem cell23_1664591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_1664591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664591 prefixEnd_1664591 := by exact prefixLift 1664591
  have htrace : WordTrace (prefixWord ++ tailWord_1664591) baseStart_1664591 baseEnd_1664591 := by
    simpa [prefixWord, tailWord_1664591, baseEnd_1664591] using wordTrace_append hprefix tailTrace_1664591
  have hstable : (prefixWord ++ tailWord_1664591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664591).length < 2 ^ (prefixWord ++ tailWord_1664591).sum := by decide
  have hdescent : baseEnd_1664591 < baseStart_1664591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664601 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 4, 6]
def baseStart_1664601 : Nat := 118140960795 + 1664601 * 2 ^ 59
def prefixEnd_1664601 : Nat := 4983230072969 + 3 ^ 40 * 1664601 * 2
def baseEnd_1664601 : Nat := 284913470318315658210715

theorem tailTrace_1664601 : CollatzResearch.WordTrace tailWord_1664601 prefixEnd_1664601 284913470318315658210715 := by
  unfold tailWord_1664601
  simp only [CollatzResearch.WordTrace]
  refine ⟨60712986242442343062329657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40475324161628228708219771 60712986242442343062329657)
  ·
    refine ⟨45534739681831757296747243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60712986242442343062329657 45534739681831757296747243)
    ·
      refine ⟨68302109522747635945120865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45534739681831757296747243 68302109522747635945120865)
      ·
        refine ⟨51226582142060726958840649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68302109522747635945120865 51226582142060726958840649)
        ·
          refine ⟨38419936606545545219130487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51226582142060726958840649 38419936606545545219130487)
          ·
            refine ⟨57629904909818317828695731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38419936606545545219130487 57629904909818317828695731)
            ·
              refine ⟨86444857364727476743043597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57629904909818317828695731 86444857364727476743043597)
              ·
                refine ⟨32416821511772803778641349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86444857364727476743043597 32416821511772803778641349)
                ·
                  refine ⟨6078154033457400708495253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32416821511772803778641349 6078154033457400708495253)
                  ·
                    refine ⟨284913470318315658210715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6078154033457400708495253 284913470318315658210715)
                    ·
                      rfl

theorem cell23_1664601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 6].length) (baseStart_1664601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664601 prefixEnd_1664601 := by exact prefixLift 1664601
  have htrace : WordTrace (prefixWord ++ tailWord_1664601) baseStart_1664601 baseEnd_1664601 := by
    simpa [prefixWord, tailWord_1664601, baseEnd_1664601] using wordTrace_append hprefix tailTrace_1664601
  have hstable : (prefixWord ++ tailWord_1664601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664601).length < 2 ^ (prefixWord ++ tailWord_1664601).sum := by decide
  have hdescent : baseEnd_1664601 < baseStart_1664601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664629 : List Nat := [1, 3, 4, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_1664629 : Nat := 118140960795 + 1664629 * 2 ^ 59
def prefixEnd_1664629 : Nat := 4983230072969 + 3 ^ 40 * 1664629 * 2
def baseEnd_1664629 : Nat := 854754788413272865082017

theorem tailTrace_1664629 : CollatzResearch.WordTrace tailWord_1664629 prefixEnd_1664629 854754788413272865082017 := by
  unfold tailWord_1664629
  simp only [CollatzResearch.WordTrace]
  refine ⟨60714007486340903844348941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40476004990893935896232627 60714007486340903844348941)
  ·
    refine ⟨22767752807377838941630853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60714007486340903844348941 22767752807377838941630853)
    ·
      refine ⟨4268953651383344801555785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22767752807377838941630853 4268953651383344801555785)
      ·
        refine ⟨3201715238537508601166839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4268953651383344801555785 3201715238537508601166839)
        ·
          refine ⟨4802572857806262901750259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3201715238537508601166839 4802572857806262901750259)
          ·
            refine ⟨7203859286709394352625389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4802572857806262901750259 7203859286709394352625389)
            ·
              refine ⟨2701447232516022882234521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7203859286709394352625389 2701447232516022882234521)
              ·
                refine ⟨2026085424387017161675891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2701447232516022882234521 2026085424387017161675891)
                ·
                  refine ⟨3039128136580525742513837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2026085424387017161675891 3039128136580525742513837)
                  ·
                    refine ⟨1139673051217697153442689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3039128136580525742513837 1139673051217697153442689)
                    ·
                      refine ⟨854754788413272865082017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1139673051217697153442689 854754788413272865082017)
                      ·
                        rfl

theorem cell23_1664629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_1664629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664629 prefixEnd_1664629 := by exact prefixLift 1664629
  have htrace : WordTrace (prefixWord ++ tailWord_1664629) baseStart_1664629 baseEnd_1664629 := by
    simpa [prefixWord, tailWord_1664629, baseEnd_1664629] using wordTrace_append hprefix tailTrace_1664629
  have hstable : (prefixWord ++ tailWord_1664629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664629).length < 2 ^ (prefixWord ++ tailWord_1664629).sum := by decide
  have hdescent : baseEnd_1664629 < baseStart_1664629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664631 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 9]
def baseStart_1664631 : Nat := 118140960795 + 1664631 * 2 ^ 59
def prefixEnd_1664631 : Nat := 4983230072969 + 3 ^ 40 * 1664631 * 2
def baseEnd_1664631 : Nat := 94972868374953539695223

theorem tailTrace_1664631 : CollatzResearch.WordTrace tailWord_1664631 prefixEnd_1664631 94972868374953539695223 := by
  unfold tailWord_1664631
  simp only [CollatzResearch.WordTrace]
  refine ⟨60714080432333658185921747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40476053621555772123947831 60714080432333658185921747)
  ·
    refine ⟨91071120648500487278882621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60714080432333658185921747 91071120648500487278882621)
    ·
      refine ⟨34151670243187682729580983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91071120648500487278882621 34151670243187682729580983)
      ·
        refine ⟨51227505364781524094371475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34151670243187682729580983 51227505364781524094371475)
        ·
          refine ⟨76841258047172286141557213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51227505364781524094371475 76841258047172286141557213)
          ·
            refine ⟨28815471767689607303083955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76841258047172286141557213 28815471767689607303083955)
            ·
              refine ⟨43223207651534410954625933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28815471767689607303083955 43223207651534410954625933)
              ·
                refine ⟨16208702869325404107984725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43223207651534410954625933 16208702869325404107984725)
                ·
                  refine ⟨94972868374953539695223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16208702869325404107984725 94972868374953539695223)
                  ·
                    rfl

theorem cell23_1664631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 9].length) (baseStart_1664631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664631 prefixEnd_1664631 := by exact prefixLift 1664631
  have htrace : WordTrace (prefixWord ++ tailWord_1664631) baseStart_1664631 baseEnd_1664631 := by
    simpa [prefixWord, tailWord_1664631, baseEnd_1664631] using wordTrace_append hprefix tailTrace_1664631
  have hstable : (prefixWord ++ tailWord_1664631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664631).length < 2 ^ (prefixWord ++ tailWord_1664631).sum := by decide
  have hdescent : baseEnd_1664631 < baseStart_1664631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664695 : List Nat := [1, 1, 3, 1, 5, 1, 3, 1, 2, 5]
def baseStart_1664695 : Nat := 118140960795 + 1664695 * 2 ^ 59
def prefixEnd_1664695 : Nat := 4983230072969 + 3 ^ 40 * 1664695 * 2
def baseEnd_1664695 : Nat := 284929559378823202285571

theorem tailTrace_1664695 : CollatzResearch.WordTrace tailWord_1664695 prefixEnd_1664695 284929559378823202285571 := by
  unfold tailWord_1664695
  simp only [CollatzResearch.WordTrace]
  refine ⟨60716414704101797116251539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40477609802734531410834359 60716414704101797116251539)
  ·
    refine ⟨91074622056152695674377309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60716414704101797116251539 91074622056152695674377309)
    ·
      refine ⟨34152983271057260877891491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91074622056152695674377309 34152983271057260877891491)
      ·
        refine ⟨51229474906585891316837237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34152983271057260877891491 51229474906585891316837237)
        ·
          refine ⟨4802763272492427310953491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51229474906585891316837237 4802763272492427310953491)
          ·
            refine ⟨7204144908738640966430237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4802763272492427310953491 7204144908738640966430237)
            ·
              refine ⟨2701554340776990362411339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7204144908738640966430237 2701554340776990362411339)
              ·
                refine ⟨4052331511165485543617009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2701554340776990362411339 4052331511165485543617009)
                ·
                  refine ⟨3039248633374114157712757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4052331511165485543617009 3039248633374114157712757)
                  ·
                    refine ⟨284929559378823202285571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3039248633374114157712757 284929559378823202285571)
                    ·
                      rfl

theorem cell23_1664695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_1664695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664695 prefixEnd_1664695 := by exact prefixLift 1664695
  have htrace : WordTrace (prefixWord ++ tailWord_1664695) baseStart_1664695 baseEnd_1664695 := by
    simpa [prefixWord, tailWord_1664695, baseEnd_1664695] using wordTrace_append hprefix tailTrace_1664695
  have hstable : (prefixWord ++ tailWord_1664695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664695).length < 2 ^ (prefixWord ++ tailWord_1664695).sum := by decide
  have hdescent : baseEnd_1664695 < baseStart_1664695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664710 : List Nat := [6, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_1664710 : Nat := 118140960795 + 1664710 * 2 ^ 59
def prefixEnd_1664710 : Nat := 4983230072969 + 3 ^ 40 * 1664710 * 2
def baseEnd_1664710 : Nat := 854796380346287048169145

theorem tailTrace_1664710 : CollatzResearch.WordTrace tailWord_1664710 prefixEnd_1664710 854796380346287048169145 := by
  unfold tailWord_1664710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1897405056220232958688987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40477974532698303118698389 1897405056220232958688987)
  ·
    refine ⟨2846107584330349438033481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1897405056220232958688987 2846107584330349438033481)
    ·
      refine ⟨2134580688247762078525111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2846107584330349438033481 2134580688247762078525111)
      ·
        refine ⟨3201871032371643117787667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2134580688247762078525111 3201871032371643117787667)
        ·
          refine ⟨4802806548557464676681501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3201871032371643117787667 4802806548557464676681501)
          ·
            refine ⟨1801052455709049253755563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4802806548557464676681501 1801052455709049253755563)
            ·
              refine ⟨2701578683563573880633345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1801052455709049253755563 2701578683563573880633345)
              ·
                refine ⟨2026184012672680410475009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2701578683563573880633345 2026184012672680410475009)
                ·
                  refine ⟨1519638009504510307856257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2026184012672680410475009 1519638009504510307856257)
                  ·
                    refine ⟨1139728507128382730892193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1519638009504510307856257 1139728507128382730892193)
                    ·
                      refine ⟨854796380346287048169145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1139728507128382730892193 854796380346287048169145)
                      ·
                        rfl

theorem cell23_1664710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_1664710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664710 prefixEnd_1664710 := by exact prefixLift 1664710
  have htrace : WordTrace (prefixWord ++ tailWord_1664710) baseStart_1664710 baseEnd_1664710 := by
    simpa [prefixWord, tailWord_1664710, baseEnd_1664710] using wordTrace_append hprefix tailTrace_1664710
  have hstable : (prefixWord ++ tailWord_1664710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664710).length < 2 ^ (prefixWord ++ tailWord_1664710).sum := by decide
  have hdescent : baseEnd_1664710 < baseStart_1664710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664728 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 2, 1, 6]
def baseStart_1664728 : Nat := 118140960795 + 1664728 * 2 ^ 59
def prefixEnd_1664728 : Nat := 4983230072969 + 3 ^ 40 * 1664728 * 2
def baseEnd_1664728 : Nat := 854805622998067977744061

theorem tailTrace_1664728 : CollatzResearch.WordTrace tailWord_1664728 prefixEnd_1664728 854805622998067977744061 := by
  unfold tailWord_1664728
  simp only [CollatzResearch.WordTrace]
  refine ⟨30358809156491121876101419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40478412208654829168135225 30358809156491121876101419)
  ·
    refine ⟨45538213734736682814152129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30358809156491121876101419 45538213734736682814152129)
    ·
      refine ⟨34153660301052512110614097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45538213734736682814152129 34153660301052512110614097)
      ·
        refine ⟨25615245225789384082960573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34153660301052512110614097 25615245225789384082960573)
        ·
          refine ⟨9605716959671019031110215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25615245225789384082960573 9605716959671019031110215)
          ·
            refine ⟨14408575439506528546665323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9605716959671019031110215 14408575439506528546665323)
            ·
              refine ⟨21612863159259792819997985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14408575439506528546665323 21612863159259792819997985)
              ·
                refine ⟨16209647369444844614998489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21612863159259792819997985 16209647369444844614998489)
                ·
                  refine ⟨12157235527083633461248867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16209647369444844614998489 12157235527083633461248867)
                  ·
                    refine ⟨18235853290625450191873301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12157235527083633461248867 18235853290625450191873301)
                    ·
                      refine ⟨854805622998067977744061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18235853290625450191873301 854805622998067977744061)
                      ·
                        rfl

theorem cell23_1664728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_1664728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664728 prefixEnd_1664728 := by exact prefixLift 1664728
  have htrace : WordTrace (prefixWord ++ tailWord_1664728) baseStart_1664728 baseEnd_1664728 := by
    simpa [prefixWord, tailWord_1664728, baseEnd_1664728] using wordTrace_append hprefix tailTrace_1664728
  have hstable : (prefixWord ++ tailWord_1664728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664728).length < 2 ^ (prefixWord ++ tailWord_1664728).sum := by decide
  have hdescent : baseEnd_1664728 < baseStart_1664728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664819 : List Nat := [1, 1, 1, 2, 7, 1, 3, 1, 1, 5]
def baseStart_1664819 : Nat := 118140960795 + 1664819 * 2 ^ 59
def prefixEnd_1664819 : Nat := 4983230072969 + 3 ^ 40 * 1664819 * 2
def baseEnd_1664819 : Nat := 284950783245875707235381

theorem tailTrace_1664819 : CollatzResearch.WordTrace tailWord_1664819 prefixEnd_1664819 284950783245875707235381 := by
  unfold tailWord_1664819
  simp only [CollatzResearch.WordTrace]
  refine ⟨60720937355652566293765511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40480624903768377529177007 60720937355652566293765511)
  ·
    refine ⟨91081406033478849440648267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60720937355652566293765511 91081406033478849440648267)
    ·
      refine ⟨136622109050218274160972401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91081406033478849440648267 136622109050218274160972401)
      ·
        refine ⟨102466581787663705620729301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136622109050218274160972401 102466581787663705620729301)
        ·
          refine ⟨2401560510648368100485843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 102466581787663705620729301 2401560510648368100485843)
          ·
            refine ⟨3602340765972552150728765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401560510648368100485843 3602340765972552150728765)
            ·
              refine ⟨1350877787239707056523287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3602340765972552150728765 1350877787239707056523287)
              ·
                refine ⟨2026316680859560584784931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350877787239707056523287 2026316680859560584784931)
                ·
                  refine ⟨3039475021289340877177397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2026316680859560584784931 3039475021289340877177397)
                  ·
                    refine ⟨284950783245875707235381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3039475021289340877177397 284950783245875707235381)
                    ·
                      rfl

theorem cell23_1664819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 1, 5].length) (baseStart_1664819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664819 prefixEnd_1664819 := by exact prefixLift 1664819
  have htrace : WordTrace (prefixWord ++ tailWord_1664819) baseStart_1664819 baseEnd_1664819 := by
    simpa [prefixWord, tailWord_1664819, baseEnd_1664819] using wordTrace_append hprefix tailTrace_1664819
  have hstable : (prefixWord ++ tailWord_1664819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664819).length < 2 ^ (prefixWord ++ tailWord_1664819).sum := by decide
  have hdescent : baseEnd_1664819 < baseStart_1664819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664852 : List Nat := [2, 4, 1, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_1664852 : Nat := 118140960795 + 1664852 * 2 ^ 59
def prefixEnd_1664852 : Nat := 4983230072969 + 3 ^ 40 * 1664852 * 2
def baseEnd_1664852 : Nat := 854869294599225492593491

theorem tailTrace_1664852 : CollatzResearch.WordTrace tailWord_1664852 prefixEnd_1664852 854869294599225492593491 := by
  unfold tailWord_1664852
  simp only [CollatzResearch.WordTrace]
  refine ⟨30361070482266506464858405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40481427309688675286477873 30361070482266506464858405)
  ·
    refine ⟨5692700715424969962160951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30361070482266506464858405 5692700715424969962160951)
    ·
      refine ⟨8539051073137454943241427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5692700715424969962160951 8539051073137454943241427)
      ·
        refine ⟨12808576609706182414862141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8539051073137454943241427 12808576609706182414862141)
        ·
          refine ⟨4803216228639818405573303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12808576609706182414862141 4803216228639818405573303)
          ·
            refine ⟨7204824342959727608359955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4803216228639818405573303 7204824342959727608359955)
            ·
              refine ⟨10807236514439591412539933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7204824342959727608359955 10807236514439591412539933)
              ·
                refine ⟨4052713692914846779702475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10807236514439591412539933 4052713692914846779702475)
                ·
                  refine ⟨6079070539372270169553713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052713692914846779702475 6079070539372270169553713)
                  ·
                    refine ⟨4559302904529202627165285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6079070539372270169553713 4559302904529202627165285)
                    ·
                      refine ⟨854869294599225492593491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4559302904529202627165285 854869294599225492593491)
                      ·
                        rfl

theorem cell23_1664852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_1664852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664852 prefixEnd_1664852 := by exact prefixLift 1664852
  have htrace : WordTrace (prefixWord ++ tailWord_1664852) baseStart_1664852 baseEnd_1664852 := by
    simpa [prefixWord, tailWord_1664852, baseEnd_1664852] using wordTrace_append hprefix tailTrace_1664852
  have hstable : (prefixWord ++ tailWord_1664852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664852).length < 2 ^ (prefixWord ++ tailWord_1664852).sum := by decide
  have hdescent : baseEnd_1664852 < baseStart_1664852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664872 : List Nat := [2, 1, 4, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_1664872 : Nat := 118140960795 + 1664872 * 2 ^ 59
def prefixEnd_1664872 : Nat := 4983230072969 + 3 ^ 40 * 1664872 * 2
def baseEnd_1664872 : Nat := 854879564212315414343399

theorem tailTrace_1664872 : CollatzResearch.WordTrace tailWord_1664872 prefixEnd_1664872 854879564212315414343399 := by
  unfold tailWord_1664872
  simp only [CollatzResearch.WordTrace]
  refine ⟨30361435212230278172722435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40481913616307037563629913 30361435212230278172722435)
  ·
    refine ⟨45542152818345417259083653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30361435212230278172722435 45542152818345417259083653)
    ·
      refine ⟨8539153653439765736078185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45542152818345417259083653 8539153653439765736078185)
      ·
        refine ⟨6404365240079824302058639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8539153653439765736078185 6404365240079824302058639)
        ·
          refine ⟨9606547860119736453087959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6404365240079824302058639 9606547860119736453087959)
          ·
            refine ⟨14409821790179604679631939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9606547860119736453087959 14409821790179604679631939)
            ·
              refine ⟨21614732685269407019447909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14409821790179604679631939 21614732685269407019447909)
              ·
                refine ⟨4052762378488013816146483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21614732685269407019447909 4052762378488013816146483)
                ·
                  refine ⟨6079143567732020724219725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052762378488013816146483 6079143567732020724219725)
                  ·
                    refine ⟨2279678837899507771582397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6079143567732020724219725 2279678837899507771582397)
                    ·
                      refine ⟨854879564212315414343399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2279678837899507771582397 854879564212315414343399)
                      ·
                        rfl

theorem cell23_1664872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_1664872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664872 prefixEnd_1664872 := by exact prefixLift 1664872
  have htrace : WordTrace (prefixWord ++ tailWord_1664872) baseStart_1664872 baseEnd_1664872 := by
    simpa [prefixWord, tailWord_1664872, baseEnd_1664872] using wordTrace_append hprefix tailTrace_1664872
  have hstable : (prefixWord ++ tailWord_1664872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664872).length < 2 ^ (prefixWord ++ tailWord_1664872).sum := by decide
  have hdescent : baseEnd_1664872 < baseStart_1664872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664876 : List Nat := [2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 3]
def baseStart_1664876 : Nat := 118140960795 + 1664876 * 2 ^ 59
def prefixEnd_1664876 : Nat := 4983230072969 + 3 ^ 40 * 1664876 * 2
def baseEnd_1664876 : Nat := 854881618134933398693381

theorem tailTrace_1664876 : CollatzResearch.WordTrace tailWord_1664876 prefixEnd_1664876 854881618134933398693381 := by
  unfold tailWord_1664876
  simp only [CollatzResearch.WordTrace]
  refine ⟨30361508158223032514295241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40482010877630710019060321 30361508158223032514295241)
  ·
    refine ⟨22771131118667274385721431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30361508158223032514295241 22771131118667274385721431)
    ·
      refine ⟨34156696678000911578582147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22771131118667274385721431 34156696678000911578582147)
      ·
        refine ⟨51235045017001367367873221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34156696678000911578582147 51235045017001367367873221)
        ·
          refine ⟨9606570940687756381476229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51235045017001367367873221 9606570940687756381476229)
          ·
            refine ⟨1801232051378954321526793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9606570940687756381476229 1801232051378954321526793)
            ·
              refine ⟨1350924038534215741145095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1801232051378954321526793 1350924038534215741145095)
              ·
                refine ⟨2026386057801323611717643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350924038534215741145095 2026386057801323611717643)
                ·
                  refine ⟨3039579086701985417576465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2026386057801323611717643 3039579086701985417576465)
                  ·
                    refine ⟨2279684315026489063182349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3039579086701985417576465 2279684315026489063182349)
                    ·
                      refine ⟨854881618134933398693381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2279684315026489063182349 854881618134933398693381)
                      ·
                        rfl

theorem cell23_1664876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 3].length) (baseStart_1664876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664876 prefixEnd_1664876 := by exact prefixLift 1664876
  have htrace : WordTrace (prefixWord ++ tailWord_1664876) baseStart_1664876 baseEnd_1664876 := by
    simpa [prefixWord, tailWord_1664876, baseEnd_1664876] using wordTrace_append hprefix tailTrace_1664876
  have hstable : (prefixWord ++ tailWord_1664876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664876).length < 2 ^ (prefixWord ++ tailWord_1664876).sum := by decide
  have hdescent : baseEnd_1664876 < baseStart_1664876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664905 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 2, 6]
def baseStart_1664905 : Nat := 118140960795 + 1664905 * 2 ^ 59
def prefixEnd_1664905 : Nat := 4983230072969 + 3 ^ 40 * 1664905 * 2
def baseEnd_1664905 : Nat := 284965503024637928410249

theorem tailTrace_1664905 : CollatzResearch.WordTrace tailWord_1664905 prefixEnd_1664905 284965503024637928410249 := by
  unfold tailWord_1664905
  simp only [CollatzResearch.WordTrace]
  refine ⟨60724074033341002981396169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40482716022227335320930779 60724074033341002981396169)
  ·
    refine ⟨45543055525005752236047127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60724074033341002981396169 45543055525005752236047127)
    ·
      refine ⟨68314583287508628354070691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45543055525005752236047127 68314583287508628354070691)
      ·
        refine ⟨102471874931262942531106037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68314583287508628354070691 102471874931262942531106037)
        ·
          refine ⟨9606738274805900862291191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102471874931262942531106037 9606738274805900862291191)
          ·
            refine ⟨14410107412208851293436787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9606738274805900862291191 14410107412208851293436787)
            ·
              refine ⟨21615161118313276940155181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14410107412208851293436787 21615161118313276940155181)
              ·
                refine ⟨8105685419367478852558193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21615161118313276940155181 8105685419367478852558193)
                ·
                  refine ⟨6079264064525609139418645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8105685419367478852558193 6079264064525609139418645)
                  ·
                    refine ⟨284965503024637928410249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6079264064525609139418645 284965503024637928410249)
                    ·
                      rfl

theorem cell23_1664905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 6].length) (baseStart_1664905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664905 prefixEnd_1664905 := by exact prefixLift 1664905
  have htrace : WordTrace (prefixWord ++ tailWord_1664905) baseStart_1664905 baseEnd_1664905 := by
    simpa [prefixWord, tailWord_1664905, baseEnd_1664905] using wordTrace_append hprefix tailTrace_1664905
  have hstable : (prefixWord ++ tailWord_1664905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664905).length < 2 ^ (prefixWord ++ tailWord_1664905).sum := by decide
  have hdescent : baseEnd_1664905 < baseStart_1664905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664906 : List Nat := [3, 1, 2, 4, 2, 2, 1, 1, 1, 3, 3]
def baseStart_1664906 : Nat := 118140960795 + 1664906 * 2 ^ 59
def prefixEnd_1664906 : Nat := 4983230072969 + 3 ^ 40 * 1664906 * 2
def baseEnd_1664906 : Nat := 854897022554568281318243

theorem tailTrace_1664906 : CollatzResearch.WordTrace tailWord_1664906 prefixEnd_1664906 854897022554568281318243 := by
  unfold tailWord_1664906
  simp only [CollatzResearch.WordTrace]
  refine ⟨15181027626584345038045643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40482740337558253434788381 15181027626584345038045643)
  ·
    refine ⟨22771541439876517557068465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15181027626584345038045643 22771541439876517557068465)
    ·
      refine ⟨17078656079907388167801349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22771541439876517557068465 17078656079907388167801349)
      ·
        refine ⟨3202248014982635281462753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17078656079907388167801349 3202248014982635281462753)
        ·
          refine ⟨2401686011236976461097065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3202248014982635281462753 2401686011236976461097065)
          ·
            refine ⟨1801264508427732345822799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2401686011236976461097065 1801264508427732345822799)
            ·
              refine ⟨2701896762641598518734199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1801264508427732345822799 2701896762641598518734199)
              ·
                refine ⟨4052845143962397778101299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2701896762641598518734199 4052845143962397778101299)
                ·
                  refine ⟨6079267715943596667151949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052845143962397778101299 6079267715943596667151949)
                  ·
                    refine ⟨2279725393478848750181981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6079267715943596667151949 2279725393478848750181981)
                    ·
                      refine ⟨854897022554568281318243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2279725393478848750181981 854897022554568281318243)
                      ·
                        rfl

theorem cell23_1664906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_1664906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664906 prefixEnd_1664906 := by exact prefixLift 1664906
  have htrace : WordTrace (prefixWord ++ tailWord_1664906) baseStart_1664906 baseEnd_1664906 := by
    simpa [prefixWord, tailWord_1664906, baseEnd_1664906] using wordTrace_append hprefix tailTrace_1664906
  have hstable : (prefixWord ++ tailWord_1664906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664906).length < 2 ^ (prefixWord ++ tailWord_1664906).sum := by decide
  have hdescent : baseEnd_1664906 < baseStart_1664906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664915 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 3]
def baseStart_1664915 : Nat := 118140960795 + 1664915 * 2 ^ 59
def prefixEnd_1664915 : Nat := 4983230072969 + 3 ^ 40 * 1664915 * 2
def baseEnd_1664915 : Nat := 854901643880458746105701

theorem tailTrace_1664915 : CollatzResearch.WordTrace tailWord_1664915 prefixEnd_1664915 854901643880458746105701 := by
  unfold tailWord_1664915
  simp only [CollatzResearch.WordTrace]
  refine ⟨60724438763304774689260199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40482959175536516459506799 60724438763304774689260199)
  ·
    refine ⟨91086658144957162033890299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60724438763304774689260199 91086658144957162033890299)
    ·
      refine ⟨136629987217435743050835449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91086658144957162033890299 136629987217435743050835449)
      ·
        refine ⟨102472490413076807288126587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136629987217435743050835449 102472490413076807288126587)
        ·
          refine ⟨153708735619615210932189881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102472490413076807288126587 153708735619615210932189881)
          ·
            refine ⟨115281551714711408199142411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153708735619615210932189881 115281551714711408199142411)
            ·
              refine ⟨172922327572067112298713617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115281551714711408199142411 172922327572067112298713617)
              ·
                refine ⟨129691745679050334224035213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172922327572067112298713617 129691745679050334224035213)
                ·
                  refine ⟨48634404629643875334013205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129691745679050334224035213 48634404629643875334013205)
                  ·
                    refine ⟨2279737717014556656281869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48634404629643875334013205 2279737717014556656281869)
                    ·
                      refine ⟨854901643880458746105701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2279737717014556656281869 854901643880458746105701)
                      ·
                        rfl

theorem cell23_1664915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 3].length) (baseStart_1664915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664915 prefixEnd_1664915 := by exact prefixLift 1664915
  have htrace : WordTrace (prefixWord ++ tailWord_1664915) baseStart_1664915 baseEnd_1664915 := by
    simpa [prefixWord, tailWord_1664915, baseEnd_1664915] using wordTrace_append hprefix tailTrace_1664915
  have hstable : (prefixWord ++ tailWord_1664915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664915).length < 2 ^ (prefixWord ++ tailWord_1664915).sum := by decide
  have hdescent : baseEnd_1664915 < baseStart_1664915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664916 : List Nat := [2, 4, 2, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_1664916 : Nat := 118140960795 + 1664916 * 2 ^ 59
def prefixEnd_1664916 : Nat := 4983230072969 + 3 ^ 40 * 1664916 * 2
def baseEnd_1664916 : Nat := 854902157361113242193197

theorem tailTrace_1664916 : CollatzResearch.WordTrace tailWord_1664916 prefixEnd_1664916 854902157361113242193197 := by
  unfold tailWord_1664916
  simp only [CollatzResearch.WordTrace]
  refine ⟨30362237618150575930023301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40482983490867434573364401 30362237618150575930023301)
  ·
    refine ⟨5692919553403232986879369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30362237618150575930023301 5692919553403232986879369)
    ·
      refine ⟨4269689665052424740159527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5692919553403232986879369 4269689665052424740159527)
      ·
        refine ⟨6404534497578637110239291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4269689665052424740159527 6404534497578637110239291)
        ·
          refine ⟨9606801746367955665358937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6404534497578637110239291 9606801746367955665358937)
          ·
            refine ⟨7205101309775966749019203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9606801746367955665358937 7205101309775966749019203)
            ·
              refine ⟨10807651964663950123528805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7205101309775966749019203 10807651964663950123528805)
              ·
                refine ⟨2026434743374490648161651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10807651964663950123528805 2026434743374490648161651)
                ·
                  refine ⟨3039652115061735972242477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2026434743374490648161651 3039652115061735972242477)
                  ·
                    refine ⟨1139869543148150989590929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3039652115061735972242477 1139869543148150989590929)
                    ·
                      refine ⟨854902157361113242193197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1139869543148150989590929 854902157361113242193197)
                      ·
                        rfl

theorem cell23_1664916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_1664916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664916 prefixEnd_1664916 := by exact prefixLift 1664916
  have htrace : WordTrace (prefixWord ++ tailWord_1664916) baseStart_1664916 baseEnd_1664916 := by
    simpa [prefixWord, tailWord_1664916, baseEnd_1664916] using wordTrace_append hprefix tailTrace_1664916
  have hstable : (prefixWord ++ tailWord_1664916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664916).length < 2 ^ (prefixWord ++ tailWord_1664916).sum := by decide
  have hdescent : baseEnd_1664916 < baseStart_1664916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664932 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_1664932 : Nat := 118140960795 + 1664932 * 2 ^ 59
def prefixEnd_1664932 : Nat := 4983230072969 + 3 ^ 40 * 1664932 * 2
def baseEnd_1664932 : Nat := 854910373051585179593123

theorem tailTrace_1664932 : CollatzResearch.WordTrace tailWord_1664932 prefixEnd_1664932 854910373051585179593123 := by
  unfold tailWord_1664932
  simp only [CollatzResearch.WordTrace]
  refine ⟨30362529402121593296314525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40483372536162124395086033 30362529402121593296314525)
  ·
    refine ⟨11385948525795597486117947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30362529402121593296314525 11385948525795597486117947)
    ·
      refine ⟨17078922788693396229176921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11385948525795597486117947 17078922788693396229176921)
      ·
        refine ⟨12809192091520047171882691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17078922788693396229176921 12809192091520047171882691)
        ·
          refine ⟨19213788137280070757824037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12809192091520047171882691 19213788137280070757824037)
          ·
            refine ⟨3602585275740013267092007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19213788137280070757824037 3602585275740013267092007)
            ·
              refine ⟨5403877913610019900638011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3602585275740013267092007 5403877913610019900638011)
              ·
                refine ⟨8105816870415029850957017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5403877913610019900638011 8105816870415029850957017)
                ·
                  refine ⟨6079362652811272388217763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8105816870415029850957017 6079362652811272388217763)
                  ·
                    refine ⟨9119043979216908582326645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6079362652811272388217763 9119043979216908582326645)
                    ·
                      refine ⟨854910373051585179593123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9119043979216908582326645 854910373051585179593123)
                      ·
                        rfl

theorem cell23_1664932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_1664932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664932 prefixEnd_1664932 := by exact prefixLift 1664932
  have htrace : WordTrace (prefixWord ++ tailWord_1664932) baseStart_1664932 baseEnd_1664932 := by
    simpa [prefixWord, tailWord_1664932, baseEnd_1664932] using wordTrace_append hprefix tailTrace_1664932
  have hstable : (prefixWord ++ tailWord_1664932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664932).length < 2 ^ (prefixWord ++ tailWord_1664932).sum := by decide
  have hdescent : baseEnd_1664932 < baseStart_1664932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664965 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 1, 7]
def baseStart_1664965 : Nat := 118140960795 + 1664965 * 2 ^ 59
def prefixEnd_1664965 : Nat := 4983230072969 + 3 ^ 40 * 1664965 * 2
def baseEnd_1664965 : Nat := 284975772637727850160157

theorem tailTrace_1664965 : CollatzResearch.WordTrace tailWord_1664965 prefixEnd_1664965 284975772637727850160157 := by
  unfold tailWord_1664965
  simp only [CollatzResearch.WordTrace]
  refine ⟨60726262413123633228580349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40484174942082422152386899 60726262413123633228580349)
  ·
    refine ⟨22772348404921362460717631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60726262413123633228580349 22772348404921362460717631)
    ·
      refine ⟨34158522607382043691076447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22772348404921362460717631 34158522607382043691076447)
      ·
        refine ⟨51237783911073065536614671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34158522607382043691076447 51237783911073065536614671)
        ·
          refine ⟨76856675866609598304922007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51237783911073065536614671 76856675866609598304922007)
          ·
            refine ⟨115285013799914397457383011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76856675866609598304922007 115285013799914397457383011)
            ·
              refine ⟨172927520699871596186074517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115285013799914397457383011 172927520699871596186074517)
              ·
                refine ⟨8105977532806481071222243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172927520699871596186074517 8105977532806481071222243)
                ·
                  refine ⟨12158966299209721606833365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8105977532806481071222243 12158966299209721606833365)
                  ·
                    refine ⟨284975772637727850160157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12158966299209721606833365 284975772637727850160157)
                    ·
                      rfl

theorem cell23_1664965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_1664965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664965 prefixEnd_1664965 := by exact prefixLift 1664965
  have htrace : WordTrace (prefixWord ++ tailWord_1664965) baseStart_1664965 baseEnd_1664965 := by
    simpa [prefixWord, tailWord_1664965, baseEnd_1664965] using wordTrace_append hprefix tailTrace_1664965
  have hstable : (prefixWord ++ tailWord_1664965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664965).length < 2 ^ (prefixWord ++ tailWord_1664965).sum := by decide
  have hdescent : baseEnd_1664965 < baseStart_1664965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1664975 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 7]
def baseStart_1664975 : Nat := 118140960795 + 1664975 * 2 ^ 59
def prefixEnd_1664975 : Nat := 4983230072969 + 3 ^ 40 * 1664975 * 2
def baseEnd_1664975 : Nat := 854932452719728511355425

theorem tailTrace_1664975 : CollatzResearch.WordTrace tailWord_1664975 prefixEnd_1664975 854932452719728511355425 := by
  unfold tailWord_1664975
  simp only [CollatzResearch.WordTrace]
  refine ⟨60726627143087404936444379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40484418095391603290962919 60726627143087404936444379)
  ·
    refine ⟨91089940714631107404666569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60726627143087404936444379 91089940714631107404666569)
    ·
      refine ⟨68317455535973330553499927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91089940714631107404666569 68317455535973330553499927)
      ·
        refine ⟨102476183303959995830249891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68317455535973330553499927 102476183303959995830249891)
        ·
          refine ⟨153714274955939993745374837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102476183303959995830249891 153714274955939993745374837)
          ·
            refine ⟨14410713277119374413628891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 153714274955939993745374837 14410713277119374413628891)
            ·
              refine ⟨21616069915679061620443337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14410713277119374413628891 21616069915679061620443337)
              ·
                refine ⟨16212052436759296215332503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21616069915679061620443337 16212052436759296215332503)
                ·
                  refine ⟨24318078655138944322998755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16212052436759296215332503 24318078655138944322998755)
                  ·
                    refine ⟨36477117982708416484498133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24318078655138944322998755 36477117982708416484498133)
                    ·
                      refine ⟨854932452719728511355425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36477117982708416484498133 854932452719728511355425)
                      ·
                        rfl

theorem cell23_1664975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_1664975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1664975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1664975 prefixEnd_1664975 := by exact prefixLift 1664975
  have htrace : WordTrace (prefixWord ++ tailWord_1664975) baseStart_1664975 baseEnd_1664975 := by
    simpa [prefixWord, tailWord_1664975, baseEnd_1664975] using wordTrace_append hprefix tailTrace_1664975
  have hstable : (prefixWord ++ tailWord_1664975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1664975).length < 2 ^ (prefixWord ++ tailWord_1664975).sum := by decide
  have hdescent : baseEnd_1664975 < baseStart_1664975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1664975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665029 : List Nat := [1, 3, 1, 1, 2, 5, 1, 2, 3, 4]
def baseStart_1665029 : Nat := 118140960795 + 1665029 * 2 ^ 59
def prefixEnd_1665029 : Nat := 4983230072969 + 3 ^ 40 * 1665029 * 2
def baseEnd_1665029 : Nat := 284986726891690433360059

theorem tailTrace_1665029 : CollatzResearch.WordTrace tailWord_1665029 prefixEnd_1665029 284986726891690433360059 := by
  unfold tailWord_1665029
  simp only [CollatzResearch.WordTrace]
  refine ⟨60728596684891772158910141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40485731123261181439273427 60728596684891772158910141)
  ·
    refine ⟨22773223756834414559591303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60728596684891772158910141 22773223756834414559591303)
    ·
      refine ⟨34159835635251621839386955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22773223756834414559591303 34159835635251621839386955)
      ·
        refine ⟨51239753452877432759080433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34159835635251621839386955 51239753452877432759080433)
        ·
          refine ⟨38429815089658074569310325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51239753452877432759080433 38429815089658074569310325)
          ·
            refine ⟨3602795164655444490872843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38429815089658074569310325 3602795164655444490872843)
            ·
              refine ⟨5404192746983166736309265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3602795164655444490872843 5404192746983166736309265)
              ·
                refine ⟨4053144560237375052231949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5404192746983166736309265 4053144560237375052231949)
                ·
                  refine ⟨1519929210089015644586981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4053144560237375052231949 1519929210089015644586981)
                  ·
                    refine ⟨284986726891690433360059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1519929210089015644586981 284986726891690433360059)
                    ·
                      rfl

theorem cell23_1665029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_1665029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665029 prefixEnd_1665029 := by exact prefixLift 1665029
  have htrace : WordTrace (prefixWord ++ tailWord_1665029) baseStart_1665029 baseEnd_1665029 := by
    simpa [prefixWord, tailWord_1665029, baseEnd_1665029] using wordTrace_append hprefix tailTrace_1665029
  have hstable : (prefixWord ++ tailWord_1665029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665029).length < 2 ^ (prefixWord ++ tailWord_1665029).sum := by decide
  have hdescent : baseEnd_1665029 < baseStart_1665029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665063 : List Nat := [1, 1, 7, 1, 2, 1, 2, 1, 3, 4]
def baseStart_1665063 : Nat := 118140960795 + 1665063 * 2 ^ 59
def prefixEnd_1665063 : Nat := 4983230072969 + 3 ^ 40 * 1665063 * 2
def baseEnd_1665063 : Nat := 284992546339108055685007

theorem tailTrace_1665063 : CollatzResearch.WordTrace tailWord_1665063 prefixEnd_1665063 284992546339108055685007 := by
  unfold tailWord_1665063
  simp only [CollatzResearch.WordTrace]
  refine ⟨60729836766768595965647843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40486557844512397310431895 60729836766768595965647843)
  ·
    refine ⟨91094755150152893948471765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60729836766768595965647843 91094755150152893948471765)
    ·
      refine ⟨2135033323831708451917307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 91094755150152893948471765 2135033323831708451917307)
      ·
        refine ⟨3202549985747562677875961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2135033323831708451917307 3202549985747562677875961)
        ·
          refine ⟨2401912489310672008406971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3202549985747562677875961 2401912489310672008406971)
          ·
            refine ⟨3602868733966008012610457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401912489310672008406971 3602868733966008012610457)
            ·
              refine ⟨2702151550474506009457843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3602868733966008012610457 2702151550474506009457843)
              ·
                refine ⟨4053227325711759014186765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2702151550474506009457843 4053227325711759014186765)
                ·
                  refine ⟨1519960247141909630320037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4053227325711759014186765 1519960247141909630320037)
                  ·
                    refine ⟨284992546339108055685007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1519960247141909630320037 284992546339108055685007)
                    ·
                      rfl

theorem cell23_1665063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_1665063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665063 prefixEnd_1665063 := by exact prefixLift 1665063
  have htrace : WordTrace (prefixWord ++ tailWord_1665063) baseStart_1665063 baseEnd_1665063 := by
    simpa [prefixWord, tailWord_1665063, baseEnd_1665063] using wordTrace_append hprefix tailTrace_1665063
  have hstable : (prefixWord ++ tailWord_1665063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665063).length < 2 ^ (prefixWord ++ tailWord_1665063).sum := by decide
  have hdescent : baseEnd_1665063 < baseStart_1665063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665079 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 1, 5, 2]
def baseStart_1665079 : Nat := 118140960795 + 1665079 * 2 ^ 59
def prefixEnd_1665079 : Nat := 4983230072969 + 3 ^ 40 * 1665079 * 2
def baseEnd_1665079 : Nat := 854985854707796104454947

theorem tailTrace_1665079 : CollatzResearch.WordTrace tailWord_1665079 prefixEnd_1665079 854985854707796104454947 := by
  unfold tailWord_1665079
  simp only [CollatzResearch.WordTrace]
  refine ⟨60730420334710630698230291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40486946889807087132153527 60730420334710630698230291)
  ·
    refine ⟨91095630502065946047345437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60730420334710630698230291 91095630502065946047345437)
    ·
      refine ⟨34160861438274729767754539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91095630502065946047345437 34160861438274729767754539)
      ·
        refine ⟨51241292157412094651631809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34160861438274729767754539 51241292157412094651631809)
        ·
          refine ⟨38430969118059070988723857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51241292157412094651631809 38430969118059070988723857)
          ·
            refine ⟨28823226838544303241542893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38430969118059070988723857 28823226838544303241542893)
            ·
              refine ⟨10808710064454113715578585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28823226838544303241542893 10808710064454113715578585)
              ·
                refine ⟨8106532548340585286683939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10808710064454113715578585 8106532548340585286683939)
                ·
                  refine ⟨12159798822510877930025909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8106532548340585286683939 12159798822510877930025909)
                  ·
                    refine ⟨1139981139610394805939929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12159798822510877930025909 1139981139610394805939929)
                    ·
                      refine ⟨854985854707796104454947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1139981139610394805939929 854985854707796104454947)
                      ·
                        rfl

theorem cell23_1665079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 5, 2].length) (baseStart_1665079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665079 prefixEnd_1665079 := by exact prefixLift 1665079
  have htrace : WordTrace (prefixWord ++ tailWord_1665079) baseStart_1665079 baseEnd_1665079 := by
    simpa [prefixWord, tailWord_1665079, baseEnd_1665079] using wordTrace_append hprefix tailTrace_1665079
  have hstable : (prefixWord ++ tailWord_1665079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665079).length < 2 ^ (prefixWord ++ tailWord_1665079).sum := by decide
  have hdescent : baseEnd_1665079 < baseStart_1665079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665120 : List Nat := [2, 1, 1, 3, 2, 4, 3, 2, 1, 1, 3]
def baseStart_1665120 : Nat := 118140960795 + 1665120 * 2 ^ 59
def prefixEnd_1665120 : Nat := 4983230072969 + 3 ^ 40 * 1665120 * 2
def baseEnd_1665120 : Nat := 855006907414630444042259

theorem tailTrace_1665120 : CollatzResearch.WordTrace tailWord_1665120 prefixEnd_1665120 855006907414630444042259 := by
  unfold tailWord_1665120
  simp only [CollatzResearch.WordTrace]
  refine ⟨30365957863781047350236407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40487943818374729800315209 30365957863781047350236407)
  ·
    refine ⟨45548936795671571025354611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30365957863781047350236407 45548936795671571025354611)
    ·
      refine ⟨68323405193507356538031917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45548936795671571025354611 68323405193507356538031917)
      ·
        refine ⟨25621276947565258701761969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68323405193507356538031917 25621276947565258701761969)
        ·
          refine ⟨19215957710673944026321477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25621276947565258701761969 19215957710673944026321477)
          ·
            refine ⟨3602992070751364504935277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19215957710673944026321477 3602992070751364504935277)
            ·
              refine ⟨1351122026531761689350729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3602992070751364504935277 1351122026531761689350729)
              ·
                refine ⟨1013341519898821267013047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1351122026531761689350729 1013341519898821267013047)
                ·
                  refine ⟨1520012279848231900519571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1013341519898821267013047 1520012279848231900519571)
                  ·
                    refine ⟨2280018419772347850779357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1520012279848231900519571 2280018419772347850779357)
                    ·
                      refine ⟨855006907414630444042259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2280018419772347850779357 855006907414630444042259)
                      ·
                        rfl

theorem cell23_1665120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 1, 1, 3].length) (baseStart_1665120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665120 prefixEnd_1665120 := by exact prefixLift 1665120
  have htrace : WordTrace (prefixWord ++ tailWord_1665120) baseStart_1665120 baseEnd_1665120 := by
    simpa [prefixWord, tailWord_1665120, baseEnd_1665120] using wordTrace_append hprefix tailTrace_1665120
  have hstable : (prefixWord ++ tailWord_1665120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665120).length < 2 ^ (prefixWord ++ tailWord_1665120).sum := by decide
  have hdescent : baseEnd_1665120 < baseStart_1665120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665129 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 3, 2, 3]
def baseStart_1665129 : Nat := 118140960795 + 1665129 * 2 ^ 59
def prefixEnd_1665129 : Nat := 4983230072969 + 3 ^ 40 * 1665129 * 2
def baseEnd_1665129 : Nat := 855011528740520908829717

theorem tailTrace_1665129 : CollatzResearch.WordTrace tailWord_1665129 prefixEnd_1665129 855011528740520908829717 := by
  unfold tailWord_1665129
  simp only [CollatzResearch.WordTrace]
  refine ⟨60732243984529489237550441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40488162656352992825033627 60732243984529489237550441)
  ·
    refine ⟨45549182988397116928162831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60732243984529489237550441 45549182988397116928162831)
    ·
      refine ⟨68323774482595675392244247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45549182988397116928162831 68323774482595675392244247)
      ·
        refine ⟨102485661723893513088366371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68323774482595675392244247 102485661723893513088366371)
        ·
          refine ⟨153728492585840269632549557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102485661723893513088366371 153728492585840269632549557)
          ·
            refine ⟨14412046179922525278051521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 153728492585840269632549557 14412046179922525278051521)
            ·
              refine ⟨10809034634941893958538641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14412046179922525278051521 10809034634941893958538641)
              ·
                refine ⟨8106775976206420468903981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10809034634941893958538641 8106775976206420468903981)
                ·
                  refine ⟨3040040991077407675838993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8106775976206420468903981 3040040991077407675838993)
                  ·
                    refine ⟨2280030743308055756879245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3040040991077407675838993 2280030743308055756879245)
                    ·
                      refine ⟨855011528740520908829717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2280030743308055756879245 855011528740520908829717)
                      ·
                        rfl

theorem cell23_1665129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 2, 3].length) (baseStart_1665129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665129 prefixEnd_1665129 := by exact prefixLift 1665129
  have htrace : WordTrace (prefixWord ++ tailWord_1665129) baseStart_1665129 baseEnd_1665129 := by
    simpa [prefixWord, tailWord_1665129, baseEnd_1665129] using wordTrace_append hprefix tailTrace_1665129
  have hstable : (prefixWord ++ tailWord_1665129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665129).length < 2 ^ (prefixWord ++ tailWord_1665129).sum := by decide
  have hdescent : baseEnd_1665129 < baseStart_1665129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665132 : List Nat := [2, 2, 1, 1, 3, 3, 1, 10]
def baseStart_1665132 : Nat := 118140960795 + 1665132 * 2 ^ 59
def prefixEnd_1665132 : Nat := 4983230072969 + 3 ^ 40 * 1665132 * 2
def baseEnd_1665132 : Nat := 31667150710462385077489

theorem tailTrace_1665132 : CollatzResearch.WordTrace tailWord_1665132 prefixEnd_1665132 31667150710462385077489 := by
  unfold tailWord_1665132
  simp only [CollatzResearch.WordTrace]
  refine ⟨30366176701759310374954825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40488235602345747166606433 30366176701759310374954825)
  ·
    refine ⟨22774632526319482781216119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30366176701759310374954825 22774632526319482781216119)
    ·
      refine ⟨34161948789479224171824179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22774632526319482781216119 34161948789479224171824179)
      ·
        refine ⟨51242923184218836257736269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34161948789479224171824179 51242923184218836257736269)
        ·
          refine ⟨19216096194082063596651101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51242923184218836257736269 19216096194082063596651101)
          ·
            refine ⟨7206036072780773848744163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19216096194082063596651101 7206036072780773848744163)
            ·
              refine ⟨10809054109171160773116245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7206036072780773848744163 10809054109171160773116245)
              ·
                refine ⟨31667150710462385077489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10809054109171160773116245 31667150710462385077489)
                ·
                  rfl

theorem cell23_1665132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 10].length) (baseStart_1665132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665132 prefixEnd_1665132 := by exact prefixLift 1665132
  have htrace : WordTrace (prefixWord ++ tailWord_1665132) baseStart_1665132 baseEnd_1665132 := by
    simpa [prefixWord, tailWord_1665132, baseEnd_1665132] using wordTrace_append hprefix tailTrace_1665132
  have hstable : (prefixWord ++ tailWord_1665132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665132).length < 2 ^ (prefixWord ++ tailWord_1665132).sum := by decide
  have hdescent : baseEnd_1665132 < baseStart_1665132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665136 : List Nat := [2, 1, 1, 1, 5, 3, 1, 3, 2, 4]
def baseStart_1665136 : Nat := 118140960795 + 1665136 * 2 ^ 59
def prefixEnd_1665136 : Nat := 4983230072969 + 3 ^ 40 * 1665136 * 2
def baseEnd_1665136 : Nat := 285005041035034127147395

theorem tailTrace_1665136 : CollatzResearch.WordTrace tailWord_1665136 prefixEnd_1665136 285005041035034127147395 := by
  unfold tailWord_1665136
  simp only [CollatzResearch.WordTrace]
  refine ⟨30366249647752064716527631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40488332863669419622036841 30366249647752064716527631)
  ·
    refine ⟨45549374471628097074791447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30366249647752064716527631 45549374471628097074791447)
    ·
      refine ⟨68324061707442145612187171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45549374471628097074791447 68324061707442145612187171)
      ·
        refine ⟨102486092561163218418280757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68324061707442145612187171 102486092561163218418280757)
        ·
          refine ⟨9608071177609051726713821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102486092561163218418280757 9608071177609051726713821)
          ·
            refine ⟨3603026691603394397517683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9608071177609051726713821 3603026691603394397517683)
            ·
              refine ⟨5404540037405091596276525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3603026691603394397517683 5404540037405091596276525)
              ·
                refine ⟨2026702514026909348603697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5404540037405091596276525 2026702514026909348603697)
                ·
                  refine ⟨1520026885520182011452773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2026702514026909348603697 1520026885520182011452773)
                  ·
                    refine ⟨285005041035034127147395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1520026885520182011452773 285005041035034127147395)
                    ·
                      rfl

theorem cell23_1665136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 2, 4].length) (baseStart_1665136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665136 prefixEnd_1665136 := by exact prefixLift 1665136
  have htrace : WordTrace (prefixWord ++ tailWord_1665136) baseStart_1665136 baseEnd_1665136 := by
    simpa [prefixWord, tailWord_1665136, baseEnd_1665136] using wordTrace_append hprefix tailTrace_1665136
  have hstable : (prefixWord ++ tailWord_1665136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665136).length < 2 ^ (prefixWord ++ tailWord_1665136).sum := by decide
  have hdescent : baseEnd_1665136 < baseStart_1665136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665159 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 3]
def baseStart_1665159 : Nat := 118140960795 + 1665159 * 2 ^ 59
def prefixEnd_1665159 : Nat := 4983230072969 + 3 ^ 40 * 1665159 * 2
def baseEnd_1665159 : Nat := 855026933160155791454579

theorem tailTrace_1665159 : CollatzResearch.WordTrace tailWord_1665159 prefixEnd_1665159 855026933160155791454579 := by
  unfold tailWord_1665159
  simp only [CollatzResearch.WordTrace]
  refine ⟨60733338174420804361142531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40488892116280536240761687 60733338174420804361142531)
  ·
    refine ⟨91100007261631206541713797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60733338174420804361142531 91100007261631206541713797)
    ·
      refine ⟨17081251361555851226571337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91100007261631206541713797 17081251361555851226571337)
      ·
        refine ⟨12810938521166888419928503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17081251361555851226571337 12810938521166888419928503)
        ·
          refine ⟨19216407781750332629892755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12810938521166888419928503 19216407781750332629892755)
          ·
            refine ⟨28824611672625498944839133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19216407781750332629892755 28824611672625498944839133)
            ·
              refine ⟨10809229377234562104314675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28824611672625498944839133 10809229377234562104314675)
              ·
                refine ⟨16213844065851843156472013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10809229377234562104314675 16213844065851843156472013)
                ·
                  refine ⟨6080191524694441183677005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16213844065851843156472013 6080191524694441183677005)
                  ·
                    refine ⟨2280071821760415443878877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6080191524694441183677005 2280071821760415443878877)
                    ·
                      refine ⟨855026933160155791454579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2280071821760415443878877 855026933160155791454579)
                      ·
                        rfl

theorem cell23_1665159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_1665159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665159 prefixEnd_1665159 := by exact prefixLift 1665159
  have htrace : WordTrace (prefixWord ++ tailWord_1665159) baseStart_1665159 baseEnd_1665159 := by
    simpa [prefixWord, tailWord_1665159, baseEnd_1665159] using wordTrace_append hprefix tailTrace_1665159
  have hstable : (prefixWord ++ tailWord_1665159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665159).length < 2 ^ (prefixWord ++ tailWord_1665159).sum := by decide
  have hdescent : baseEnd_1665159 < baseStart_1665159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665220 : List Nat := [2, 3, 3, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_1665220 : Nat := 118140960795 + 1665220 * 2 ^ 59
def prefixEnd_1665220 : Nat := 4983230072969 + 3 ^ 40 * 1665220 * 2
def baseEnd_1665220 : Nat := 855058255480080052791799

theorem tailTrace_1665220 : CollatzResearch.WordTrace tailWord_1665220 prefixEnd_1665220 855058255480080052791799 := by
  unfold tailWord_1665220
  simp only [CollatzResearch.WordTrace]
  refine ⟨30367781513599905889556557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40490375351466541186075409 30367781513599905889556557)
  ·
    refine ⟨11387918067599964708583709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30367781513599905889556557 11387918067599964708583709)
    ·
      refine ⟨4270469275349986765718891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11387918067599964708583709 4270469275349986765718891)
      ·
        refine ⟨6405703913024980148578337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4270469275349986765718891 6405703913024980148578337)
        ·
          refine ⟨4804277934768735111433753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6405703913024980148578337 4804277934768735111433753)
          ·
            refine ⟨3603208451076551333575315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4804277934768735111433753 3603208451076551333575315)
            ·
              refine ⟨5404812676614827000362973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3603208451076551333575315 5404812676614827000362973)
              ·
                refine ⟨2026804753730560125136115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5404812676614827000362973 2026804753730560125136115)
                ·
                  refine ⟨3040207130595840187704173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2026804753730560125136115 3040207130595840187704173)
                  ·
                    refine ⟨1140077673973440070389065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3040207130595840187704173 1140077673973440070389065)
                    ·
                      refine ⟨855058255480080052791799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1140077673973440070389065 855058255480080052791799)
                      ·
                        rfl

theorem cell23_1665220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_1665220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665220 prefixEnd_1665220 := by exact prefixLift 1665220
  have htrace : WordTrace (prefixWord ++ tailWord_1665220) baseStart_1665220 baseEnd_1665220 := by
    simpa [prefixWord, tailWord_1665220, baseEnd_1665220] using wordTrace_append hprefix tailTrace_1665220
  have hstable : (prefixWord ++ tailWord_1665220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665220).length < 2 ^ (prefixWord ++ tailWord_1665220).sum := by decide
  have hdescent : baseEnd_1665220 < baseStart_1665220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665244 : List Nat := [2, 2, 5, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_1665244 : Nat := 118140960795 + 1665244 * 2 ^ 59
def prefixEnd_1665244 : Nat := 4983230072969 + 3 ^ 40 * 1665244 * 2
def baseEnd_1665244 : Nat := 855070579015787958891689

theorem tailTrace_1665244 : CollatzResearch.WordTrace tailWord_1665244 prefixEnd_1665244 855070579015787958891689 := by
  unfold tailWord_1665244
  simp only [CollatzResearch.WordTrace]
  refine ⟨30368219189556431938993393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40490958919408575918657857 30368219189556431938993393)
  ·
    refine ⟨22776164392167323954245045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30368219189556431938993393 22776164392167323954245045)
    ·
      refine ⟨2135265411765686620710473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22776164392167323954245045 2135265411765686620710473)
      ·
        refine ⟨1601449058824264965532855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2135265411765686620710473 1601449058824264965532855)
        ·
          refine ⟨2402173588236397448299283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1601449058824264965532855 2402173588236397448299283)
          ·
            refine ⟨3603260382354596172448925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2402173588236397448299283 3603260382354596172448925)
            ·
              refine ⟨1351222643382973564668347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3603260382354596172448925 1351222643382973564668347)
              ·
                refine ⟨2026833965074460347002521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1351222643382973564668347 2026833965074460347002521)
                ·
                  refine ⟨1520125473805845260251891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2026833965074460347002521 1520125473805845260251891)
                  ·
                    refine ⟨2280188210708767890377837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1520125473805845260251891 2280188210708767890377837)
                    ·
                      refine ⟨855070579015787958891689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2280188210708767890377837 855070579015787958891689)
                      ·
                        rfl

theorem cell23_1665244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_1665244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665244 prefixEnd_1665244 := by exact prefixLift 1665244
  have htrace : WordTrace (prefixWord ++ tailWord_1665244) baseStart_1665244 baseEnd_1665244 := by
    simpa [prefixWord, tailWord_1665244, baseEnd_1665244] using wordTrace_append hprefix tailTrace_1665244
  have hstable : (prefixWord ++ tailWord_1665244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665244).length < 2 ^ (prefixWord ++ tailWord_1665244).sum := by decide
  have hdescent : baseEnd_1665244 < baseStart_1665244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665279 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 5]
def baseStart_1665279 : Nat := 118140960795 + 1665279 * 2 ^ 59
def prefixEnd_1665279 : Nat := 4983230072969 + 3 ^ 40 * 1665279 * 2
def baseEnd_1665279 : Nat := 855088550838695321954027

theorem tailTrace_1665279 : CollatzResearch.WordTrace tailWord_1665279 prefixEnd_1665279 855088550838695321954027 := by
  unfold tailWord_1665279
  simp only [CollatzResearch.WordTrace]
  refine ⟨60737714933986064855510891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40491809955990709903673927 60737714933986064855510891)
  ·
    refine ⟨91106572400979097283266337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60737714933986064855510891 91106572400979097283266337)
    ·
      refine ⟨68329929300734322962449753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91106572400979097283266337 68329929300734322962449753)
      ·
        refine ⟨51247446975550742221837315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68329929300734322962449753 51247446975550742221837315)
        ·
          refine ⟨76871170463326113332755973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51247446975550742221837315 76871170463326113332755973)
          ·
            refine ⟨14413344461873646249891745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76871170463326113332755973 14413344461873646249891745)
            ·
              refine ⟨10810008346405234687418809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14413344461873646249891745 10810008346405234687418809)
              ·
                refine ⟨8107506259803926015564107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10810008346405234687418809 8107506259803926015564107)
                ·
                  refine ⟨12161259389705889023346161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8107506259803926015564107 12161259389705889023346161)
                  ·
                    refine ⟨9120944542279416767509621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12161259389705889023346161 9120944542279416767509621)
                    ·
                      refine ⟨855088550838695321954027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9120944542279416767509621 855088550838695321954027)
                      ·
                        rfl

theorem cell23_1665279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_1665279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665279 prefixEnd_1665279 := by exact prefixLift 1665279
  have htrace : WordTrace (prefixWord ++ tailWord_1665279) baseStart_1665279 baseEnd_1665279 := by
    simpa [prefixWord, tailWord_1665279, baseEnd_1665279] using wordTrace_append hprefix tailTrace_1665279
  have hstable : (prefixWord ++ tailWord_1665279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665279).length < 2 ^ (prefixWord ++ tailWord_1665279).sum := by decide
  have hdescent : baseEnd_1665279 < baseStart_1665279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665369 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 7]
def baseStart_1665369 : Nat := 118140960795 + 1665369 * 2 ^ 59
def prefixEnd_1665369 : Nat := 4983230072969 + 3 ^ 40 * 1665369 * 2
def baseEnd_1665369 : Nat := 855134764097599969828613

theorem tailTrace_1665369 : CollatzResearch.WordTrace tailWord_1665369 prefixEnd_1665369 855134764097599969828613 := by
  unfold tailWord_1665369
  simp only [CollatzResearch.WordTrace]
  refine ⟨60740997503660010226287161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40493998335773340150858107 60740997503660010226287161)
  ·
    refine ⟨45555748127745007669715371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60740997503660010226287161 45555748127745007669715371)
    ·
      refine ⟨68333622191617511504573057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45555748127745007669715371 68333622191617511504573057)
      ·
        refine ⟨51250216643713133628429793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68333622191617511504573057 51250216643713133628429793)
        ·
          refine ⟨38437662482784850221322345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51250216643713133628429793 38437662482784850221322345)
          ·
            refine ⟨28828246862088637665991759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38437662482784850221322345 28828246862088637665991759)
            ·
              refine ⟨43242370293132956498987639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28828246862088637665991759 43242370293132956498987639)
              ·
                refine ⟨64863555439699434748481459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43242370293132956498987639 64863555439699434748481459)
                ·
                  refine ⟨97295333159549152122722189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64863555439699434748481459 97295333159549152122722189)
                  ·
                    refine ⟨36485749934830932046020821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97295333159549152122722189 36485749934830932046020821)
                    ·
                      refine ⟨855134764097599969828613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36485749934830932046020821 855134764097599969828613)
                      ·
                        rfl

theorem cell23_1665369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_1665369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665369 prefixEnd_1665369 := by exact prefixLift 1665369
  have htrace : WordTrace (prefixWord ++ tailWord_1665369) baseStart_1665369 baseEnd_1665369 := by
    simpa [prefixWord, tailWord_1665369, baseEnd_1665369] using wordTrace_append hprefix tailTrace_1665369
  have hstable : (prefixWord ++ tailWord_1665369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665369).length < 2 ^ (prefixWord ++ tailWord_1665369).sum := by decide
  have hdescent : baseEnd_1665369 < baseStart_1665369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665374 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_1665374 : Nat := 118140960795 + 1665374 * 2 ^ 59
def prefixEnd_1665374 : Nat := 4983230072969 + 3 ^ 40 * 1665374 * 2
def baseEnd_1665374 : Nat := 855137331500872450266091

theorem tailTrace_1665374 : CollatzResearch.WordTrace tailWord_1665374 prefixEnd_1665374 855137331500872450266091 := by
  unfold tailWord_1665374
  simp only [CollatzResearch.WordTrace]
  refine ⟨7592647483580237010027397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40494119912427930720146117 7592647483580237010027397)
  ·
    refine ⟨1423621403171294439380137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7592647483580237010027397 1423621403171294439380137)
    ·
      refine ⟨1067716052378470829535103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1423621403171294439380137 1067716052378470829535103)
      ·
        refine ⟨1601574078567706244302655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1067716052378470829535103 1601574078567706244302655)
        ·
          refine ⟨2402361117851559366453983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1601574078567706244302655 2402361117851559366453983)
          ·
            refine ⟨3603541676777339049680975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2402361117851559366453983 3603541676777339049680975)
            ·
              refine ⟨5405312515166008574521463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3603541676777339049680975 5405312515166008574521463)
              ·
                refine ⟨8107968772749012861782195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5405312515166008574521463 8107968772749012861782195)
                ·
                  refine ⟨12161953159123519292673293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8107968772749012861782195 12161953159123519292673293)
                  ·
                    refine ⟨4560732434671319734752485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12161953159123519292673293 4560732434671319734752485)
                    ·
                      refine ⟨855137331500872450266091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4560732434671319734752485 855137331500872450266091)
                      ·
                        rfl

theorem cell23_1665374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_1665374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665374 prefixEnd_1665374 := by exact prefixLift 1665374
  have htrace : WordTrace (prefixWord ++ tailWord_1665374) baseStart_1665374 baseEnd_1665374 := by
    simpa [prefixWord, tailWord_1665374, baseEnd_1665374] using wordTrace_append hprefix tailTrace_1665374
  have hstable : (prefixWord ++ tailWord_1665374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665374).length < 2 ^ (prefixWord ++ tailWord_1665374).sum := by decide
  have hdescent : baseEnd_1665374 < baseStart_1665374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665441 : List Nat := [1, 2, 3, 5, 1, 2, 1, 3, 1, 1, 3]
def baseStart_1665441 : Nat := 118140960795 + 1665441 * 2 ^ 59
def prefixEnd_1665441 : Nat := 4983230072969 + 3 ^ 40 * 1665441 * 2
def baseEnd_1665441 : Nat := 855171734704723688128283

theorem tailTrace_1665441 : CollatzResearch.WordTrace tailWord_1665441 prefixEnd_1665441 855171734704723688128283 := by
  unfold tailWord_1665441
  simp only [CollatzResearch.WordTrace]
  refine ⟨60743623559399166522908177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40495749039599444348605451 60743623559399166522908177)
  ·
    refine ⟨45557717669549374892181133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60743623559399166522908177 45557717669549374892181133)
    ·
      refine ⟨17084144126081015584567925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45557717669549374892181133 17084144126081015584567925)
      ·
        refine ⟨1601638511820095211053243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17084144126081015584567925 1601638511820095211053243)
        ·
          refine ⟨2402457767730142816579865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1601638511820095211053243 2402457767730142816579865)
          ·
            refine ⟨1801843325797607112434899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2402457767730142816579865 1801843325797607112434899)
            ·
              refine ⟨2702764988696410668652349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1801843325797607112434899 2702764988696410668652349)
              ·
                refine ⟨1013536870761154000744631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2702764988696410668652349 1013536870761154000744631)
                ·
                  refine ⟨1520305306141731001116947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1013536870761154000744631 1520305306141731001116947)
                  ·
                    refine ⟨2280457959212596501675421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1520305306141731001116947 2280457959212596501675421)
                    ·
                      refine ⟨855171734704723688128283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2280457959212596501675421 855171734704723688128283)
                      ·
                        rfl

theorem cell23_1665441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_1665441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665441 prefixEnd_1665441 := by exact prefixLift 1665441
  have htrace : WordTrace (prefixWord ++ tailWord_1665441) baseStart_1665441 baseEnd_1665441 := by
    simpa [prefixWord, tailWord_1665441, baseEnd_1665441] using wordTrace_append hprefix tailTrace_1665441
  have hstable : (prefixWord ++ tailWord_1665441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665441).length < 2 ^ (prefixWord ++ tailWord_1665441).sum := by decide
  have hdescent : baseEnd_1665441 < baseStart_1665441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665484 : List Nat := [2, 2, 1, 4, 4, 1, 1, 2, 1, 2, 3]
def baseStart_1665484 : Nat := 118140960795 + 1665484 * 2 ^ 59
def prefixEnd_1665484 : Nat := 4983230072969 + 3 ^ 40 * 1665484 * 2
def baseEnd_1665484 : Nat := 855193814372867019890585

theorem tailTrace_1665484 : CollatzResearch.WordTrace tailWord_1665484 prefixEnd_1665484 855193814372867019890585 := by
  unfold tailWord_1665484
  simp only [CollatzResearch.WordTrace]
  refine ⟨30372595949121692433361753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40496794598828923244482337 30372595949121692433361753)
  ·
    refine ⟨22779446961841269325021315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30372595949121692433361753 22779446961841269325021315)
    ·
      refine ⟨34169170442761903987531973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22779446961841269325021315 34169170442761903987531973)
      ·
        refine ⟨6406719458017856997662245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34169170442761903987531973 6406719458017856997662245)
        ·
          refine ⟨1201259898378348187061671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6406719458017856997662245 1201259898378348187061671)
          ·
            refine ⟨1801889847567522280592507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201259898378348187061671 1801889847567522280592507)
            ·
              refine ⟨2702834771351283420888761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1801889847567522280592507 2702834771351283420888761)
              ·
                refine ⟨2027126078513462565666571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2702834771351283420888761 2027126078513462565666571)
                ·
                  refine ⟨3040689117770193848499857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2027126078513462565666571 3040689117770193848499857)
                  ·
                    refine ⟨2280516838327645386374893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3040689117770193848499857 2280516838327645386374893)
                    ·
                      refine ⟨855193814372867019890585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2280516838327645386374893 855193814372867019890585)
                      ·
                        rfl

theorem cell23_1665484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_1665484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665484 prefixEnd_1665484 := by exact prefixLift 1665484
  have htrace : WordTrace (prefixWord ++ tailWord_1665484) baseStart_1665484 baseEnd_1665484 := by
    simpa [prefixWord, tailWord_1665484, baseEnd_1665484] using wordTrace_append hprefix tailTrace_1665484
  have hstable : (prefixWord ++ tailWord_1665484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665484).length < 2 ^ (prefixWord ++ tailWord_1665484).sum := by decide
  have hdescent : baseEnd_1665484 < baseStart_1665484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665486 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_1665486 : Nat := 118140960795 + 1665486 * 2 ^ 59
def prefixEnd_1665486 : Nat := 4983230072969 + 3 ^ 40 * 1665486 * 2
def baseEnd_1665486 : Nat := 855194841334176012065575

theorem tailTrace_1665486 : CollatzResearch.WordTrace tailWord_1665486 prefixEnd_1665486 855194841334176012065575 := by
  unfold tailWord_1665486
  simp only [CollatzResearch.WordTrace]
  refine ⟨7593158105529517401037039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40496843229490759472197541 7593158105529517401037039)
  ·
    refine ⟨11389737158294276101555559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7593158105529517401037039 11389737158294276101555559)
    ·
      refine ⟨17084605737441414152333339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11389737158294276101555559 17084605737441414152333339)
      ·
        refine ⟨25626908606162121228500009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17084605737441414152333339 25626908606162121228500009)
        ·
          refine ⟨19220181454621590921375007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25626908606162121228500009 19220181454621590921375007)
          ·
            refine ⟨28830272181932386382062511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19220181454621590921375007 28830272181932386382062511)
            ·
              refine ⟨43245408272898579573093767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28830272181932386382062511 43245408272898579573093767)
              ·
                refine ⟨64868112409347869359640651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43245408272898579573093767 64868112409347869359640651)
                ·
                  refine ⟨97302168614021804039460977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64868112409347869359640651 97302168614021804039460977)
                  ·
                    refine ⟨72976626460516353029595733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97302168614021804039460977 72976626460516353029595733)
                    ·
                      refine ⟨855194841334176012065575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 72976626460516353029595733 855194841334176012065575)
                      ·
                        rfl

theorem cell23_1665486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_1665486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665486 prefixEnd_1665486 := by exact prefixLift 1665486
  have htrace : WordTrace (prefixWord ++ tailWord_1665486) baseStart_1665486 baseEnd_1665486 := by
    simpa [prefixWord, tailWord_1665486, baseEnd_1665486] using wordTrace_append hprefix tailTrace_1665486
  have hstable : (prefixWord ++ tailWord_1665486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665486).length < 2 ^ (prefixWord ++ tailWord_1665486).sum := by decide
  have hdescent : baseEnd_1665486 < baseStart_1665486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665496 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 4, 6]
def baseStart_1665496 : Nat := 118140960795 + 1665496 * 2 ^ 59
def prefixEnd_1665496 : Nat := 4983230072969 + 3 ^ 40 * 1665496 * 2
def baseEnd_1665496 : Nat := 285066658713573657646843

theorem tailTrace_1665496 : CollatzResearch.WordTrace tailWord_1665496 prefixEnd_1665496 285066658713573657646843 := by
  unfold tailWord_1665496
  simp only [CollatzResearch.WordTrace]
  refine ⟨30372814787099955458080171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40497086382799940610773561 30372814787099955458080171)
  ·
    refine ⟨45559222180649933187120257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30372814787099955458080171 45559222180649933187120257)
    ·
      refine ⟨34169416635487449890340193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45559222180649933187120257 34169416635487449890340193)
      ·
        refine ⟨25627062476615587417755145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34169416635487449890340193 25627062476615587417755145)
        ·
          refine ⟨19220296857461690563316359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25627062476615587417755145 19220296857461690563316359)
          ·
            refine ⟨28830445286192535844974539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19220296857461690563316359 28830445286192535844974539)
            ·
              refine ⟨43245667929288803767461809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28830445286192535844974539 43245667929288803767461809)
              ·
                refine ⟨32434250946966602825596357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43245667929288803767461809 32434250946966602825596357)
                ·
                  refine ⟨6081422052556238029799317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32434250946966602825596357 6081422052556238029799317)
                  ·
                    refine ⟨285066658713573657646843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6081422052556238029799317 285066658713573657646843)
                    ·
                      rfl

theorem cell23_1665496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_1665496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665496 prefixEnd_1665496 := by exact prefixLift 1665496
  have htrace : WordTrace (prefixWord ++ tailWord_1665496) baseStart_1665496 baseEnd_1665496 := by
    simpa [prefixWord, tailWord_1665496, baseEnd_1665496] using wordTrace_append hprefix tailTrace_1665496
  have hstable : (prefixWord ++ tailWord_1665496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665496).length < 2 ^ (prefixWord ++ tailWord_1665496).sum := by decide
  have hdescent : baseEnd_1665496 < baseStart_1665496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665533 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_1665533 : Nat := 118140960795 + 1665533 * 2 ^ 59
def prefixEnd_1665533 : Nat := 4983230072969 + 3 ^ 40 * 1665533 * 2
def baseEnd_1665533 : Nat := 855218974924937328177859

theorem tailTrace_1665533 : CollatzResearch.WordTrace tailWord_1665533 prefixEnd_1665533 855218974924937328177859 := by
  unfold tailWord_1665533
  simp only [CollatzResearch.WordTrace]
  refine ⟨60746979075065866235257253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40497986050043910823504835 60746979075065866235257253)
  ·
    refine ⟨11390058576574849919110735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60746979075065866235257253 11390058576574849919110735)
    ·
      refine ⟨17085087864862274878666103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11390058576574849919110735 17085087864862274878666103)
      ·
        refine ⟨25627631797293412317999155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17085087864862274878666103 25627631797293412317999155)
        ·
          refine ⟨38441447695940118476998733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25627631797293412317999155 38441447695940118476998733)
          ·
            refine ⟨14415542885977544428874525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38441447695940118476998733 14415542885977544428874525)
            ·
              refine ⟨5405828582241579160827947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14415542885977544428874525 5405828582241579160827947)
              ·
                refine ⟨8108742873362368741241921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5405828582241579160827947 8108742873362368741241921)
                ·
                  refine ⟨6081557155021776555931441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8108742873362368741241921 6081557155021776555931441)
                  ·
                    refine ⟨4561167866266332416948581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6081557155021776555931441 4561167866266332416948581)
                    ·
                      refine ⟨855218974924937328177859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4561167866266332416948581 855218974924937328177859)
                      ·
                        rfl

theorem cell23_1665533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_1665533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665533 prefixEnd_1665533 := by exact prefixLift 1665533
  have htrace : WordTrace (prefixWord ++ tailWord_1665533) baseStart_1665533 baseEnd_1665533 := by
    simpa [prefixWord, tailWord_1665533, baseEnd_1665533] using wordTrace_append hprefix tailTrace_1665533
  have hstable : (prefixWord ++ tailWord_1665533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665533).length < 2 ^ (prefixWord ++ tailWord_1665533).sum := by decide
  have hdescent : baseEnd_1665533 < baseStart_1665533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665537 : List Nat := [1, 2, 4, 1, 3, 2, 2, 1, 1, 4, 2]
def baseStart_1665537 : Nat := 118140960795 + 1665537 * 2 ^ 59
def prefixEnd_1665537 : Nat := 4983230072969 + 3 ^ 40 * 1665537 * 2
def baseEnd_1665537 : Nat := 855221028847555312527841

theorem tailTrace_1665537 : CollatzResearch.WordTrace tailWord_1665537 prefixEnd_1665537 855221028847555312527841 := by
  unfold tailWord_1665537
  simp only [CollatzResearch.WordTrace]
  refine ⟨60747124967051374918402865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40498083311367583278935243 60747124967051374918402865)
  ·
    refine ⟨45560343725288531188802149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60747124967051374918402865 45560343725288531188802149)
    ·
      refine ⟨8542564448491599597900403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45560343725288531188802149 8542564448491599597900403)
      ·
        refine ⟨12813846672737399396850605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8542564448491599597900403 12813846672737399396850605)
        ·
          refine ⟨4805192502276524773818977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12813846672737399396850605 4805192502276524773818977)
          ·
            refine ⟨3603894376707393580364233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4805192502276524773818977 3603894376707393580364233)
            ·
              refine ⟨2702920782530545185273175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3603894376707393580364233 2702920782530545185273175)
              ·
                refine ⟨4054381173795817777909763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2702920782530545185273175 4054381173795817777909763)
                ·
                  refine ⟨6081571760693726666864645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4054381173795817777909763 6081571760693726666864645)
                  ·
                    refine ⟨1140294705130073750037121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6081571760693726666864645 1140294705130073750037121)
                    ·
                      refine ⟨855221028847555312527841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1140294705130073750037121 855221028847555312527841)
                      ·
                        rfl

theorem cell23_1665537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_1665537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665537 prefixEnd_1665537 := by exact prefixLift 1665537
  have htrace : WordTrace (prefixWord ++ tailWord_1665537) baseStart_1665537 baseEnd_1665537 := by
    simpa [prefixWord, tailWord_1665537, baseEnd_1665537] using wordTrace_append hprefix tailTrace_1665537
  have hstable : (prefixWord ++ tailWord_1665537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665537).length < 2 ^ (prefixWord ++ tailWord_1665537).sum := by decide
  have hdescent : baseEnd_1665537 < baseStart_1665537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665560 : List Nat := [2, 1, 2, 3, 3, 1, 1, 5, 5]
def baseStart_1665560 : Nat := 118140960795 + 1665560 * 2 ^ 59
def prefixEnd_1665560 : Nat := 4983230072969 + 3 ^ 40 * 1665560 * 2
def baseEnd_1665560 : Nat := 95025870989178746948915

theorem tailTrace_1665560 : CollatzResearch.WordTrace tailWord_1665560 prefixEnd_1665560 95025870989178746948915 := by
  unfold tailWord_1665560
  simp only [CollatzResearch.WordTrace]
  refine ⟨30373981922984024923245067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40498642563978699897660089 30373981922984024923245067)
  ·
    refine ⟨45560972884476037384867601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30373981922984024923245067 45560972884476037384867601)
    ·
      refine ⟨34170729663357028038650701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45560972884476037384867601 34170729663357028038650701)
      ·
        refine ⟨12814023623758885514494013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34170729663357028038650701 12814023623758885514494013)
        ·
          refine ⟨4805258858909582067935255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12814023623758885514494013 4805258858909582067935255)
          ·
            refine ⟨7207888288364373101902883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4805258858909582067935255 7207888288364373101902883)
            ·
              refine ⟨10811832432546559652854325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7207888288364373101902883 10811832432546559652854325)
              ·
                refine ⟨1013609290551239967455093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10811832432546559652854325 1013609290551239967455093)
                ·
                  refine ⟨95025870989178746948915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1013609290551239967455093 95025870989178746948915)
                  ·
                    rfl

theorem cell23_1665560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 5].length) (baseStart_1665560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665560 prefixEnd_1665560 := by exact prefixLift 1665560
  have htrace : WordTrace (prefixWord ++ tailWord_1665560) baseStart_1665560 baseEnd_1665560 := by
    simpa [prefixWord, tailWord_1665560, baseEnd_1665560] using wordTrace_append hprefix tailTrace_1665560
  have hstable : (prefixWord ++ tailWord_1665560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665560).length < 2 ^ (prefixWord ++ tailWord_1665560).sum := by decide
  have hdescent : baseEnd_1665560 < baseStart_1665560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665573 : List Nat := [1, 3, 1, 2, 2, 1, 2, 4, 2, 5]
def baseStart_1665573 : Nat := 118140960795 + 1665573 * 2 ^ 59
def prefixEnd_1665573 : Nat := 4983230072969 + 3 ^ 40 * 1665573 * 2
def baseEnd_1665573 : Nat := 285079838050372390559225

theorem tailTrace_1665573 : CollatzResearch.WordTrace tailWord_1665573 prefixEnd_1665573 285079838050372390559225 := by
  unfold tailWord_1665573
  simp only [CollatzResearch.WordTrace]
  refine ⟨60748437994920953066713373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40498958663280635377808915 60748437994920953066713373)
  ·
    refine ⟨22780664248095357400017515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60748437994920953066713373 22780664248095357400017515)
    ·
      refine ⟨34170996372143036100026273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22780664248095357400017515 34170996372143036100026273)
      ·
        refine ⟨25628247279107277075019705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34170996372143036100026273 25628247279107277075019705)
        ·
          refine ⟨19221185459330457806264779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25628247279107277075019705 19221185459330457806264779)
          ·
            refine ⟨28831778188995686709397169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19221185459330457806264779 28831778188995686709397169)
            ·
              refine ⟨21623833641746765032047877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28831778188995686709397169 21623833641746765032047877)
              ·
                refine ⟨4054468807827518443508977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21623833641746765032047877 4054468807827518443508977)
                ·
                  refine ⟨3040851605870638832631733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4054468807827518443508977 3040851605870638832631733)
                  ·
                    refine ⟨285079838050372390559225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3040851605870638832631733 285079838050372390559225)
                    ·
                      rfl

theorem cell23_1665573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_1665573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665573 prefixEnd_1665573 := by exact prefixLift 1665573
  have htrace : WordTrace (prefixWord ++ tailWord_1665573) baseStart_1665573 baseEnd_1665573 := by
    simpa [prefixWord, tailWord_1665573, baseEnd_1665573] using wordTrace_append hprefix tailTrace_1665573
  have hstable : (prefixWord ++ tailWord_1665573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665573).length < 2 ^ (prefixWord ++ tailWord_1665573).sum := by decide
  have hdescent : baseEnd_1665573 < baseStart_1665573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665588 : List Nat := [2, 5, 1, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_1665588 : Nat := 118140960795 + 1665588 * 2 ^ 59
def prefixEnd_1665588 : Nat := 4983230072969 + 3 ^ 40 * 1665588 * 2
def baseEnd_1665588 : Nat := 855247216360934612990107

theorem tailTrace_1665588 : CollatzResearch.WordTrace tailWord_1665588 prefixEnd_1665588 855247216360934612990107 := by
  unfold tailWord_1665588
  simp only [CollatzResearch.WordTrace]
  refine ⟨30374492544933305314254709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40499323393244407085672945 30374492544933305314254709)
  ·
    refine ⟨2847608676087497373211379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30374492544933305314254709 2847608676087497373211379)
    ·
      refine ⟨4271413014131246059817069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2847608676087497373211379 4271413014131246059817069)
      ·
        refine ⟨1601779880299217272431401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4271413014131246059817069 1601779880299217272431401)
        ·
          refine ⟨1201334910224412954323551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1601779880299217272431401 1201334910224412954323551)
          ·
            refine ⟨1802002365336619431485327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201334910224412954323551 1802002365336619431485327)
            ·
              refine ⟨2703003548004929147227991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1802002365336619431485327 2703003548004929147227991)
              ·
                refine ⟨4054505322007393720841987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2703003548004929147227991 4054505322007393720841987)
                ·
                  refine ⟨6081757983011090581262981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4054505322007393720841987 6081757983011090581262981)
                  ·
                    refine ⟨1140329621814579483986809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6081757983011090581262981 1140329621814579483986809)
                    ·
                      refine ⟨855247216360934612990107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1140329621814579483986809 855247216360934612990107)
                      ·
                        rfl

theorem cell23_1665588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_1665588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665588 prefixEnd_1665588 := by exact prefixLift 1665588
  have htrace : WordTrace (prefixWord ++ tailWord_1665588) baseStart_1665588 baseEnd_1665588 := by
    simpa [prefixWord, tailWord_1665588, baseEnd_1665588] using wordTrace_append hprefix tailTrace_1665588
  have hstable : (prefixWord ++ tailWord_1665588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665588).length < 2 ^ (prefixWord ++ tailWord_1665588).sum := by decide
  have hdescent : baseEnd_1665588 < baseStart_1665588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665590 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_1665590 : Nat := 118140960795 + 1665590 * 2 ^ 59
def prefixEnd_1665590 : Nat := 4983230072969 + 3 ^ 40 * 1665590 * 2
def baseEnd_1665590 : Nat := 285082747774081201721699

theorem tailTrace_1665590 : CollatzResearch.WordTrace tailWord_1665590 prefixEnd_1665590 285082747774081201721699 := by
  unfold tailWord_1665590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3796816127241210310630139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40499372023906243313388149 3796816127241210310630139)
  ·
    refine ⟨5695224190861815465945209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3796816127241210310630139 5695224190861815465945209)
    ·
      refine ⟨4271418143146361599458907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5695224190861815465945209 4271418143146361599458907)
      ·
        refine ⟨6407127214719542399188361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4271418143146361599458907 6407127214719542399188361)
        ·
          refine ⟨4805345411039656799391271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6407127214719542399188361 4805345411039656799391271)
          ·
            refine ⟨7208018116559485199086907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4805345411039656799391271 7208018116559485199086907)
            ·
              refine ⟨10812027174839227798630361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7208018116559485199086907 10812027174839227798630361)
              ·
                refine ⟨8109020381129420848972771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10812027174839227798630361 8109020381129420848972771)
                ·
                  refine ⟨12163530571694131273459157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8109020381129420848972771 12163530571694131273459157)
                  ·
                    refine ⟨285082747774081201721699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12163530571694131273459157 285082747774081201721699)
                    ·
                      rfl

theorem cell23_1665590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_1665590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665590 prefixEnd_1665590 := by exact prefixLift 1665590
  have htrace : WordTrace (prefixWord ++ tailWord_1665590) baseStart_1665590 baseEnd_1665590 := by
    simpa [prefixWord, tailWord_1665590, baseEnd_1665590] using wordTrace_append hprefix tailTrace_1665590
  have hstable : (prefixWord ++ tailWord_1665590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665590).length < 2 ^ (prefixWord ++ tailWord_1665590).sum := by decide
  have hdescent : baseEnd_1665590 < baseStart_1665590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665593 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 3, 3, 4]
def baseStart_1665593 : Nat := 118140960795 + 1665593 * 2 ^ 59
def prefixEnd_1665593 : Nat := 4983230072969 + 3 ^ 40 * 1665593 * 2
def baseEnd_1665593 : Nat := 855249783764207093427583

theorem tailTrace_1665593 : CollatzResearch.WordTrace tailWord_1665593 prefixEnd_1665593 855249783764207093427583 := by
  unfold tailWord_1665593
  simp only [CollatzResearch.WordTrace]
  refine ⟨60749167454848496482441433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40499444969898997654960955 60749167454848496482441433)
  ·
    refine ⟨45561875591136372361831075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60749167454848496482441433 45561875591136372361831075)
    ·
      refine ⟨68342813386704558542746613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45561875591136372361831075 68342813386704558542746613)
      ·
        refine ⟨6407138755003552363382495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68342813386704558542746613 6407138755003552363382495)
        ·
          refine ⟨9610708132505328545073743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6407138755003552363382495 9610708132505328545073743)
          ·
            refine ⟨14416062198757992817610615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9610708132505328545073743 14416062198757992817610615)
            ·
              refine ⟨21624093298136989226415923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14416062198757992817610615 21624093298136989226415923)
              ·
                refine ⟨32436139947205483839623885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21624093298136989226415923 32436139947205483839623885)
                ·
                  refine ⟨12163552480202056439858957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32436139947205483839623885 12163552480202056439858957)
                  ·
                    refine ⟨4561332180075771164947109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12163552480202056439858957 4561332180075771164947109)
                    ·
                      refine ⟨855249783764207093427583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4561332180075771164947109 855249783764207093427583)
                      ·
                        rfl

theorem cell23_1665593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_1665593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665593 prefixEnd_1665593 := by exact prefixLift 1665593
  have htrace : WordTrace (prefixWord ++ tailWord_1665593) baseStart_1665593 baseEnd_1665593 := by
    simpa [prefixWord, tailWord_1665593, baseEnd_1665593] using wordTrace_append hprefix tailTrace_1665593
  have hstable : (prefixWord ++ tailWord_1665593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665593).length < 2 ^ (prefixWord ++ tailWord_1665593).sum := by decide
  have hdescent : baseEnd_1665593 < baseStart_1665593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665633 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 8]
def baseStart_1665633 : Nat := 118140960795 + 1665633 * 2 ^ 59
def prefixEnd_1665633 : Nat := 4983230072969 + 3 ^ 40 * 1665633 * 2
def baseEnd_1665633 : Nat := 95030035887820770769711

theorem tailTrace_1665633 : CollatzResearch.WordTrace tailWord_1665633 prefixEnd_1665633 95030035887820770769711 := by
  unfold tailWord_1665633
  simp only [CollatzResearch.WordTrace]
  refine ⟨60750626374703583313897553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40500417583135722209265035 60750626374703583313897553)
  ·
    refine ⟨45562969781027687485423165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60750626374703583313897553 45562969781027687485423165)
    ·
      refine ⟨17086113667885382807033687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45562969781027687485423165 17086113667885382807033687)
      ·
        refine ⟨25629170501828074210550531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17086113667885382807033687 25629170501828074210550531)
        ·
          refine ⟨38443755752742111315825797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25629170501828074210550531 38443755752742111315825797)
          ·
            refine ⟨7208204203639145871717337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38443755752742111315825797 7208204203639145871717337)
            ·
              refine ⟨5406153152729359403788003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7208204203639145871717337 5406153152729359403788003)
              ·
                refine ⟨8109229729094039105682005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5406153152729359403788003 8109229729094039105682005)
                ·
                  refine ⟨95030035887820770769711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8109229729094039105682005 95030035887820770769711)
                  ·
                    rfl

theorem cell23_1665633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 8].length) (baseStart_1665633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665633 prefixEnd_1665633 := by exact prefixLift 1665633
  have htrace : WordTrace (prefixWord ++ tailWord_1665633) baseStart_1665633 baseEnd_1665633 := by
    simpa [prefixWord, tailWord_1665633, baseEnd_1665633] using wordTrace_append hprefix tailTrace_1665633
  have hstable : (prefixWord ++ tailWord_1665633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665633).length < 2 ^ (prefixWord ++ tailWord_1665633).sum := by decide
  have hdescent : baseEnd_1665633 < baseStart_1665633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665643 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 3]
def baseStart_1665643 : Nat := 118140960795 + 1665643 * 2 ^ 59
def prefixEnd_1665643 : Nat := 4983230072969 + 3 ^ 40 * 1665643 * 2
def baseEnd_1665643 : Nat := 855275457796931897802353

theorem tailTrace_1665643 : CollatzResearch.WordTrace tailWord_1665643 prefixEnd_1665643 855275457796931897802353 := by
  unfold tailWord_1665643
  simp only [CollatzResearch.WordTrace]
  refine ⟨60750991104667355021761583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40500660736444903347841055 60750991104667355021761583)
  ·
    refine ⟨91126486657001032532642375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60750991104667355021761583 91126486657001032532642375)
    ·
      refine ⟨136689729985501548798963563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91126486657001032532642375 136689729985501548798963563)
      ·
        refine ⟨205034594978252323198445345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136689729985501548798963563 205034594978252323198445345)
        ·
          refine ⟨153775946233689242398834009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205034594978252323198445345 153775946233689242398834009)
          ·
            refine ⟨115331959675266931799125507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153775946233689242398834009 115331959675266931799125507)
            ·
              refine ⟨172997939512900397698688261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115331959675266931799125507 172997939512900397698688261)
              ·
                refine ⟨32437113658668824568504049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172997939512900397698688261 32437113658668824568504049)
                ·
                  refine ⟨24327835244001618426378037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32437113658668824568504049 24327835244001618426378037)
                  ·
                    refine ⟨2280734554125151727472941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24327835244001618426378037 2280734554125151727472941)
                    ·
                      refine ⟨855275457796931897802353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2280734554125151727472941 855275457796931897802353)
                      ·
                        rfl

theorem cell23_1665643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 3].length) (baseStart_1665643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665643 prefixEnd_1665643 := by exact prefixLift 1665643
  have htrace : WordTrace (prefixWord ++ tailWord_1665643) baseStart_1665643 baseEnd_1665643 := by
    simpa [prefixWord, tailWord_1665643, baseEnd_1665643] using wordTrace_append hprefix tailTrace_1665643
  have hstable : (prefixWord ++ tailWord_1665643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665643).length < 2 ^ (prefixWord ++ tailWord_1665643).sum := by decide
  have hdescent : baseEnd_1665643 < baseStart_1665643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665687 : List Nat := [1, 1, 3, 3, 2, 1, 1, 4, 2, 3, 2]
def baseStart_1665687 : Nat := 118140960795 + 1665687 * 2 ^ 59
def prefixEnd_1665687 : Nat := 4983230072969 + 3 ^ 40 * 1665687 * 2
def baseEnd_1665687 : Nat := 855298050945729725652151

theorem tailTrace_1665687 : CollatzResearch.WordTrace tailWord_1665687 prefixEnd_1665687 855298050945729725652151 := by
  unfold tailWord_1665687
  simp only [CollatzResearch.WordTrace]
  refine ⟨60752595916507950536363315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40501730611005300357575543 60752595916507950536363315)
  ·
    refine ⟨91128893874761925804544973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60752595916507950536363315 91128893874761925804544973)
    ·
      refine ⟨34173335203035722176704365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91128893874761925804544973 34173335203035722176704365)
      ·
        refine ⟨12815000701138395816264137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34173335203035722176704365 12815000701138395816264137)
        ·
          refine ⟨9611250525853796862198103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12815000701138395816264137 9611250525853796862198103)
          ·
            refine ⟨14416875788780695293297155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9611250525853796862198103 14416875788780695293297155)
            ·
              refine ⟨21625313683171042939945733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14416875788780695293297155 21625313683171042939945733)
              ·
                refine ⟨4054746315594570551239825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21625313683171042939945733 4054746315594570551239825)
                ·
                  refine ⟨3041059736695927913429869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4054746315594570551239825 3041059736695927913429869)
                  ·
                    refine ⟨1140397401260972967536201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3041059736695927913429869 1140397401260972967536201)
                    ·
                      refine ⟨855298050945729725652151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1140397401260972967536201 855298050945729725652151)
                      ·
                        rfl

theorem cell23_1665687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_1665687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665687 prefixEnd_1665687 := by exact prefixLift 1665687
  have htrace : WordTrace (prefixWord ++ tailWord_1665687) baseStart_1665687 baseEnd_1665687 := by
    simpa [prefixWord, tailWord_1665687, baseEnd_1665687] using wordTrace_append hprefix tailTrace_1665687
  have hstable : (prefixWord ++ tailWord_1665687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665687).length < 2 ^ (prefixWord ++ tailWord_1665687).sum := by decide
  have hdescent : baseEnd_1665687 < baseStart_1665687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665694 : List Nat := [4, 3, 1, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_1665694 : Nat := 118140960795 + 1665694 * 2 ^ 59
def prefixEnd_1665694 : Nat := 4983230072969 + 3 ^ 40 * 1665694 * 2
def baseEnd_1665694 : Nat := 855301645310311198264619

theorem tailTrace_1665694 : CollatzResearch.WordTrace tailWord_1665694 prefixEnd_1665694 855301645310311198264619 := by
  unfold tailWord_1665694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7594106403435323841483517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40501900818321727154578757 7594106403435323841483517)
  ·
    refine ⟨2847789901288246440556319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7594106403435323841483517 2847789901288246440556319)
    ·
      refine ⟨4271684851932369660834479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2847789901288246440556319 4271684851932369660834479)
      ·
        refine ⟨6407527277898554491251719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4271684851932369660834479 6407527277898554491251719)
        ·
          refine ⟨9611290916847831736877579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6407527277898554491251719 9611290916847831736877579)
          ·
            refine ⟨14416936375271747605316369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9611290916847831736877579 14416936375271747605316369)
            ·
              refine ⟨10812702281453810703987277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14416936375271747605316369 10812702281453810703987277)
              ·
                refine ⟨4054763355545179013995229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10812702281453810703987277 4054763355545179013995229)
                ·
                  refine ⟨1520536258329442130248211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4054763355545179013995229 1520536258329442130248211)
                  ·
                    refine ⟨2280804387494163195372317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1520536258329442130248211 2280804387494163195372317)
                    ·
                      refine ⟨855301645310311198264619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2280804387494163195372317 855301645310311198264619)
                      ·
                        rfl

theorem cell23_1665694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_1665694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665694 prefixEnd_1665694 := by exact prefixLift 1665694
  have htrace : WordTrace (prefixWord ++ tailWord_1665694) baseStart_1665694 baseEnd_1665694 := by
    simpa [prefixWord, tailWord_1665694, baseEnd_1665694] using wordTrace_append hprefix tailTrace_1665694
  have hstable : (prefixWord ++ tailWord_1665694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665694).length < 2 ^ (prefixWord ++ tailWord_1665694).sum := by decide
  have hdescent : baseEnd_1665694 < baseStart_1665694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665700 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_1665700 : Nat := 118140960795 + 1665700 * 2 ^ 59
def prefixEnd_1665700 : Nat := 4983230072969 + 3 ^ 40 * 1665700 * 2
def baseEnd_1665700 : Nat := 855304726194238174789591

theorem tailTrace_1665700 : CollatzResearch.WordTrace tailWord_1665700 prefixEnd_1665700 855304726194238174789591 := by
  unfold tailWord_1665700
  simp only [CollatzResearch.WordTrace]
  refine ⟨30376535032730426878293277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40502046710307235837724369 30376535032730426878293277)
  ·
    refine ⟨11391200637273910079359979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30376535032730426878293277 11391200637273910079359979)
    ·
      refine ⟨17086800955910865119039969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11391200637273910079359979 17086800955910865119039969)
      ·
        refine ⟨12815100716933148839279977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17086800955910865119039969 12815100716933148839279977)
        ·
          refine ⟨9611325537699861629459983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12815100716933148839279977 9611325537699861629459983)
          ·
            refine ⟨14416988306549792444189975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9611325537699861629459983 14416988306549792444189975)
            ·
              refine ⟨21625482459824688666284963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14416988306549792444189975 21625482459824688666284963)
              ·
                refine ⟨32438223689737032999427445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21625482459824688666284963 32438223689737032999427445)
                ·
                  refine ⟨3041083470912846843696323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32438223689737032999427445 3041083470912846843696323)
                  ·
                    refine ⟨4561625206369270265544485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3041083470912846843696323 4561625206369270265544485)
                    ·
                      refine ⟨855304726194238174789591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4561625206369270265544485 855304726194238174789591)
                      ·
                        rfl

theorem cell23_1665700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_1665700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665700 prefixEnd_1665700 := by exact prefixLift 1665700
  have htrace : WordTrace (prefixWord ++ tailWord_1665700) baseStart_1665700 baseEnd_1665700 := by
    simpa [prefixWord, tailWord_1665700, baseEnd_1665700] using wordTrace_append hprefix tailTrace_1665700
  have hstable : (prefixWord ++ tailWord_1665700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665700).length < 2 ^ (prefixWord ++ tailWord_1665700).sum := by decide
  have hdescent : baseEnd_1665700 < baseStart_1665700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665717 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1665717 : Nat := 118140960795 + 1665717 * 2 ^ 59
def prefixEnd_1665717 : Nat := 4983230072969 + 3 ^ 40 * 1665717 * 2
def baseEnd_1665717 : Nat := 855313455365364608277013

theorem tailTrace_1665717 : CollatzResearch.WordTrace tailWord_1665717 prefixEnd_1665717 855313455365364608277013 := by
  unfold tailWord_1665717
  simp only [CollatzResearch.WordTrace]
  refine ⟨60753690106399265659955405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40502460070932843773303603 60753690106399265659955405)
  ·
    refine ⟨22782633789899724622483277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60753690106399265659955405 22782633789899724622483277)
    ·
      refine ⟨8543487671212396733431229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22782633789899724622483277 8543487671212396733431229)
      ·
        refine ⟨3203807876704648775036711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8543487671212396733431229 3203807876704648775036711)
        ·
          refine ⟨4805711815056973162555067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3203807876704648775036711 4805711815056973162555067)
          ·
            refine ⟨7208567722585459743832601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4805711815056973162555067 7208567722585459743832601)
            ·
              refine ⟨5406425791939094807874451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7208567722585459743832601 5406425791939094807874451)
              ·
                refine ⟨8109638687908642211811677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5406425791939094807874451 8109638687908642211811677)
                ·
                  refine ⟨3041114507965740829429379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8109638687908642211811677 3041114507965740829429379)
                  ·
                    refine ⟨4561671761948611244144069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3041114507965740829429379 4561671761948611244144069)
                    ·
                      refine ⟨855313455365364608277013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4561671761948611244144069 855313455365364608277013)
                      ·
                        rfl

theorem cell23_1665717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1665717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665717 prefixEnd_1665717 := by exact prefixLift 1665717
  have htrace : WordTrace (prefixWord ++ tailWord_1665717) baseStart_1665717 baseEnd_1665717 := by
    simpa [prefixWord, tailWord_1665717, baseEnd_1665717] using wordTrace_append hprefix tailTrace_1665717
  have hstable : (prefixWord ++ tailWord_1665717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665717).length < 2 ^ (prefixWord ++ tailWord_1665717).sum := by decide
  have hdescent : baseEnd_1665717 < baseStart_1665717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665740 : List Nat := [2, 2, 1, 5, 1, 2, 10]
def baseStart_1665740 : Nat := 118140960795 + 1665740 * 2 ^ 59
def prefixEnd_1665740 : Nat := 4983230072969 + 3 ^ 40 * 1665740 * 2
def baseEnd_1665740 : Nat := 10559571178029852077647

theorem tailTrace_1665740 : CollatzResearch.WordTrace tailWord_1665740 prefixEnd_1665740 10559571178029852077647 := by
  unfold tailWord_1665740
  simp only [CollatzResearch.WordTrace]
  refine ⟨30377264492657970294021337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40503019323543960392028449 30377264492657970294021337)
  ·
    refine ⟨22782948369493477720516003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30377264492657970294021337 22782948369493477720516003)
    ·
      refine ⟨34174422554240216580774005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22782948369493477720516003 34174422554240216580774005)
      ·
        refine ⟨3203852114460020304447563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34174422554240216580774005 3203852114460020304447563)
        ·
          refine ⟨4805778171690030456671345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3203852114460020304447563 4805778171690030456671345)
          ·
            refine ⟨3604333628767522842503509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4805778171690030456671345 3604333628767522842503509)
            ·
              refine ⟨10559571178029852077647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3604333628767522842503509 10559571178029852077647)
              ·
                rfl

theorem cell23_1665740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 10].length) (baseStart_1665740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665740 prefixEnd_1665740 := by exact prefixLift 1665740
  have htrace : WordTrace (prefixWord ++ tailWord_1665740) baseStart_1665740 baseEnd_1665740 := by
    simpa [prefixWord, tailWord_1665740, baseEnd_1665740] using wordTrace_append hprefix tailTrace_1665740
  have hstable : (prefixWord ++ tailWord_1665740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665740).length < 2 ^ (prefixWord ++ tailWord_1665740).sum := by decide
  have hdescent : baseEnd_1665740 < baseStart_1665740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665743 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 6]
def baseStart_1665743 : Nat := 118140960795 + 1665743 * 2 ^ 59
def prefixEnd_1665743 : Nat := 4983230072969 + 3 ^ 40 * 1665743 * 2
def baseEnd_1665743 : Nat := 855326805862381506551893

theorem tailTrace_1665743 : CollatzResearch.WordTrace tailWord_1665743 prefixEnd_1665743 855326805862381506551893 := by
  unfold tailWord_1665743
  simp only [CollatzResearch.WordTrace]
  refine ⟨60754638404305072100401883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40503092269536714733601255 60754638404305072100401883)
  ·
    refine ⟨91131957606457608150602825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60754638404305072100401883 91131957606457608150602825)
    ·
      refine ⟨68348968204843206112952119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91131957606457608150602825 68348968204843206112952119)
      ·
        refine ⟨102523452307264809169428179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68348968204843206112952119 102523452307264809169428179)
        ·
          refine ⟨153785178460897213754142269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102523452307264809169428179 153785178460897213754142269)
          ·
            refine ⟨57669441922836455157803351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153785178460897213754142269 57669441922836455157803351)
            ·
              refine ⟨86504162884254682736705027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57669441922836455157803351 86504162884254682736705027)
              ·
                refine ⟨129756244326382024105057541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86504162884254682736705027 129756244326382024105057541)
                ·
                  refine ⟨24329295811196629519698289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129756244326382024105057541 24329295811196629519698289)
                  ·
                    refine ⟨18246971858397472139773717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24329295811196629519698289 18246971858397472139773717)
                    ·
                      refine ⟨855326805862381506551893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18246971858397472139773717 855326805862381506551893)
                      ·
                        rfl

theorem cell23_1665743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_1665743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665743 prefixEnd_1665743 := by exact prefixLift 1665743
  have htrace : WordTrace (prefixWord ++ tailWord_1665743) baseStart_1665743 baseEnd_1665743 := by
    simpa [prefixWord, tailWord_1665743, baseEnd_1665743] using wordTrace_append hprefix tailTrace_1665743
  have hstable : (prefixWord ++ tailWord_1665743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665743).length < 2 ^ (prefixWord ++ tailWord_1665743).sum := by decide
  have hdescent : baseEnd_1665743 < baseStart_1665743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665751 : List Nat := [1, 1, 3, 2, 1, 4, 2, 4, 1, 2, 2]
def baseStart_1665751 : Nat := 118140960795 + 1665751 * 2 ^ 59
def prefixEnd_1665751 : Nat := 4983230072969 + 3 ^ 40 * 1665751 * 2
def baseEnd_1665751 : Nat := 855330913707617475251857

theorem tailTrace_1665751 : CollatzResearch.WordTrace tailWord_1665751 prefixEnd_1665751 855330913707617475251857 := by
  unfold tailWord_1665751
  simp only [CollatzResearch.WordTrace]
  refine ⟨60754930188276089466693107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40503286792184059644462071 60754930188276089466693107)
  ·
    refine ⟨91132395282414134200039661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60754930188276089466693107 91132395282414134200039661)
    ·
      refine ⟨34174648230905300325014873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91132395282414134200039661 34174648230905300325014873)
      ·
        refine ⟨25630986173178975243761155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34174648230905300325014873 25630986173178975243761155)
        ·
          refine ⟨38446479259768462865641733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25630986173178975243761155 38446479259768462865641733)
          ·
            refine ⟨7208714861206586787307825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38446479259768462865641733 7208714861206586787307825)
            ·
              refine ⟨5406536145904940090480869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7208714861206586787307825 5406536145904940090480869)
              ·
                refine ⟨1013725527357176266965163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5406536145904940090480869 1013725527357176266965163)
                ·
                  refine ⟨1520588291035764400447745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1013725527357176266965163 1520588291035764400447745)
                  ·
                    refine ⟨1140441218276823300335809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1520588291035764400447745 1140441218276823300335809)
                    ·
                      refine ⟨855330913707617475251857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1140441218276823300335809 855330913707617475251857)
                      ·
                        rfl

theorem cell23_1665751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 1, 2, 2].length) (baseStart_1665751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665751 prefixEnd_1665751 := by exact prefixLift 1665751
  have htrace : WordTrace (prefixWord ++ tailWord_1665751) baseStart_1665751 baseEnd_1665751 := by
    simpa [prefixWord, tailWord_1665751, baseEnd_1665751] using wordTrace_append hprefix tailTrace_1665751
  have hstable : (prefixWord ++ tailWord_1665751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665751).length < 2 ^ (prefixWord ++ tailWord_1665751).sum := by decide
  have hdescent : baseEnd_1665751 < baseStart_1665751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665828 : List Nat := [2, 3, 1, 3, 3, 2, 1, 2, 1, 3, 2]
def baseStart_1665828 : Nat := 118140960795 + 1665828 * 2 ^ 59
def prefixEnd_1665828 : Nat := 4983230072969 + 3 ^ 40 * 1665828 * 2
def baseEnd_1665828 : Nat := 855370451718013673989003

theorem tailTrace_1665828 : CollatzResearch.WordTrace tailWord_1665828 prefixEnd_1665828 855370451718013673989003 := by
  unfold tailWord_1665828
  simp only [CollatzResearch.WordTrace]
  refine ⟨30378869304498565808623069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40505159072664754411497425 30378869304498565808623069)
  ·
    refine ⟨11392075989186962178233651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30378869304498565808623069 11392075989186962178233651)
    ·
      refine ⟨17088113983780443267350477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11392075989186962178233651 17088113983780443267350477)
      ·
        refine ⟨6408042743917666225256429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17088113983780443267350477 6408042743917666225256429)
        ·
          refine ⟨2403016028969124834471161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6408042743917666225256429 2403016028969124834471161)
          ·
            refine ⟨1802262021726843625853371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2403016028969124834471161 1802262021726843625853371)
            ·
              refine ⟨2703393032590265438780057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1802262021726843625853371 2703393032590265438780057)
              ·
                refine ⟨2027544774442699079085043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2703393032590265438780057 2027544774442699079085043)
                ·
                  refine ⟨3041317161664048618627565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2027544774442699079085043 3041317161664048618627565)
                  ·
                    refine ⟨1140493935624018231985337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3041317161664048618627565 1140493935624018231985337)
                    ·
                      refine ⟨855370451718013673989003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1140493935624018231985337 855370451718013673989003)
                      ·
                        rfl

theorem cell23_1665828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_1665828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665828 prefixEnd_1665828 := by exact prefixLift 1665828
  have htrace : WordTrace (prefixWord ++ tailWord_1665828) baseStart_1665828 baseEnd_1665828 := by
    simpa [prefixWord, tailWord_1665828, baseEnd_1665828] using wordTrace_append hprefix tailTrace_1665828
  have hstable : (prefixWord ++ tailWord_1665828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665828).length < 2 ^ (prefixWord ++ tailWord_1665828).sum := by decide
  have hdescent : baseEnd_1665828 < baseStart_1665828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665847 : List Nat := [1, 1, 3, 1, 2, 1, 4, 5, 5]
def baseStart_1665847 : Nat := 118140960795 + 1665847 * 2 ^ 59
def prefixEnd_1665847 : Nat := 4983230072969 + 3 ^ 40 * 1665847 * 2
def baseEnd_1665847 : Nat := 95042245316716566627935

theorem tailTrace_1665847 : CollatzResearch.WordTrace tailWord_1665847 prefixEnd_1665847 95042245316716566627935 := by
  unfold tailWord_1665847
  simp only [CollatzResearch.WordTrace]
  refine ⟨60758431595928297862187795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40505621063952198574791863 60758431595928297862187795)
  ·
    refine ⟨91137647393892446793281693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60758431595928297862187795 91137647393892446793281693)
    ·
      refine ⟨34176617772709667547480635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91137647393892446793281693 34176617772709667547480635)
      ·
        refine ⟨51264926659064501321220953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34176617772709667547480635 51264926659064501321220953)
        ·
          refine ⟨38448694994298375990915715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51264926659064501321220953 38448694994298375990915715)
          ·
            refine ⟨57673042491447563986373573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38448694994298375990915715 57673042491447563986373573)
            ·
              refine ⟨10813695467146418247445045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57673042491447563986373573 10813695467146418247445045)
              ·
                refine ⟨1013783950044976710697973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10813695467146418247445045 1013783950044976710697973)
                ·
                  refine ⟨95042245316716566627935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1013783950044976710697973 95042245316716566627935)
                  ·
                    rfl

theorem cell23_1665847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 5].length) (baseStart_1665847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665847 prefixEnd_1665847 := by exact prefixLift 1665847
  have htrace : WordTrace (prefixWord ++ tailWord_1665847) baseStart_1665847 baseEnd_1665847 := by
    simpa [prefixWord, tailWord_1665847, baseEnd_1665847] using wordTrace_append hprefix tailTrace_1665847
  have hstable : (prefixWord ++ tailWord_1665847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665847).length < 2 ^ (prefixWord ++ tailWord_1665847).sum := by decide
  have hdescent : baseEnd_1665847 < baseStart_1665847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1665987 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 4]
def baseStart_1665987 : Nat := 118140960795 + 1665987 * 2 ^ 59
def prefixEnd_1665987 : Nat := 4983230072969 + 3 ^ 40 * 1665987 * 2
def baseEnd_1665987 : Nat := 855452095142078551900771

theorem tailTrace_1665987 : CollatzResearch.WordTrace tailWord_1665987 prefixEnd_1665987 855452095142078551900771 := by
  unfold tailWord_1665987
  simp only [CollatzResearch.WordTrace]
  refine ⟨60763537815421101772284215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40509025210280734514856143 60763537815421101772284215)
  ·
    refine ⟨91145306723131652658426323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60763537815421101772284215 91145306723131652658426323)
    ·
      refine ⟨136717960084697478987639485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91145306723131652658426323 136717960084697478987639485)
      ·
        refine ⟨51269235031761554620364807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136717960084697478987639485 51269235031761554620364807)
        ·
          refine ⟨76903852547642331930547211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51269235031761554620364807 76903852547642331930547211)
          ·
            refine ⟨115355778821463497895820817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76903852547642331930547211 115355778821463497895820817)
            ·
              refine ⟨86516834116097623421865613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115355778821463497895820817 86516834116097623421865613)
              ·
                refine ⟨32443812793536608783199605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86516834116097623421865613 32443812793536608783199605)
                ·
                  refine ⟨3041607449394057073424963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32443812793536608783199605 3041607449394057073424963)
                  ·
                    refine ⟨4562411174091085610137445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3041607449394057073424963 4562411174091085610137445)
                    ·
                      refine ⟨855452095142078551900771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4562411174091085610137445 855452095142078551900771)
                      ·
                        rfl

theorem cell23_1665987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_1665987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1665987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1665987 prefixEnd_1665987 := by exact prefixLift 1665987
  have htrace : WordTrace (prefixWord ++ tailWord_1665987) baseStart_1665987 baseEnd_1665987 := by
    simpa [prefixWord, tailWord_1665987, baseEnd_1665987] using wordTrace_append hprefix tailTrace_1665987
  have hstable : (prefixWord ++ tailWord_1665987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1665987).length < 2 ^ (prefixWord ++ tailWord_1665987).sum := by decide
  have hdescent : baseEnd_1665987 < baseStart_1665987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1665987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666024 : List Nat := [2, 1, 4, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_1666024 : Nat := 118140960795 + 1666024 * 2 ^ 59
def prefixEnd_1666024 : Nat := 4983230072969 + 3 ^ 40 * 1666024 * 2
def baseEnd_1666024 : Nat := 855471093926294907138101

theorem tailTrace_1666024 : CollatzResearch.WordTrace tailWord_1666024 prefixEnd_1666024 855471093926294907138101 := by
  unfold tailWord_1666024
  simp only [CollatzResearch.WordTrace]
  refine ⟨30382443658143528545690563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40509924877524704727587417 30382443658143528545690563)
  ·
    refine ⟨45573665487215292818535845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30382443658143528545690563 45573665487215292818535845)
    ·
      refine ⟨8545062278852867403475471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45573665487215292818535845 8545062278852867403475471)
      ·
        refine ⟨12817593418279301105213207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8545062278852867403475471 12817593418279301105213207)
        ·
          refine ⟨19226390127418951657819811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12817593418279301105213207 19226390127418951657819811)
          ·
            refine ⟨28839585191128427486729717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19226390127418951657819811 28839585191128427486729717)
            ·
              refine ⟨2703711111668290076880911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28839585191128427486729717 2703711111668290076880911)
              ·
                refine ⟨4055566667502435115321367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2703711111668290076880911 4055566667502435115321367)
                ·
                  refine ⟨6083350001253652672982051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4055566667502435115321367 6083350001253652672982051)
                  ·
                    refine ⟨9125025001880479009473077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6083350001253652672982051 9125025001880479009473077)
                    ·
                      refine ⟨855471093926294907138101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9125025001880479009473077 855471093926294907138101)
                      ·
                        rfl

theorem cell23_1666024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_1666024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666024 prefixEnd_1666024 := by exact prefixLift 1666024
  have htrace : WordTrace (prefixWord ++ tailWord_1666024) baseStart_1666024 baseEnd_1666024 := by
    simpa [prefixWord, tailWord_1666024, baseEnd_1666024] using wordTrace_append hprefix tailTrace_1666024
  have hstable : (prefixWord ++ tailWord_1666024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666024).length < 2 ^ (prefixWord ++ tailWord_1666024).sum := by decide
  have hdescent : baseEnd_1666024 < baseStart_1666024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666031 : List Nat := [1, 1, 2, 1, 4, 4, 2, 2, 2, 4]
def baseStart_1666031 : Nat := 118140960795 + 1666031 * 2 ^ 59
def prefixEnd_1666031 : Nat := 4983230072969 + 3 ^ 40 * 1666031 * 2
def baseEnd_1666031 : Nat := 285158229430292126583523

theorem tailTrace_1666031 : CollatzResearch.WordTrace tailWord_1666031 prefixEnd_1666031 285158229430292126583523 := by
  unfold tailWord_1666031
  simp only [CollatzResearch.WordTrace]
  refine ⟨60765142627261697286885947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40510095084841131524590631 60765142627261697286885947)
  ·
    refine ⟨91147713940892545930328921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60765142627261697286885947 91147713940892545930328921)
    ·
      refine ⟨68360785455669409447746691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91147713940892545930328921 68360785455669409447746691)
      ·
        refine ⟨102541178183504114171620037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68360785455669409447746691 102541178183504114171620037)
        ·
          refine ⟨19226470909407021407178757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102541178183504114171620037 19226470909407021407178757)
          ·
            refine ⟨3604963295513816513846017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19226470909407021407178757 3604963295513816513846017)
            ·
              refine ⟨2703722471635362385384513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3604963295513816513846017 2703722471635362385384513)
              ·
                refine ⟨2027791853726521789038385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2703722471635362385384513 2027791853726521789038385)
                ·
                  refine ⟨1520843890294891341778789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2027791853726521789038385 1520843890294891341778789)
                  ·
                    refine ⟨285158229430292126583523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1520843890294891341778789 285158229430292126583523)
                    ·
                      rfl

theorem cell23_1666031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 4].length) (baseStart_1666031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666031 prefixEnd_1666031 := by exact prefixLift 1666031
  have htrace : WordTrace (prefixWord ++ tailWord_1666031) baseStart_1666031 baseEnd_1666031 := by
    simpa [prefixWord, tailWord_1666031, baseEnd_1666031] using wordTrace_append hprefix tailTrace_1666031
  have hstable : (prefixWord ++ tailWord_1666031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666031).length < 2 ^ (prefixWord ++ tailWord_1666031).sum := by decide
  have hdescent : baseEnd_1666031 < baseStart_1666031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666044 : List Nat := [2, 2, 2, 1, 2, 5, 1, 8]
def baseStart_1666044 : Nat := 118140960795 + 1666044 * 2 ^ 59
def prefixEnd_1666044 : Nat := 4983230072969 + 3 ^ 40 * 1666044 * 2
def baseEnd_1666044 : Nat := 31684494945903141810667

theorem tailTrace_1666044 : CollatzResearch.WordTrace tailWord_1666044 prefixEnd_1666044 31684494945903141810667 := by
  unfold tailWord_1666044
  simp only [CollatzResearch.WordTrace]
  refine ⟨30382808388107300253554593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40510411184143067004739457 30382808388107300253554593)
  ·
    refine ⟨22787106291080475190165945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30382808388107300253554593 22787106291080475190165945)
    ·
      refine ⟨17090329718310356392624459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22787106291080475190165945 17090329718310356392624459)
      ·
        refine ⟨25635494577465534588936689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17090329718310356392624459 25635494577465534588936689)
        ·
          refine ⟨19226620933099150941702517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25635494577465534588936689 19226620933099150941702517)
          ·
            refine ⟨1802495712478045400784611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19226620933099150941702517 1802495712478045400784611)
            ·
              refine ⟨2703743568717068101176917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1802495712478045400784611 2703743568717068101176917)
              ·
                refine ⟨31684494945903141810667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2703743568717068101176917 31684494945903141810667)
                ·
                  rfl

theorem cell23_1666044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 8].length) (baseStart_1666044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666044 prefixEnd_1666044 := by exact prefixLift 1666044
  have htrace : WordTrace (prefixWord ++ tailWord_1666044) baseStart_1666044 baseEnd_1666044 := by
    simpa [prefixWord, tailWord_1666044, baseEnd_1666044] using wordTrace_append hprefix tailTrace_1666044
  have hstable : (prefixWord ++ tailWord_1666044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666044).length < 2 ^ (prefixWord ++ tailWord_1666044).sum := by decide
  have hdescent : baseEnd_1666044 < baseStart_1666044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666067 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 5]
def baseStart_1666067 : Nat := 118140960795 + 1666067 * 2 ^ 59
def prefixEnd_1666067 : Nat := 4983230072969 + 3 ^ 40 * 1666067 * 2
def baseEnd_1666067 : Nat := 855493173594438238900403

theorem tailTrace_1666067 : CollatzResearch.WordTrace tailWord_1666067 prefixEnd_1666067 855493173594438238900403 := by
  unfold tailWord_1666067
  simp only [CollatzResearch.WordTrace]
  refine ⟨60766455655131275435196455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40510970436754183623464303 60766455655131275435196455)
  ·
    refine ⟨91149683482696913152794683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60766455655131275435196455 91149683482696913152794683)
    ·
      refine ⟨136724525224045369729192025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91149683482696913152794683 136724525224045369729192025)
      ·
        refine ⟨102543393918034027296894019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136724525224045369729192025 102543393918034027296894019)
        ·
          refine ⟨153815090877051040945341029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102543393918034027296894019 153815090877051040945341029)
          ·
            refine ⟨28840329539447070177251443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153815090877051040945341029 28840329539447070177251443)
            ·
              refine ⟨43260494309170605265877165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28840329539447070177251443 43260494309170605265877165)
              ·
                refine ⟨16222685365938976974703937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43260494309170605265877165 16222685365938976974703937)
                ·
                  refine ⟨12167014024454232731027953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16222685365938976974703937 12167014024454232731027953)
                  ·
                    refine ⟨9125260518340674548270965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12167014024454232731027953 9125260518340674548270965)
                    ·
                      refine ⟨855493173594438238900403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9125260518340674548270965 855493173594438238900403)
                      ·
                        rfl

theorem cell23_1666067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_1666067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666067 prefixEnd_1666067 := by exact prefixLift 1666067
  have htrace : WordTrace (prefixWord ++ tailWord_1666067) baseStart_1666067 baseEnd_1666067 := by
    simpa [prefixWord, tailWord_1666067, baseEnd_1666067] using wordTrace_append hprefix tailTrace_1666067
  have hstable : (prefixWord ++ tailWord_1666067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666067).length < 2 ^ (prefixWord ++ tailWord_1666067).sum := by decide
  have hdescent : baseEnd_1666067 < baseStart_1666067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666071 : List Nat := [1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 3]
def baseStart_1666071 : Nat := 118140960795 + 1666071 * 2 ^ 59
def prefixEnd_1666071 : Nat := 4983230072969 + 3 ^ 40 * 1666071 * 2
def baseEnd_1666071 : Nat := 855495227517056223250385

theorem tailTrace_1666071 : CollatzResearch.WordTrace tailWord_1666071 prefixEnd_1666071 855495227517056223250385 := by
  unfold tailWord_1666071
  simp only [CollatzResearch.WordTrace]
  refine ⟨60766601547116784118342067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40511067698077856078894711 60766601547116784118342067)
  ·
    refine ⟨91149902320675176177513101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60766601547116784118342067 91149902320675176177513101)
    ·
      refine ⟨34181213370253191066567413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91149902320675176177513101 34181213370253191066567413)
      ·
        refine ⟨3204488753461236662490695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34181213370253191066567413 3204488753461236662490695)
        ·
          refine ⟨4806733130191854993736043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3204488753461236662490695 4806733130191854993736043)
          ·
            refine ⟨7210099695287782490604065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4806733130191854993736043 7210099695287782490604065)
            ·
              refine ⟨5407574771465836867953049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7210099695287782490604065 5407574771465836867953049)
              ·
                refine ⟨4055681078599377650964787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5407574771465836867953049 4055681078599377650964787)
                ·
                  refine ⟨6083521617899066476447181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4055681078599377650964787 6083521617899066476447181)
                  ·
                    refine ⟨2281320606712149928667693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6083521617899066476447181 2281320606712149928667693)
                    ·
                      refine ⟨855495227517056223250385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2281320606712149928667693 855495227517056223250385)
                      ·
                        rfl

theorem cell23_1666071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_1666071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666071 prefixEnd_1666071 := by exact prefixLift 1666071
  have htrace : WordTrace (prefixWord ++ tailWord_1666071) baseStart_1666071 baseEnd_1666071 := by
    simpa [prefixWord, tailWord_1666071, baseEnd_1666071] using wordTrace_append hprefix tailTrace_1666071
  have hstable : (prefixWord ++ tailWord_1666071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666071).length < 2 ^ (prefixWord ++ tailWord_1666071).sum := by decide
  have hdescent : baseEnd_1666071 < baseStart_1666071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666104 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 2, 6]
def baseStart_1666104 : Nat := 118140960795 + 1666104 * 2 ^ 59
def prefixEnd_1666104 : Nat := 4983230072969 + 3 ^ 40 * 1666104 * 2
def baseEnd_1666104 : Nat := 285170724126218198045911

theorem tailTrace_1666104 : CollatzResearch.WordTrace tailWord_1666104 prefixEnd_1666104 285170724126218198045911 := by
  unfold tailWord_1666104
  simp only [CollatzResearch.WordTrace]
  refine ⟨30383902577998615377146683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40511870103998153836195577 30383902577998615377146683)
  ·
    refine ⟨45575853866997923065720025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30383902577998615377146683 45575853866997923065720025)
    ·
      refine ⟨34181890400248442299290019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45575853866997923065720025 34181890400248442299290019)
      ·
        refine ⟨51272835600372663448935029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34181890400248442299290019 51272835600372663448935029)
        ·
          refine ⟨4806828337534937198337659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51272835600372663448935029 4806828337534937198337659)
          ·
            refine ⟨7210242506302405797506489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4806828337534937198337659 7210242506302405797506489)
            ·
              refine ⟨5407681879726804348129867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7210242506302405797506489 5407681879726804348129867)
              ·
                refine ⟨8111522819590206522194801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5407681879726804348129867 8111522819590206522194801)
                ·
                  refine ⟨6083642114692654891646101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8111522819590206522194801 6083642114692654891646101)
                  ·
                    refine ⟨285170724126218198045911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6083642114692654891646101 285170724126218198045911)
                    ·
                      rfl

theorem cell23_1666104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_1666104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666104 prefixEnd_1666104 := by exact prefixLift 1666104
  have htrace : WordTrace (prefixWord ++ tailWord_1666104) baseStart_1666104 baseEnd_1666104 := by
    simpa [prefixWord, tailWord_1666104, baseEnd_1666104] using wordTrace_append hprefix tailTrace_1666104
  have hstable : (prefixWord ++ tailWord_1666104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666104).length < 2 ^ (prefixWord ++ tailWord_1666104).sum := by decide
  have hdescent : baseEnd_1666104 < baseStart_1666104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666105 : List Nat := [1, 2, 1, 5, 2, 2, 3, 1, 2, 1, 3]
def baseStart_1666105 : Nat := 118140960795 + 1666105 * 2 ^ 59
def prefixEnd_1666105 : Nat := 4983230072969 + 3 ^ 40 * 1666105 * 2
def baseEnd_1666105 : Nat := 855512685859309090225229

theorem tailTrace_1666105 : CollatzResearch.WordTrace tailWord_1666105 prefixEnd_1666105 855512685859309090225229 := by
  unfold tailWord_1666105
  simp only [CollatzResearch.WordTrace]
  refine ⟨60767841628993607925079769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40511894419329071950053179 60767841628993607925079769)
  ·
    refine ⟨45575881221745205943809827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60767841628993607925079769 45575881221745205943809827)
    ·
      refine ⟨68363821832617808915714741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45575881221745205943809827 68363821832617808915714741)
      ·
        refine ⟨6409108296807919585848257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68363821832617808915714741 6409108296807919585848257)
        ·
          refine ⟨4806831222605939689386193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6409108296807919585848257 4806831222605939689386193)
          ·
            refine ⟨3605123416954454767039645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4806831222605939689386193 3605123416954454767039645)
            ·
              refine ⟨1351921281357920537639867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3605123416954454767039645 1351921281357920537639867)
              ·
                refine ⟨2027881922036880806459801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1351921281357920537639867 2027881922036880806459801)
                ·
                  refine ⟨1520911441527660604844851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2027881922036880806459801 1520911441527660604844851)
                  ·
                    refine ⟨2281367162291490907267277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1520911441527660604844851 2281367162291490907267277)
                    ·
                      refine ⟨855512685859309090225229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2281367162291490907267277 855512685859309090225229)
                      ·
                        rfl

theorem cell23_1666105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_1666105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666105 prefixEnd_1666105 := by exact prefixLift 1666105
  have htrace : WordTrace (prefixWord ++ tailWord_1666105) baseStart_1666105 baseEnd_1666105 := by
    simpa [prefixWord, tailWord_1666105, baseEnd_1666105] using wordTrace_append hprefix tailTrace_1666105
  have hstable : (prefixWord ++ tailWord_1666105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666105).length < 2 ^ (prefixWord ++ tailWord_1666105).sum := by decide
  have hdescent : baseEnd_1666105 < baseStart_1666105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666127 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 7]
def baseStart_1666127 : Nat := 118140960795 + 1666127 * 2 ^ 59
def prefixEnd_1666127 : Nat := 4983230072969 + 3 ^ 40 * 1666127 * 2
def baseEnd_1666127 : Nat := 855523982433708004150127

theorem tailTrace_1666127 : CollatzResearch.WordTrace tailWord_1666127 prefixEnd_1666127 855523982433708004150127 := by
  unfold tailWord_1666127
  simp only [CollatzResearch.WordTrace]
  refine ⟨60768644034913905682380635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40512429356609270454920423 60768644034913905682380635)
  ·
    refine ⟨91152966052370858523570953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60768644034913905682380635 91152966052370858523570953)
    ·
      refine ⟨68364724539278143892678215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91152966052370858523570953 68364724539278143892678215)
      ·
        refine ⟨102547086808917215839017323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68364724539278143892678215 102547086808917215839017323)
        ·
          refine ⟨153820630213375823758525985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102547086808917215839017323 153820630213375823758525985)
          ·
            refine ⟨115365472660031867818894489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153820630213375823758525985 115365472660031867818894489)
            ·
              refine ⟨86524104495023900864170867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115365472660031867818894489 86524104495023900864170867)
              ·
                refine ⟨129786156742535851296256301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86524104495023900864170867 129786156742535851296256301)
                ·
                  refine ⟨48669808778450944236096113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129786156742535851296256301 48669808778450944236096113)
                  ·
                    refine ⟨36502356583838208177072085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48669808778450944236096113 36502356583838208177072085)
                    ·
                      refine ⟨855523982433708004150127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36502356583838208177072085 855523982433708004150127)
                      ·
                        rfl

theorem cell23_1666127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_1666127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666127 prefixEnd_1666127 := by exact prefixLift 1666127
  have htrace : WordTrace (prefixWord ++ tailWord_1666127) baseStart_1666127 baseEnd_1666127 := by
    simpa [prefixWord, tailWord_1666127, baseEnd_1666127] using wordTrace_append hprefix tailTrace_1666127
  have hstable : (prefixWord ++ tailWord_1666127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666127).length < 2 ^ (prefixWord ++ tailWord_1666127).sum := by decide
  have hdescent : baseEnd_1666127 < baseStart_1666127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666151 : List Nat := [1, 1, 5, 1, 1, 5, 1, 1, 7]
def baseStart_1666151 : Nat := 118140960795 + 1666151 * 2 ^ 59
def prefixEnd_1666151 : Nat := 4983230072969 + 3 ^ 40 * 1666151 * 2
def baseEnd_1666151 : Nat := 95059589552157323361113

theorem tailTrace_1666151 : CollatzResearch.WordTrace tailWord_1666151 prefixEnd_1666151 95059589552157323361113 := by
  unfold tailWord_1666151
  simp only [CollatzResearch.WordTrace]
  refine ⟨60769519386826957781254307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40513012924551305187502871 60769519386826957781254307)
  ·
    refine ⟨91154279080240436671881461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60769519386826957781254307 91154279080240436671881461)
    ·
      refine ⟨8545713663772540937988887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91154279080240436671881461 8545713663772540937988887)
      ·
        refine ⟨12818570495658811406983331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8545713663772540937988887 12818570495658811406983331)
        ·
          refine ⟨19227855743488217110474997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12818570495658811406983331 19227855743488217110474997)
          ·
            refine ⟨1802611475952020354107031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19227855743488217110474997 1802611475952020354107031)
            ·
              refine ⟨2703917213928030531160547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1802611475952020354107031 2703917213928030531160547)
              ·
                refine ⟨4055875820892045796740821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2703917213928030531160547 4055875820892045796740821)
                ·
                  refine ⟨95059589552157323361113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4055875820892045796740821 95059589552157323361113)
                  ·
                    rfl

theorem cell23_1666151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 7].length) (baseStart_1666151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666151 prefixEnd_1666151 := by exact prefixLift 1666151
  have htrace : WordTrace (prefixWord ++ tailWord_1666151) baseStart_1666151 baseEnd_1666151 := by
    simpa [prefixWord, tailWord_1666151, baseEnd_1666151] using wordTrace_append hprefix tailTrace_1666151
  have hstable : (prefixWord ++ tailWord_1666151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666151).length < 2 ^ (prefixWord ++ tailWord_1666151).sum := by decide
  have hdescent : baseEnd_1666151 < baseStart_1666151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666238 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_1666238 : Nat := 118140960795 + 1666238 * 2 ^ 59
def prefixEnd_1666238 : Nat := 4983230072969 + 3 ^ 40 * 1666238 * 2
def baseEnd_1666238 : Nat := 855580978786357069862117

theorem tailTrace_1666238 : CollatzResearch.WordTrace tailWord_1666238 prefixEnd_1666238 855580978786357069862117 := by
  unfold tailWord_1666238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7596586567188971454958921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40515128358341181093114245 7596586567188971454958921)
  ·
    refine ⟨5697439925391728591219191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7596586567188971454958921 5697439925391728591219191)
    ·
      refine ⟨8546159888087592886828787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5697439925391728591219191 8546159888087592886828787)
      ·
        refine ⟨12819239832131389330243181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8546159888087592886828787 12819239832131389330243181)
        ·
          refine ⟨4807214937049270998841193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12819239832131389330243181 4807214937049270998841193)
          ·
            refine ⟨3605411202786953249130895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4807214937049270998841193 3605411202786953249130895)
            ·
              refine ⟨5408116804180429873696343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3605411202786953249130895 5408116804180429873696343)
              ·
                refine ⟨8112175206270644810544515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5408116804180429873696343 8112175206270644810544515)
                ·
                  refine ⟨12168262809405967215816773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8112175206270644810544515 12168262809405967215816773)
                  ·
                    refine ⟨2281549276763618852965645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12168262809405967215816773 2281549276763618852965645)
                    ·
                      refine ⟨855580978786357069862117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2281549276763618852965645 855580978786357069862117)
                      ·
                        rfl

theorem cell23_1666238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_1666238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666238 prefixEnd_1666238 := by exact prefixLift 1666238
  have htrace : WordTrace (prefixWord ++ tailWord_1666238) baseStart_1666238 baseEnd_1666238 := by
    simpa [prefixWord, tailWord_1666238, baseEnd_1666238] using wordTrace_append hprefix tailTrace_1666238
  have hstable : (prefixWord ++ tailWord_1666238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666238).length < 2 ^ (prefixWord ++ tailWord_1666238).sum := by decide
  have hdescent : baseEnd_1666238 < baseStart_1666238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666261 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1666261 : Nat := 118140960795 + 1666261 * 2 ^ 59
def prefixEnd_1666261 : Nat := 4983230072969 + 3 ^ 40 * 1666261 * 2
def baseEnd_1666261 : Nat := 855592788841410479874511

theorem tailTrace_1666261 : CollatzResearch.WordTrace tailWord_1666261 prefixEnd_1666261 855592788841410479874511 := by
  unfold tailWord_1666261
  simp only [CollatzResearch.WordTrace]
  refine ⟨60773531416428446567758637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40515687610952297711839091 60773531416428446567758637)
  ·
    refine ⟨22790074281160667462909489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60773531416428446567758637 22790074281160667462909489)
    ·
      refine ⟨17092555710870500597182117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22790074281160667462909489 17092555710870500597182117)
      ·
        refine ⟨3204854195788218861971647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17092555710870500597182117 3204854195788218861971647)
        ·
          refine ⟨4807281293682328292957471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3204854195788218861971647 4807281293682328292957471)
          ·
            refine ⟨7210921940523492439436207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4807281293682328292957471 7210921940523492439436207)
            ·
              refine ⟨10816382910785238659154311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7210921940523492439436207 10816382910785238659154311)
              ·
                refine ⟨16224574366177857988731467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10816382910785238659154311 16224574366177857988731467)
                ·
                  refine ⟨24336861549266786983097201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16224574366177857988731467 24336861549266786983097201)
                  ·
                    refine ⟨18252646161950090237322901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24336861549266786983097201 18252646161950090237322901)
                    ·
                      refine ⟨855592788841410479874511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18252646161950090237322901 855592788841410479874511)
                      ·
                        rfl

theorem cell23_1666261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1666261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666261 prefixEnd_1666261 := by exact prefixLift 1666261
  have htrace : WordTrace (prefixWord ++ tailWord_1666261) baseStart_1666261 baseEnd_1666261 := by
    simpa [prefixWord, tailWord_1666261, baseEnd_1666261] using wordTrace_append hprefix tailTrace_1666261
  have hstable : (prefixWord ++ tailWord_1666261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666261).length < 2 ^ (prefixWord ++ tailWord_1666261).sum := by decide
  have hdescent : baseEnd_1666261 < baseStart_1666261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666262 : List Nat := [5, 2, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_1666262 : Nat := 118140960795 + 1666262 * 2 ^ 59
def prefixEnd_1666262 : Nat := 4983230072969 + 3 ^ 40 * 1666262 * 2
def baseEnd_1666262 : Nat := 285197767440688325320669

theorem tailTrace_1666262 : CollatzResearch.WordTrace tailWord_1666262 prefixEnd_1666262 285197767440688325320669 := by
  unfold tailWord_1666262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3798347993089051483659065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40515711926283215825696693 3798347993089051483659065)
  ·
    refine ⟨2848760994816788612744299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3798347993089051483659065 2848760994816788612744299)
    ·
      refine ⟨4273141492225182919116449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2848760994816788612744299 4273141492225182919116449)
      ·
        refine ⟨3204856119168887189337337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4273141492225182919116449 3204856119168887189337337)
        ·
          refine ⟨2403642089376665392003003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3204856119168887189337337 2403642089376665392003003)
          ·
            refine ⟨3605463134064998088004505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2403642089376665392003003 3605463134064998088004505)
            ·
              refine ⟨2704097350548748566003379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3605463134064998088004505 2704097350548748566003379)
              ·
                refine ⟨4056146025823122849005069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2704097350548748566003379 4056146025823122849005069)
                ·
                  refine ⟨1521054759683671068376901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4056146025823122849005069 1521054759683671068376901)
                  ·
                    refine ⟨285197767440688325320669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1521054759683671068376901 285197767440688325320669)
                    ·
                      rfl

theorem cell23_1666262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_1666262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666262 prefixEnd_1666262 := by exact prefixLift 1666262
  have htrace : WordTrace (prefixWord ++ tailWord_1666262) baseStart_1666262 baseEnd_1666262 := by
    simpa [prefixWord, tailWord_1666262, baseEnd_1666262] using wordTrace_append hprefix tailTrace_1666262
  have hstable : (prefixWord ++ tailWord_1666262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666262).length < 2 ^ (prefixWord ++ tailWord_1666262).sum := by decide
  have hdescent : baseEnd_1666262 < baseStart_1666262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666285 : List Nat := [1, 5, 1, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_1666285 : Nat := 118140960795 + 1666285 * 2 ^ 59
def prefixEnd_1666285 : Nat := 4983230072969 + 3 ^ 40 * 1666285 * 2
def baseEnd_1666285 : Nat := 855605112377118385974401

theorem tailTrace_1666285 : CollatzResearch.WordTrace tailWord_1666285 prefixEnd_1666285 855605112377118385974401 := by
  unfold tailWord_1666285
  simp only [CollatzResearch.WordTrace]
  refine ⟨60774406768341498666632309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40516271178894332444421539 60774406768341498666632309)
  ·
    refine ⟨5697600634532015499996779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60774406768341498666632309 5697600634532015499996779)
    ·
      refine ⟨8546400951798023249995169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5697600634532015499996779 8546400951798023249995169)
      ·
        refine ⟨6409800713848517437496377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8546400951798023249995169 6409800713848517437496377)
        ·
          refine ⟨4807350535386388078122283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6409800713848517437496377 4807350535386388078122283)
          ·
            refine ⟨7211025803079582117183425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4807350535386388078122283 7211025803079582117183425)
            ·
              refine ⟨5408269352309686587887569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7211025803079582117183425 5408269352309686587887569)
              ·
                refine ⟨4056202014232264940915677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5408269352309686587887569 4056202014232264940915677)
                ·
                  refine ⟨1521075755337099352843379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4056202014232264940915677 1521075755337099352843379)
                  ·
                    refine ⟨2281613633005649029265069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1521075755337099352843379 2281613633005649029265069)
                    ·
                      refine ⟨855605112377118385974401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2281613633005649029265069 855605112377118385974401)
                      ·
                        rfl

theorem cell23_1666285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_1666285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666285 prefixEnd_1666285 := by exact prefixLift 1666285
  have htrace : WordTrace (prefixWord ++ tailWord_1666285) baseStart_1666285 baseEnd_1666285 := by
    simpa [prefixWord, tailWord_1666285, baseEnd_1666285] using wordTrace_append hprefix tailTrace_1666285
  have hstable : (prefixWord ++ tailWord_1666285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666285).length < 2 ^ (prefixWord ++ tailWord_1666285).sum := by decide
  have hdescent : baseEnd_1666285 < baseStart_1666285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666318 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 4, 4]
def baseStart_1666318 : Nat := 118140960795 + 1666318 * 2 ^ 59
def prefixEnd_1666318 : Nat := 4983230072969 + 3 ^ 40 * 1666318 * 2
def baseEnd_1666318 : Nat := 285207352412905585620583

theorem tailTrace_1666318 : CollatzResearch.WordTrace tailWord_1666318 prefixEnd_1666318 285207352412905585620583 := by
  unfold tailWord_1666318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7596951297152743162822951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40517073584814630201722405 7596951297152743162822951)
  ·
    refine ⟨11395426945729114744234427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7596951297152743162822951 11395426945729114744234427)
    ·
      refine ⟨17093140418593672116351641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11395426945729114744234427 17093140418593672116351641)
      ·
        refine ⟨12819855313945254087263731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17093140418593672116351641 12819855313945254087263731)
        ·
          refine ⟨19229782970917881130895597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12819855313945254087263731 19229782970917881130895597)
          ·
            refine ⟨7211168614094205424085849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19229782970917881130895597 7211168614094205424085849)
            ·
              refine ⟨5408376460570654068064387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7211168614094205424085849 5408376460570654068064387)
              ·
                refine ⟨8112564690855981102096581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5408376460570654068064387 8112564690855981102096581)
                ·
                  refine ⟨1521105879535496456643109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8112564690855981102096581 1521105879535496456643109)
                  ·
                    refine ⟨285207352412905585620583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1521105879535496456643109 285207352412905585620583)
                    ·
                      rfl

theorem cell23_1666318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_1666318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666318 prefixEnd_1666318 := by exact prefixLift 1666318
  have htrace : WordTrace (prefixWord ++ tailWord_1666318) baseStart_1666318 baseEnd_1666318 := by
    simpa [prefixWord, tailWord_1666318, baseEnd_1666318] using wordTrace_append hprefix tailTrace_1666318
  have hstable : (prefixWord ++ tailWord_1666318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666318).length < 2 ^ (prefixWord ++ tailWord_1666318).sum := by decide
  have hdescent : baseEnd_1666318 < baseStart_1666318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666335 : List Nat := [1, 1, 2, 4, 4, 1, 1, 3, 2, 4]
def baseStart_1666335 : Nat := 118140960795 + 1666335 * 2 ^ 59
def prefixEnd_1666335 : Nat := 4983230072969 + 3 ^ 40 * 1666335 * 2
def baseEnd_1666335 : Nat := 285210262136614396783057

theorem tailTrace_1666335 : CollatzResearch.WordTrace tailWord_1666335 prefixEnd_1666335 285210262136614396783057 := by
  unfold tailWord_1666335
  simp only [CollatzResearch.WordTrace]
  refine ⟨60776230418160357205952459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40517486945440238137301639 60776230418160357205952459)
  ·
    refine ⟨91164345627240535808928689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60776230418160357205952459 91164345627240535808928689)
    ·
      refine ⟨68373259220430401856696517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91164345627240535808928689 68373259220430401856696517)
      ·
        refine ⟨12819986103830700348130597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68373259220430401856696517 12819986103830700348130597)
        ·
          refine ⟨2403747394468256315274487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12819986103830700348130597 2403747394468256315274487)
          ·
            refine ⟨3605621091702384472911731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2403747394468256315274487 3605621091702384472911731)
            ·
              refine ⟨5408431637553576709367597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3605621091702384472911731 5408431637553576709367597)
              ·
                refine ⟨2028161864082591266012849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5408431637553576709367597 2028161864082591266012849)
                ·
                  refine ⟨1521121398061943449509637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2028161864082591266012849 1521121398061943449509637)
                  ·
                    refine ⟨285210262136614396783057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1521121398061943449509637 285210262136614396783057)
                    ·
                      rfl

theorem cell23_1666335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 4].length) (baseStart_1666335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666335 prefixEnd_1666335 := by exact prefixLift 1666335
  have htrace : WordTrace (prefixWord ++ tailWord_1666335) baseStart_1666335 baseEnd_1666335 := by
    simpa [prefixWord, tailWord_1666335, baseEnd_1666335] using wordTrace_append hprefix tailTrace_1666335
  have hstable : (prefixWord ++ tailWord_1666335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666335).length < 2 ^ (prefixWord ++ tailWord_1666335).sum := by decide
  have hdescent : baseEnd_1666335 < baseStart_1666335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666375 : List Nat := [1, 1, 4, 1, 2, 3, 1, 4, 2, 1, 3]
def baseStart_1666375 : Nat := 118140960795 + 1666375 * 2 ^ 59
def prefixEnd_1666375 : Nat := 4983230072969 + 3 ^ 40 * 1666375 * 2
def baseEnd_1666375 : Nat := 855651325636023033848987

theorem tailTrace_1666375 : CollatzResearch.WordTrace tailWord_1666375 prefixEnd_1666375 855651325636023033848987 := by
  unfold tailWord_1666375
  simp only [CollatzResearch.WordTrace]
  refine ⟨60777689338015444037408579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40518459558676962691605719 60777689338015444037408579)
  ·
    refine ⟨91166534007023166056112869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60777689338015444037408579 91166534007023166056112869)
    ·
      refine ⟨17093725126316843635521163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91166534007023166056112869 17093725126316843635521163)
      ·
        refine ⟨25640587689475265453281745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17093725126316843635521163 25640587689475265453281745)
        ·
          refine ⟨19230440767106449089961309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25640587689475265453281745 19230440767106449089961309)
          ·
            refine ⟨7211415287664918408735491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19230440767106449089961309 7211415287664918408735491)
            ·
              refine ⟨10817122931497377613103237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7211415287664918408735491 10817122931497377613103237)
              ·
                refine ⟨2028210549655758302456857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10817122931497377613103237 2028210549655758302456857)
                ·
                  refine ⟨1521157912241818726842643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2028210549655758302456857 1521157912241818726842643)
                  ·
                    refine ⟨2281736868362728090263965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1521157912241818726842643 2281736868362728090263965)
                    ·
                      refine ⟨855651325636023033848987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2281736868362728090263965 855651325636023033848987)
                      ·
                        rfl

theorem cell23_1666375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_1666375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666375 prefixEnd_1666375 := by exact prefixLift 1666375
  have htrace : WordTrace (prefixWord ++ tailWord_1666375) baseStart_1666375 baseEnd_1666375 := by
    simpa [prefixWord, tailWord_1666375, baseEnd_1666375] using wordTrace_append hprefix tailTrace_1666375
  have hstable : (prefixWord ++ tailWord_1666375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666375).length < 2 ^ (prefixWord ++ tailWord_1666375).sum := by decide
  have hdescent : baseEnd_1666375 < baseStart_1666375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666391 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 1, 8]
def baseStart_1666391 : Nat := 118140960795 + 1666391 * 2 ^ 59
def prefixEnd_1666391 : Nat := 4983230072969 + 3 ^ 40 * 1666391 * 2
def baseEnd_1666391 : Nat := 285219847108831657082971

theorem tailTrace_1666391 : CollatzResearch.WordTrace tailWord_1666391 prefixEnd_1666391 285219847108831657082971 := by
  unfold tailWord_1666391
  simp only [CollatzResearch.WordTrace]
  refine ⟨60778272905957478769991027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40518848603971652513327351 60778272905957478769991027)
  ·
    refine ⟨91167409358936218154986541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60778272905957478769991027 91167409358936218154986541)
    ·
      refine ⟨34187778509601081808119953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91167409358936218154986541 34187778509601081808119953)
      ·
        refine ⟨25640833882200811356089965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34187778509601081808119953 25640833882200811356089965)
        ·
          refine ⟨9615312705825304258533737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25640833882200811356089965 9615312705825304258533737)
          ·
            refine ⟨7211484529368978193900303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9615312705825304258533737 7211484529368978193900303)
            ·
              refine ⟨10817226794053467290850455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7211484529368978193900303 10817226794053467290850455)
              ·
                refine ⟨16225840191080200936275683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10817226794053467290850455 16225840191080200936275683)
                ·
                  refine ⟨24338760286620301404413525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16225840191080200936275683 24338760286620301404413525)
                  ·
                    refine ⟨285219847108831657082971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24338760286620301404413525 285219847108831657082971)
                    ·
                      rfl

theorem cell23_1666391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_1666391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666391 prefixEnd_1666391 := by exact prefixLift 1666391
  have htrace : WordTrace (prefixWord ++ tailWord_1666391) baseStart_1666391 baseEnd_1666391 := by
    simpa [prefixWord, tailWord_1666391, baseEnd_1666391] using wordTrace_append hprefix tailTrace_1666391
  have hstable : (prefixWord ++ tailWord_1666391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666391).length < 2 ^ (prefixWord ++ tailWord_1666391).sum := by decide
  have hdescent : baseEnd_1666391 < baseStart_1666391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666401 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_1666401 : Nat := 118140960795 + 1666401 * 2 ^ 59
def prefixEnd_1666401 : Nat := 4983230072969 + 3 ^ 40 * 1666401 * 2
def baseEnd_1666401 : Nat := 855664676133039932123867

theorem tailTrace_1666401 : CollatzResearch.WordTrace tailWord_1666401 prefixEnd_1666401 855664676133039932123867 := by
  unfold tailWord_1666401
  simp only [CollatzResearch.WordTrace]
  refine ⟨60778637635921250477855057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40519091757280833651903371 60778637635921250477855057)
  ·
    refine ⟨45583978226940937858391293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60778637635921250477855057 45583978226940937858391293)
    ·
      refine ⟨17093991835102851696896735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45583978226940937858391293 17093991835102851696896735)
      ·
        refine ⟨25640987752654277545345103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17093991835102851696896735 25640987752654277545345103)
        ·
          refine ⟨38461481628981416318017655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25640987752654277545345103 38461481628981416318017655)
          ·
            refine ⟨57692222443472124477026483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38461481628981416318017655 57692222443472124477026483)
            ·
              refine ⟨86538333665208186715539725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57692222443472124477026483 86538333665208186715539725)
              ·
                refine ⟨32451875124453070018327397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86538333665208186715539725 32451875124453070018327397)
                ·
                  refine ⟨6084726585834950628436387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32451875124453070018327397 6084726585834950628436387)
                  ·
                    refine ⟨9127089878752425942654581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6084726585834950628436387 9127089878752425942654581)
                    ·
                      refine ⟨855664676133039932123867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9127089878752425942654581 855664676133039932123867)
                      ·
                        rfl

theorem cell23_1666401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_1666401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666401 prefixEnd_1666401 := by exact prefixLift 1666401
  have htrace : WordTrace (prefixWord ++ tailWord_1666401) baseStart_1666401 baseEnd_1666401 := by
    simpa [prefixWord, tailWord_1666401, baseEnd_1666401] using wordTrace_append hprefix tailTrace_1666401
  have hstable : (prefixWord ++ tailWord_1666401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666401).length < 2 ^ (prefixWord ++ tailWord_1666401).sum := by decide
  have hdescent : baseEnd_1666401 < baseStart_1666401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666402 : List Nat := [3, 3, 2, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_1666402 : Nat := 118140960795 + 1666402 * 2 ^ 59
def prefixEnd_1666402 : Nat := 4983230072969 + 3 ^ 40 * 1666402 * 2
def baseEnd_1666402 : Nat := 855665189613694428211363

theorem tailTrace_1666402 : CollatzResearch.WordTrace tailWord_1666402 prefixEnd_1666402 855665189613694428211363 := by
  unfold tailWord_1666402
  simp only [CollatzResearch.WordTrace]
  refine ⟨15194668527229406912160365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40519116072611751765760973 15194668527229406912160365)
  ·
    refine ⟨5698000697711027592060137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15194668527229406912160365 5698000697711027592060137)
    ·
      refine ⟨4273500523283270694045103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5698000697711027592060137 4273500523283270694045103)
      ·
        refine ⟨6410250784924906041067655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4273500523283270694045103 6410250784924906041067655)
        ·
          refine ⟨9615376177387359061601483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6410250784924906041067655 9615376177387359061601483)
          ·
            refine ⟨14423064266081038592402225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9615376177387359061601483 14423064266081038592402225)
            ·
              refine ⟨10817298199560778944301669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14423064266081038592402225 10817298199560778944301669)
              ·
                refine ⟨2028243412417646052056563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10817298199560778944301669 2028243412417646052056563)
                ·
                  refine ⟨3042365118626469078084845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2028243412417646052056563 3042365118626469078084845)
                  ·
                    refine ⟨1140886919484925904281817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3042365118626469078084845 1140886919484925904281817)
                    ·
                      refine ⟨855665189613694428211363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1140886919484925904281817 855665189613694428211363)
                      ·
                        rfl

theorem cell23_1666402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_1666402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666402 prefixEnd_1666402 := by exact prefixLift 1666402
  have htrace : WordTrace (prefixWord ++ tailWord_1666402) baseStart_1666402 baseEnd_1666402 := by
    simpa [prefixWord, tailWord_1666402, baseEnd_1666402] using wordTrace_append hprefix tailTrace_1666402
  have hstable : (prefixWord ++ tailWord_1666402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666402).length < 2 ^ (prefixWord ++ tailWord_1666402).sum := by decide
  have hdescent : baseEnd_1666402 < baseStart_1666402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666411 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 4]
def baseStart_1666411 : Nat := 118140960795 + 1666411 * 2 ^ 59
def prefixEnd_1666411 : Nat := 4983230072969 + 3 ^ 40 * 1666411 * 2
def baseEnd_1666411 : Nat := 855669810939584892998821

theorem tailTrace_1666411 : CollatzResearch.WordTrace tailWord_1666411 prefixEnd_1666411 855669810939584892998821 := by
  unfold tailWord_1666411
  simp only [CollatzResearch.WordTrace]
  refine ⟨60779002365885022185719087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40519334910590014790479391 60779002365885022185719087)
  ·
    refine ⟨91168503548827533278578631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60779002365885022185719087 91168503548827533278578631)
    ·
      refine ⟨136752755323241299917867947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91168503548827533278578631 136752755323241299917867947)
      ·
        refine ⟨205129132984861949876801921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136752755323241299917867947 205129132984861949876801921)
        ·
          refine ⟨153846849738646462407601441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205129132984861949876801921 153846849738646462407601441)
          ·
            refine ⟨115385137303984846805701081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153846849738646462407601441 115385137303984846805701081)
            ·
              refine ⟨86538852977988635104275811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115385137303984846805701081 86538852977988635104275811)
              ·
                refine ⟨129808279466982952656413717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86538852977988635104275811 129808279466982952656413717)
                ·
                  refine ⟨6084763100014825905769393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129808279466982952656413717 6084763100014825905769393)
                  ·
                    refine ⟨4563572325011119429327045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6084763100014825905769393 4563572325011119429327045)
                    ·
                      refine ⟨855669810939584892998821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4563572325011119429327045 855669810939584892998821)
                      ·
                        rfl

theorem cell23_1666411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 4].length) (baseStart_1666411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666411 prefixEnd_1666411 := by exact prefixLift 1666411
  have htrace : WordTrace (prefixWord ++ tailWord_1666411) baseStart_1666411 baseEnd_1666411 := by
    simpa [prefixWord, tailWord_1666411, baseEnd_1666411] using wordTrace_append hprefix tailTrace_1666411
  have hstable : (prefixWord ++ tailWord_1666411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666411).length < 2 ^ (prefixWord ++ tailWord_1666411).sum := by decide
  have hdescent : baseEnd_1666411 < baseStart_1666411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666415 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 4, 2, 2]
def baseStart_1666415 : Nat := 118140960795 + 1666415 * 2 ^ 59
def prefixEnd_1666415 : Nat := 4983230072969 + 3 ^ 40 * 1666415 * 2
def baseEnd_1666415 : Nat := 855671864862202877348803

theorem tailTrace_1666415 : CollatzResearch.WordTrace tailWord_1666415 prefixEnd_1666415 855671864862202877348803 := by
  unfold tailWord_1666415
  simp only [CollatzResearch.WordTrace]
  refine ⟨60779148257870530868864699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40519432171913687245909799 60779148257870530868864699)
  ·
    refine ⟨91168722386805796303297049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60779148257870530868864699 91168722386805796303297049)
    ·
      refine ⟨68376541790104347227472787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91168722386805796303297049 68376541790104347227472787)
      ·
        refine ⟨102564812685156520841209181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68376541790104347227472787 102564812685156520841209181)
        ·
          refine ⟨38461804756933695315453443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102564812685156520841209181 38461804756933695315453443)
          ·
            refine ⟨57692707135400542973180165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38461804756933695315453443 57692707135400542973180165)
            ·
              refine ⟨10817382587887601807471281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57692707135400542973180165 10817382587887601807471281)
              ·
                refine ⟨8113036940915701355603461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10817382587887601807471281 8113036940915701355603461)
                ·
                  refine ⟨1521194426421694004175649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8113036940915701355603461 1521194426421694004175649)
                  ·
                    refine ⟨1140895819816270503131737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1521194426421694004175649 1140895819816270503131737)
                    ·
                      refine ⟨855671864862202877348803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1140895819816270503131737 855671864862202877348803)
                      ·
                        rfl

theorem cell23_1666415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 2, 2].length) (baseStart_1666415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666415 prefixEnd_1666415 := by exact prefixLift 1666415
  have htrace : WordTrace (prefixWord ++ tailWord_1666415) baseStart_1666415 baseEnd_1666415 := by
    simpa [prefixWord, tailWord_1666415, baseEnd_1666415] using wordTrace_append hprefix tailTrace_1666415
  have hstable : (prefixWord ++ tailWord_1666415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666415).length < 2 ^ (prefixWord ++ tailWord_1666415).sum := by decide
  have hdescent : baseEnd_1666415 < baseStart_1666415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666468 : List Nat := [2, 3, 1, 2, 1, 1, 1, 5, 2, 5]
def baseStart_1666468 : Nat := 118140960795 + 1666468 * 2 ^ 59
def prefixEnd_1666468 : Nat := 4983230072969 + 3 ^ 40 * 1666468 * 2
def baseEnd_1666468 : Nat := 285233026445630389995353

theorem tailTrace_1666468 : CollatzResearch.WordTrace tailWord_1666468 prefixEnd_1666468 285233026445630389995353 := by
  unfold tailWord_1666468
  simp only [CollatzResearch.WordTrace]
  refine ⟨30390540663339260460272029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40520720884452347280362705 30390540663339260460272029)
  ·
    refine ⟨11396452748752222672602011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30390540663339260460272029 11396452748752222672602011)
    ·
      refine ⟨17094679123128334008903017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11396452748752222672602011 17094679123128334008903017)
      ·
        refine ⟨12821009342346250506677263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17094679123128334008903017 12821009342346250506677263)
        ·
          refine ⟨19231514013519375760015895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12821009342346250506677263 19231514013519375760015895)
          ·
            refine ⟨28847271020279063640023843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19231514013519375760015895 28847271020279063640023843)
            ·
              refine ⟨43270906530418595460035765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28847271020279063640023843 43270906530418595460035765)
              ·
                refine ⟨4056647487226743324378353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43270906530418595460035765 4056647487226743324378353)
                ·
                  refine ⟨3042485615420057493283765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4056647487226743324378353 3042485615420057493283765)
                  ·
                    refine ⟨285233026445630389995353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3042485615420057493283765 285233026445630389995353)
                    ·
                      rfl

theorem cell23_1666468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_1666468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666468 prefixEnd_1666468 := by exact prefixLift 1666468
  have htrace : WordTrace (prefixWord ++ tailWord_1666468) baseStart_1666468 baseEnd_1666468 := by
    simpa [prefixWord, tailWord_1666468, baseEnd_1666468] using wordTrace_append hprefix tailTrace_1666468
  have hstable : (prefixWord ++ tailWord_1666468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666468).length < 2 ^ (prefixWord ++ tailWord_1666468).sum := by decide
  have hdescent : baseEnd_1666468 < baseStart_1666468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666485 : List Nat := [1, 3, 3, 2, 2, 2, 1, 2, 2, 5]
def baseStart_1666485 : Nat := 118140960795 + 1666485 * 2 ^ 59
def prefixEnd_1666485 : Nat := 4983230072969 + 3 ^ 40 * 1666485 * 2
def baseEnd_1666485 : Nat := 285235936169339201157827

theorem tailTrace_1666485 : CollatzResearch.WordTrace tailWord_1666485 prefixEnd_1666485 285235936169339201157827 := by
  unfold tailWord_1666485
  simp only [CollatzResearch.WordTrace]
  refine ⟨60781701367616932823912909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40521134245077955215941939 60781701367616932823912909)
  ·
    refine ⟨22793138012856349808967341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60781701367616932823912909 22793138012856349808967341)
    ·
      refine ⟨8547426754821131178362753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22793138012856349808967341 8547426754821131178362753)
      ·
        refine ⟨6410570066115848383772065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8547426754821131178362753 6410570066115848383772065)
        ·
          refine ⟨4807927549586886287829049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6410570066115848383772065 4807927549586886287829049)
          ·
            refine ⟨3605945662190164715871787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4807927549586886287829049 3605945662190164715871787)
            ·
              refine ⟨5408918493285247073807681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3605945662190164715871787 5408918493285247073807681)
              ·
                refine ⟨4056688869963935305355761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5408918493285247073807681 4056688869963935305355761)
                ·
                  refine ⟨3042516652472951479016821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4056688869963935305355761 3042516652472951479016821)
                  ·
                    refine ⟨285235936169339201157827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3042516652472951479016821 285235936169339201157827)
                    ·
                      rfl

theorem cell23_1666485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_1666485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666485 prefixEnd_1666485 := by exact prefixLift 1666485
  have htrace : WordTrace (prefixWord ++ tailWord_1666485) baseStart_1666485 baseEnd_1666485 := by
    simpa [prefixWord, tailWord_1666485, baseEnd_1666485] using wordTrace_append hprefix tailTrace_1666485
  have hstable : (prefixWord ++ tailWord_1666485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666485).length < 2 ^ (prefixWord ++ tailWord_1666485).sum := by decide
  have hdescent : baseEnd_1666485 < baseStart_1666485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666488 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 4, 1, 4]
def baseStart_1666488 : Nat := 118140960795 + 1666488 * 2 ^ 59
def prefixEnd_1666488 : Nat := 4983230072969 + 3 ^ 40 * 1666488 * 2
def baseEnd_1666488 : Nat := 855709348949981091735967

theorem tailTrace_1666488 : CollatzResearch.WordTrace tailWord_1666488 prefixEnd_1666488 855709348949981091735967 := by
  unfold tailWord_1666488
  simp only [CollatzResearch.WordTrace]
  refine ⟨30390905393303032168136059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40521207191070709557514745 30390905393303032168136059)
  ·
    refine ⟨45586358089954548252204089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30390905393303032168136059 45586358089954548252204089)
    ·
      refine ⟨34189768567465911189153067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45586358089954548252204089 34189768567465911189153067)
      ·
        refine ⟨51284652851198866783729601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34189768567465911189153067 51284652851198866783729601)
        ·
          refine ⟨38463489638399150087797201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51284652851198866783729601 38463489638399150087797201)
          ·
            refine ⟨28847617228799362565847901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38463489638399150087797201 28847617228799362565847901)
            ·
              refine ⟨10817856460799760962192963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28847617228799362565847901 10817856460799760962192963)
              ·
                refine ⟨16226784691199641443289445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10817856460799760962192963 16226784691199641443289445)
                ·
                  refine ⟨3042522129599932770616771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16226784691199641443289445 3042522129599932770616771)
                  ·
                    refine ⟨4563783194399899155925157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3042522129599932770616771 4563783194399899155925157)
                    ·
                      refine ⟨855709348949981091735967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4563783194399899155925157 855709348949981091735967)
                      ·
                        rfl

theorem cell23_1666488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_1666488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666488 prefixEnd_1666488 := by exact prefixLift 1666488
  have htrace : WordTrace (prefixWord ++ tailWord_1666488) baseStart_1666488 baseEnd_1666488 := by
    simpa [prefixWord, tailWord_1666488, baseEnd_1666488] using wordTrace_append hprefix tailTrace_1666488
  have hstable : (prefixWord ++ tailWord_1666488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666488).length < 2 ^ (prefixWord ++ tailWord_1666488).sum := by decide
  have hdescent : baseEnd_1666488 < baseStart_1666488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666545 : List Nat := [1, 2, 2, 2, 3, 3, 2, 2, 6]
def baseStart_1666545 : Nat := 118140960795 + 1666545 * 2 ^ 59
def prefixEnd_1666545 : Nat := 4983230072969 + 3 ^ 40 * 1666545 * 2
def baseEnd_1666545 : Nat := 95082068594143040969245

theorem tailTrace_1666545 : CollatzResearch.WordTrace tailWord_1666545 prefixEnd_1666545 95082068594143040969245 := by
  unfold tailWord_1666545
  simp only [CollatzResearch.WordTrace]
  refine ⟨60783889747399563071097089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40522593164933042047398059 60783889747399563071097089)
  ·
    refine ⟨45587917310549672303322817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60783889747399563071097089 45587917310549672303322817)
    ·
      refine ⟨34190937982912254227492113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45587917310549672303322817 34190937982912254227492113)
      ·
        refine ⟨25643203487184190670619085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34190937982912254227492113 25643203487184190670619085)
        ·
          refine ⟨9616201307694071501482157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25643203487184190670619085 9616201307694071501482157)
          ·
            refine ⟨3606075490385276813055809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9616201307694071501482157 3606075490385276813055809)
            ·
              refine ⟨2704556617788957609791857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3606075490385276813055809 2704556617788957609791857)
              ·
                refine ⟨2028417463341718207343893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2704556617788957609791857 2028417463341718207343893)
                ·
                  refine ⟨95082068594143040969245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2028417463341718207343893 95082068594143040969245)
                  ·
                    rfl

theorem cell23_1666545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 6].length) (baseStart_1666545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666545 prefixEnd_1666545 := by exact prefixLift 1666545
  have htrace : WordTrace (prefixWord ++ tailWord_1666545) baseStart_1666545 baseEnd_1666545 := by
    simpa [prefixWord, tailWord_1666545, baseEnd_1666545] using wordTrace_append hprefix tailTrace_1666545
  have hstable : (prefixWord ++ tailWord_1666545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666545).length < 2 ^ (prefixWord ++ tailWord_1666545).sum := by decide
  have hdescent : baseEnd_1666545 < baseStart_1666545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666562 : List Nat := [3, 4, 1, 2, 1, 1, 2, 3, 6]
def baseStart_1666562 : Nat := 118140960795 + 1666562 * 2 ^ 59
def prefixEnd_1666562 : Nat := 4983230072969 + 3 ^ 40 * 1666562 * 2
def baseEnd_1666562 : Nat := 95083038502045978023403

theorem tailTrace_1666562 : CollatzResearch.WordTrace tailWord_1666562 prefixEnd_1666562 95083038502045978023403 := by
  unfold tailWord_1666562
  simp only [CollatzResearch.WordTrace]
  refine ⟨15196127447084493743616485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40523006525558649982977293 15196127447084493743616485)
  ·
    refine ⟨2849273896328342576928091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15196127447084493743616485 2849273896328342576928091)
    ·
      refine ⟨4273910844492513865392137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2849273896328342576928091 4273910844492513865392137)
      ·
        refine ⟨3205433133369385399044103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4273910844492513865392137 3205433133369385399044103)
        ·
          refine ⟨4808149700054078098566155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3205433133369385399044103 4808149700054078098566155)
          ·
            refine ⟨7212224550081117147849233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4808149700054078098566155 7212224550081117147849233)
            ·
              refine ⟨5409168412560837860886925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7212224550081117147849233 5409168412560837860886925)
              ·
                refine ⟨2028438154710314197832597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5409168412560837860886925 2028438154710314197832597)
                ·
                  refine ⟨95083038502045978023403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2028438154710314197832597 95083038502045978023403)
                  ·
                    rfl

theorem cell23_1666562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_1666562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666562 prefixEnd_1666562 := by exact prefixLift 1666562
  have htrace : WordTrace (prefixWord ++ tailWord_1666562) baseStart_1666562 baseEnd_1666562 := by
    simpa [prefixWord, tailWord_1666562, baseEnd_1666562] using wordTrace_append hprefix tailTrace_1666562
  have hstable : (prefixWord ++ tailWord_1666562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666562).length < 2 ^ (prefixWord ++ tailWord_1666562).sum := by decide
  have hdescent : baseEnd_1666562 < baseStart_1666562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666565 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 1, 5, 2]
def baseStart_1666565 : Nat := 118140960795 + 1666565 * 2 ^ 59
def prefixEnd_1666565 : Nat := 4983230072969 + 3 ^ 40 * 1666565 * 2
def baseEnd_1666565 : Nat := 855748886960377290473113

theorem tailTrace_1666565 : CollatzResearch.WordTrace tailWord_1666565 prefixEnd_1666565 855748886960377290473113 := by
  unfold tailWord_1666565
  simp only [CollatzResearch.WordTrace]
  refine ⟨60784619207327106486825149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40523079471551404324550099 60784619207327106486825149)
  ·
    refine ⟨22794232202747664932559431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60784619207327106486825149 22794232202747664932559431)
    ·
      refine ⟨34191348304121497398839147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22794232202747664932559431 34191348304121497398839147)
      ·
        refine ⟨51287022456182246098258721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34191348304121497398839147 51287022456182246098258721)
        ·
          refine ⟨38465266842136684573694041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51287022456182246098258721 38465266842136684573694041)
          ·
            refine ⟨28848950131602513430270531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38465266842136684573694041 28848950131602513430270531)
            ·
              refine ⟨43273425197403770145405797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28848950131602513430270531 43273425197403770145405797)
              ·
                refine ⟨8113767224513206902263587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43273425197403770145405797 8113767224513206902263587)
                ·
                  refine ⟨12170650836769810353395381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8113767224513206902263587 12170650836769810353395381)
                  ·
                    refine ⟨1140998515947169720630817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12170650836769810353395381 1140998515947169720630817)
                    ·
                      refine ⟨855748886960377290473113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1140998515947169720630817 855748886960377290473113)
                      ·
                        rfl

theorem cell23_1666565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 5, 2].length) (baseStart_1666565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666565 prefixEnd_1666565 := by exact prefixLift 1666565
  have htrace : WordTrace (prefixWord ++ tailWord_1666565) baseStart_1666565 baseEnd_1666565 := by
    simpa [prefixWord, tailWord_1666565, baseEnd_1666565] using wordTrace_append hprefix tailTrace_1666565
  have hstable : (prefixWord ++ tailWord_1666565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666565).length < 2 ^ (prefixWord ++ tailWord_1666565).sum := by decide
  have hdescent : baseEnd_1666565 < baseStart_1666565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666573 : List Nat := [1, 7, 1, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_1666573 : Nat := 118140960795 + 1666573 * 2 ^ 59
def prefixEnd_1666573 : Nat := 4983230072969 + 3 ^ 40 * 1666573 * 2
def baseEnd_1666573 : Nat := 855752994805613259173077

theorem tailTrace_1666573 : CollatzResearch.WordTrace tailWord_1666573 prefixEnd_1666573 855752994805613259173077 := by
  unfold tailWord_1666573
  simp only [CollatzResearch.WordTrace]
  refine ⟨60784910991298123853116373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40523273994198749235410915 60784910991298123853116373)
  ·
    refine ⟨1424646351358549777807415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 60784910991298123853116373 1424646351358549777807415)
    ·
      refine ⟨2136969527037824666711123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1424646351358549777807415 2136969527037824666711123)
      ·
        refine ⟨3205454290556737000066685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2136969527037824666711123 3205454290556737000066685)
        ·
          refine ⟨1202045358958776375025007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3205454290556737000066685 1202045358958776375025007)
          ·
            refine ⟨1803068038438164562537511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202045358958776375025007 1803068038438164562537511)
            ·
              refine ⟨2704602057657246843806267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1803068038438164562537511 2704602057657246843806267)
              ·
                refine ⟨4056903086485870265709401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2704602057657246843806267 4056903086485870265709401)
                ·
                  refine ⟨3042677314864402699282051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4056903086485870265709401 3042677314864402699282051)
                  ·
                    refine ⟨4564015972296604048923077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3042677314864402699282051 4564015972296604048923077)
                    ·
                      refine ⟨855752994805613259173077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4564015972296604048923077 855752994805613259173077)
                      ·
                        rfl

theorem cell23_1666573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_1666573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666573 prefixEnd_1666573 := by exact prefixLift 1666573
  have htrace : WordTrace (prefixWord ++ tailWord_1666573) baseStart_1666573 baseEnd_1666573 := by
    simpa [prefixWord, tailWord_1666573, baseEnd_1666573] using wordTrace_append hprefix tailTrace_1666573
  have hstable : (prefixWord ++ tailWord_1666573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666573).length < 2 ^ (prefixWord ++ tailWord_1666573).sum := by decide
  have hdescent : baseEnd_1666573 < baseStart_1666573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666592 : List Nat := [2, 1, 1, 6, 1, 2, 1, 3, 1, 5]
def baseStart_1666592 : Nat := 118140960795 + 1666592 * 2 ^ 59
def prefixEnd_1666592 : Nat := 4983230072969 + 3 ^ 40 * 1666592 * 2
def baseEnd_1666592 : Nat := 285254250312682894945163

theorem tailTrace_1666592 : CollatzResearch.WordTrace tailWord_1666592 prefixEnd_1666592 285254250312682894945163 := by
  unfold tailWord_1666592
  simp only [CollatzResearch.WordTrace]
  refine ⟨30392801989114645049029015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40523735985486193398705353 30392801989114645049029015)
  ·
    refine ⟨45589202983671967573543523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30392801989114645049029015 45589202983671967573543523)
    ·
      refine ⟨68383804475507951360315285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45589202983671967573543523 68383804475507951360315285)
      ·
        refine ⟨3205490834789435220014779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68383804475507951360315285 3205490834789435220014779)
        ·
          refine ⟨4808236252184152830022169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3205490834789435220014779 4808236252184152830022169)
          ·
            refine ⟨3606177189138114622516627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4808236252184152830022169 3606177189138114622516627)
            ·
              refine ⟨5409265783707171933774941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3606177189138114622516627 5409265783707171933774941)
              ·
                refine ⟨2028474668890189475165603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5409265783707171933774941 2028474668890189475165603)
                ·
                  refine ⟨3042712003335284212748405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2028474668890189475165603 3042712003335284212748405)
                  ·
                    refine ⟨285254250312682894945163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3042712003335284212748405 285254250312682894945163)
                    ·
                      rfl

theorem cell23_1666592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 1, 5].length) (baseStart_1666592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666592 prefixEnd_1666592 := by exact prefixLift 1666592
  have htrace : WordTrace (prefixWord ++ tailWord_1666592) baseStart_1666592 baseEnd_1666592 := by
    simpa [prefixWord, tailWord_1666592, baseEnd_1666592] using wordTrace_append hprefix tailTrace_1666592
  have hstable : (prefixWord ++ tailWord_1666592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666592).length < 2 ^ (prefixWord ++ tailWord_1666592).sum := by decide
  have hdescent : baseEnd_1666592 < baseStart_1666592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666606 : List Nat := [4, 1, 3, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_1666606 : Nat := 118140960795 + 1666606 * 2 ^ 59
def prefixEnd_1666606 : Nat := 4983230072969 + 3 ^ 40 * 1666606 * 2
def baseEnd_1666606 : Nat := 855769939667211630060425

theorem tailTrace_1666606 : CollatzResearch.WordTrace tailWord_1666606 prefixEnd_1666606 855769939667211630060425 := by
  unfold tailWord_1666606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7598264325022321311133459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40524076400119046992711781 7598264325022321311133459)
  ·
    refine ⟨11397396487533481966700189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7598264325022321311133459 11397396487533481966700189)
    ·
      refine ⟨4274023682825055737512571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11397396487533481966700189 4274023682825055737512571)
      ·
        refine ⟨6411035524237583606268857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4274023682825055737512571 6411035524237583606268857)
        ·
          refine ⟨4808276643178187704701643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6411035524237583606268857 4808276643178187704701643)
          ·
            refine ⟨7212414964767281557052465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4808276643178187704701643 7212414964767281557052465)
            ·
              refine ⟨5409311223575461167789349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7212414964767281557052465 5409311223575461167789349)
              ·
                refine ⟨1014245854420398968960503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5409311223575461167789349 1014245854420398968960503)
                ·
                  refine ⟨1521368781630598453440755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1014245854420398968960503 1521368781630598453440755)
                  ·
                    refine ⟨2282053172445897680161133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1521368781630598453440755 2282053172445897680161133)
                    ·
                      refine ⟨855769939667211630060425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2282053172445897680161133 855769939667211630060425)
                      ·
                        rfl

theorem cell23_1666606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_1666606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666606 prefixEnd_1666606 := by exact prefixLift 1666606
  have htrace : WordTrace (prefixWord ++ tailWord_1666606) baseStart_1666606 baseEnd_1666606 := by
    simpa [prefixWord, tailWord_1666606, baseEnd_1666606] using wordTrace_append hprefix tailTrace_1666606
  have hstable : (prefixWord ++ tailWord_1666606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666606).length < 2 ^ (prefixWord ++ tailWord_1666606).sum := by decide
  have hdescent : baseEnd_1666606 < baseStart_1666606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666608 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 6]
def baseStart_1666608 : Nat := 118140960795 + 1666608 * 2 ^ 59
def prefixEnd_1666608 : Nat := 4983230072969 + 3 ^ 40 * 1666608 * 2
def baseEnd_1666608 : Nat := 855770966628520622235415

theorem tailTrace_1666608 : CollatzResearch.WordTrace tailWord_1666608 prefixEnd_1666608 855770966628520622235415 := by
  unfold tailWord_1666608
  simp only [CollatzResearch.WordTrace]
  refine ⟨30393093773085662415320239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40524125030780883220426985 30393093773085662415320239)
  ·
    refine ⟨45589640659628493622980359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30393093773085662415320239 45589640659628493622980359)
    ·
      refine ⟨68384460989442740434470539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45589640659628493622980359 68384460989442740434470539)
      ·
        refine ⟨102576691484164110651705809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68384460989442740434470539 102576691484164110651705809)
        ·
          refine ⟨76932518613123082988779357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102576691484164110651705809 76932518613123082988779357)
          ·
            refine ⟨28849694479921156120792259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76932518613123082988779357 28849694479921156120792259)
            ·
              refine ⟨43274541719881734181188389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28849694479921156120792259 43274541719881734181188389)
              ·
                refine ⟨8113976572477825158972823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43274541719881734181188389 8113976572477825158972823)
                ·
                  refine ⟨12170964858716737738459235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8113976572477825158972823 12170964858716737738459235)
                  ·
                    refine ⟨18256447288075106607688853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12170964858716737738459235 18256447288075106607688853)
                    ·
                      refine ⟨855770966628520622235415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18256447288075106607688853 855770966628520622235415)
                      ·
                        rfl

theorem cell23_1666608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_1666608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666608 prefixEnd_1666608 := by exact prefixLift 1666608
  have htrace : WordTrace (prefixWord ++ tailWord_1666608) baseStart_1666608 baseEnd_1666608 := by
    simpa [prefixWord, tailWord_1666608, baseEnd_1666608] using wordTrace_append hprefix tailTrace_1666608
  have hstable : (prefixWord ++ tailWord_1666608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666608).length < 2 ^ (prefixWord ++ tailWord_1666608).sum := by decide
  have hdescent : baseEnd_1666608 < baseStart_1666608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666615 : List Nat := [1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 5]
def baseStart_1666615 : Nat := 118140960795 + 1666615 * 2 ^ 59
def prefixEnd_1666615 : Nat := 4983230072969 + 3 ^ 40 * 1666615 * 2
def baseEnd_1666615 : Nat := 855774560993102094847883

theorem tailTrace_1666615 : CollatzResearch.WordTrace tailWord_1666615 prefixEnd_1666615 855774560993102094847883 := by
  unfold tailWord_1666615
  simp only [CollatzResearch.WordTrace]
  refine ⟨60786442857145965026145299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40524295238097310017430199 60786442857145965026145299)
  ·
    refine ⟨91179664285718947539217949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60786442857145965026145299 91179664285718947539217949)
    ·
      refine ⟨34192374107144605327206731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91179664285718947539217949 34192374107144605327206731)
      ·
        refine ⟨51288561160716907990810097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34192374107144605327206731 51288561160716907990810097)
        ·
          refine ⟨38466420870537680993107573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51288561160716907990810097 38466420870537680993107573)
          ·
            refine ⟨3606226956612907593103835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38466420870537680993107573 3606226956612907593103835)
            ·
              refine ⟨5409340434919361389655753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3606226956612907593103835 5409340434919361389655753)
              ·
                refine ⟨4057005326189521042241815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5409340434919361389655753 4057005326189521042241815)
                ·
                  refine ⟨6085507989284281563362723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4057005326189521042241815 6085507989284281563362723)
                  ·
                    refine ⟨9128261983926422345044085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6085507989284281563362723 9128261983926422345044085)
                    ·
                      refine ⟨855774560993102094847883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9128261983926422345044085 855774560993102094847883)
                      ·
                        rfl

theorem cell23_1666615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_1666615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666615 prefixEnd_1666615 := by exact prefixLift 1666615
  have htrace : WordTrace (prefixWord ++ tailWord_1666615) baseStart_1666615 baseEnd_1666615 := by
    simpa [prefixWord, tailWord_1666615, baseEnd_1666615] using wordTrace_append hprefix tailTrace_1666615
  have hstable : (prefixWord ++ tailWord_1666615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666615).length < 2 ^ (prefixWord ++ tailWord_1666615).sum := by decide
  have hdescent : baseEnd_1666615 < baseStart_1666615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666618 : List Nat := [3, 1, 1, 1, 3, 2, 2, 10]
def baseStart_1666618 : Nat := 118140960795 + 1666618 * 2 ^ 59
def prefixEnd_1666618 : Nat := 4983230072969 + 3 ^ 40 * 1666618 * 2
def baseEnd_1666618 : Nat := 31695411164261688263347

theorem tailTrace_1666618 : CollatzResearch.WordTrace tailWord_1666618 prefixEnd_1666618 31695411164261688263347 := by
  unfold tailWord_1666618
  simp only [CollatzResearch.WordTrace]
  refine ⟨15196638069033774134626127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40524368184090064359003005 15196638069033774134626127)
  ·
    refine ⟨22794957103550661201939191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15196638069033774134626127 22794957103550661201939191)
    ·
      refine ⟨34192435655325991802908787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22794957103550661201939191 34192435655325991802908787)
      ·
        refine ⟨51288653482988987704363181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34192435655325991802908787 51288653482988987704363181)
        ·
          refine ⟨19233245056120870389136193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51288653482988987704363181 19233245056120870389136193)
          ·
            refine ⟨14424933792090652791852145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19233245056120870389136193 14424933792090652791852145)
            ·
              refine ⟨10818700344067989593889109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14424933792090652791852145 10818700344067989593889109)
              ·
                refine ⟨31695411164261688263347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10818700344067989593889109 31695411164261688263347)
                ·
                  rfl

theorem cell23_1666618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 10].length) (baseStart_1666618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666618 prefixEnd_1666618 := by exact prefixLift 1666618
  have htrace : WordTrace (prefixWord ++ tailWord_1666618) baseStart_1666618 baseEnd_1666618 := by
    simpa [prefixWord, tailWord_1666618, baseEnd_1666618] using wordTrace_append hprefix tailTrace_1666618
  have hstable : (prefixWord ++ tailWord_1666618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666618).length < 2 ^ (prefixWord ++ tailWord_1666618).sum := by decide
  have hdescent : baseEnd_1666618 < baseStart_1666618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666625 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1666625 : Nat := 118140960795 + 1666625 * 2 ^ 59
def prefixEnd_1666625 : Nat := 4983230072969 + 3 ^ 40 * 1666625 * 2
def baseEnd_1666625 : Nat := 855779695799647055722837

theorem tailTrace_1666625 : CollatzResearch.WordTrace tailWord_1666625 prefixEnd_1666625 855779695799647055722837 := by
  unfold tailWord_1666625
  simp only [CollatzResearch.WordTrace]
  refine ⟨60786807587109736734009329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40524538391406491156006219 60786807587109736734009329)
  ·
    refine ⟨45590105690332302550506997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60786807587109736734009329 45590105690332302550506997)
    ·
      refine ⟨4274072408468653364110031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45590105690332302550506997 4274072408468653364110031)
      ·
        refine ⟨6411108612702980046165047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4274072408468653364110031 6411108612702980046165047)
        ·
          refine ⟨9616662919054470069247571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6411108612702980046165047 9616662919054470069247571)
          ·
            refine ⟨14424994378581705103871357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9616662919054470069247571 14424994378581705103871357)
            ·
              refine ⟨5409372891968139413951759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14424994378581705103871357 5409372891968139413951759)
              ·
                refine ⟨8114059337952209120927639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5409372891968139413951759 8114059337952209120927639)
                ·
                  refine ⟨12171089006928313681391459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8114059337952209120927639 12171089006928313681391459)
                  ·
                    refine ⟨18256633510392470522087189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12171089006928313681391459 18256633510392470522087189)
                    ·
                      refine ⟨855779695799647055722837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18256633510392470522087189 855779695799647055722837)
                      ·
                        rfl

theorem cell23_1666625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1666625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666625 prefixEnd_1666625 := by exact prefixLift 1666625
  have htrace : WordTrace (prefixWord ++ tailWord_1666625) baseStart_1666625 baseEnd_1666625 := by
    simpa [prefixWord, tailWord_1666625, baseEnd_1666625] using wordTrace_append hprefix tailTrace_1666625
  have hstable : (prefixWord ++ tailWord_1666625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666625).length < 2 ^ (prefixWord ++ tailWord_1666625).sum := by decide
  have hdescent : baseEnd_1666625 < baseStart_1666625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666645 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 3, 3, 3]
def baseStart_1666645 : Nat := 118140960795 + 1666645 * 2 ^ 59
def prefixEnd_1666645 : Nat := 4983230072969 + 3 ^ 40 * 1666645 * 2
def baseEnd_1666645 : Nat := 855789965412736977472745

theorem tailTrace_1666645 : CollatzResearch.WordTrace tailWord_1666645 prefixEnd_1666645 855789965412736977472745 := by
  unfold tailWord_1666645
  simp only [CollatzResearch.WordTrace]
  refine ⟨60787537047037280149737389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40525024698024853433158259 60787537047037280149737389)
  ·
    refine ⟨22795326392638980056151521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60787537047037280149737389 22795326392638980056151521)
    ·
      refine ⟨17096494794479235042113641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22795326392638980056151521 17096494794479235042113641)
      ·
        refine ⟨12822371095859426281585231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17096494794479235042113641 12822371095859426281585231)
        ·
          refine ⟨19233556643789139422377847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12822371095859426281585231 19233556643789139422377847)
          ·
            refine ⟨28850334965683709133566771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19233556643789139422377847 28850334965683709133566771)
            ·
              refine ⟨43275502448525563700350157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28850334965683709133566771 43275502448525563700350157)
              ·
                refine ⟨16228313418197086387631309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43275502448525563700350157 16228313418197086387631309)
                ·
                  refine ⟨6085617531823907395361741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16228313418197086387631309 6085617531823907395361741)
                  ·
                    refine ⟨2282106574433965273260653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6085617531823907395361741 2282106574433965273260653)
                    ·
                      refine ⟨855789965412736977472745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2282106574433965273260653 855789965412736977472745)
                      ·
                        rfl

theorem cell23_1666645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_1666645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666645 prefixEnd_1666645 := by exact prefixLift 1666645
  have htrace : WordTrace (prefixWord ++ tailWord_1666645) baseStart_1666645 baseEnd_1666645 := by
    simpa [prefixWord, tailWord_1666645, baseEnd_1666645] using wordTrace_append hprefix tailTrace_1666645
  have hstable : (prefixWord ++ tailWord_1666645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666645).length < 2 ^ (prefixWord ++ tailWord_1666645).sum := by decide
  have hdescent : baseEnd_1666645 < baseStart_1666645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666648 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 1, 9]
def baseStart_1666648 : Nat := 118140960795 + 1666648 * 2 ^ 59
def prefixEnd_1666648 : Nat := 4983230072969 + 3 ^ 40 * 1666648 * 2
def baseEnd_1666648 : Nat := 285263835284900155245077

theorem tailTrace_1666648 : CollatzResearch.WordTrace tailWord_1666648 prefixEnd_1666648 285263835284900155245077 := by
  unfold tailWord_1666648
  simp only [CollatzResearch.WordTrace]
  refine ⟨30393823233013205831048299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40525097644017607774731065 30393823233013205831048299)
  ·
    refine ⟨45590734849519808746572449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30393823233013205831048299 45590734849519808746572449)
    ·
      refine ⟨34193051137139856559929337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45590734849519808746572449 34193051137139856559929337)
      ·
        refine ⟨25644788352854892419947003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34193051137139856559929337 25644788352854892419947003)
        ·
          refine ⟨38467182529282338629920505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25644788352854892419947003 38467182529282338629920505)
          ·
            refine ⟨28850386896961753972440379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38467182529282338629920505 28850386896961753972440379)
            ·
              refine ⟨43275580345442630958660569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28850386896961753972440379 43275580345442630958660569)
              ·
                refine ⟨32456685259081973218995427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43275580345442630958660569 32456685259081973218995427)
                ·
                  refine ⟨48685027888622959828493141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32456685259081973218995427 48685027888622959828493141)
                  ·
                    refine ⟨285263835284900155245077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 48685027888622959828493141 285263835284900155245077)
                    ·
                      rfl

theorem cell23_1666648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_1666648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666648 prefixEnd_1666648 := by exact prefixLift 1666648
  have htrace : WordTrace (prefixWord ++ tailWord_1666648) baseStart_1666648 baseEnd_1666648 := by
    simpa [prefixWord, tailWord_1666648, baseEnd_1666648] using wordTrace_append hprefix tailTrace_1666648
  have hstable : (prefixWord ++ tailWord_1666648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666648).length < 2 ^ (prefixWord ++ tailWord_1666648).sum := by decide
  have hdescent : baseEnd_1666648 < baseStart_1666648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666689 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 3, 3, 2]
def baseStart_1666689 : Nat := 118140960795 + 1666689 * 2 ^ 59
def prefixEnd_1666689 : Nat := 4983230072969 + 3 ^ 40 * 1666689 * 2
def baseEnd_1666689 : Nat := 855812558561534805322543

theorem tailTrace_1666689 : CollatzResearch.WordTrace tailWord_1666689 prefixEnd_1666689 855812558561534805322543 := by
  unfold tailWord_1666689
  simp only [CollatzResearch.WordTrace]
  refine ⟨60789141858877875664339121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40526094572585250442892747 60789141858877875664339121)
  ·
    refine ⟨45591856394158406748254341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60789141858877875664339121 45591856394158406748254341)
    ·
      refine ⟨8548473073904701265297689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45591856394158406748254341 8548473073904701265297689)
      ·
        refine ⟨6411354805428525948973267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8548473073904701265297689 6411354805428525948973267)
        ·
          refine ⟨9617032208142788923459901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6411354805428525948973267 9617032208142788923459901)
          ·
            refine ⟨3606387078053545846297463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9617032208142788923459901 3606387078053545846297463)
            ·
              refine ⟨5409580617080318769446195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3606387078053545846297463 5409580617080318769446195)
              ·
                refine ⟨8114370925620478154169293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5409580617080318769446195 8114370925620478154169293)
                ·
                  refine ⟨3042889097107679307813485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8114370925620478154169293 3042889097107679307813485)
                  ·
                    refine ⟨1141083411415379740430057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3042889097107679307813485 1141083411415379740430057)
                    ·
                      refine ⟨855812558561534805322543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1141083411415379740430057 855812558561534805322543)
                      ·
                        rfl

theorem cell23_1666689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_1666689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666689 prefixEnd_1666689 := by exact prefixLift 1666689
  have htrace : WordTrace (prefixWord ++ tailWord_1666689) baseStart_1666689 baseEnd_1666689 := by
    simpa [prefixWord, tailWord_1666689, baseEnd_1666689] using wordTrace_append hprefix tailTrace_1666689
  have hstable : (prefixWord ++ tailWord_1666689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666689).length < 2 ^ (prefixWord ++ tailWord_1666689).sum := by decide
  have hdescent : baseEnd_1666689 < baseStart_1666689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666792 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_1666792 : Nat := 118140960795 + 1666792 * 2 ^ 59
def prefixEnd_1666792 : Nat := 4983230072969 + 3 ^ 40 * 1666792 * 2
def baseEnd_1666792 : Nat := 855865447068947902334569

theorem tailTrace_1666792 : CollatzResearch.WordTrace tailWord_1666792 prefixEnd_1666792 855865447068947902334569 := by
  unfold tailWord_1666792
  simp only [CollatzResearch.WordTrace]
  refine ⟨30396449288752362127669315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40528599051669816170225753 30396449288752362127669315)
  ·
    refine ⟨45594673933128543191503973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30396449288752362127669315 45594673933128543191503973)
    ·
      refine ⟨8549001362461601848406995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45594673933128543191503973 8549001362461601848406995)
      ·
        refine ⟨12823502043692402772610493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8549001362461601848406995 12823502043692402772610493)
        ·
          refine ⟨4808813266384651039728935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12823502043692402772610493 4808813266384651039728935)
          ·
            refine ⟨7213219899576976559593403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4808813266384651039728935 7213219899576976559593403)
            ·
              refine ⟨10819829849365464839390105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7213219899576976559593403 10819829849365464839390105)
              ·
                refine ⟨8114872387024098629542579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10819829849365464839390105 8114872387024098629542579)
                ·
                  refine ⟨12172308580536147944313869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8114872387024098629542579 12172308580536147944313869)
                  ·
                    refine ⟨4564615717701055479117701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12172308580536147944313869 4564615717701055479117701)
                    ·
                      refine ⟨855865447068947902334569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4564615717701055479117701 855865447068947902334569)
                      ·
                        rfl

theorem cell23_1666792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_1666792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666792 prefixEnd_1666792 := by exact prefixLift 1666792
  have htrace : WordTrace (prefixWord ++ tailWord_1666792) baseStart_1666792 baseEnd_1666792 := by
    simpa [prefixWord, tailWord_1666792, baseEnd_1666792] using wordTrace_append hprefix tailTrace_1666792
  have hstable : (prefixWord ++ tailWord_1666792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666792).length < 2 ^ (prefixWord ++ tailWord_1666792).sum := by decide
  have hdescent : baseEnd_1666792 < baseStart_1666792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666812 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 1, 4, 3]
def baseStart_1666812 : Nat := 118140960795 + 1666812 * 2 ^ 59
def prefixEnd_1666812 : Nat := 4983230072969 + 3 ^ 40 * 1666812 * 2
def baseEnd_1666812 : Nat := 855875716682037824084477

theorem tailTrace_1666812 : CollatzResearch.WordTrace tailWord_1666812 prefixEnd_1666812 855875716682037824084477 := by
  unfold tailWord_1666812
  simp only [CollatzResearch.WordTrace]
  refine ⟨30396814018716133835533345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40529085358288178447377793 30396814018716133835533345)
  ·
    refine ⟨22797610514037100376650009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30396814018716133835533345 22797610514037100376650009)
    ·
      refine ⟨17098207885527825282487507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22797610514037100376650009 17098207885527825282487507)
      ·
        refine ⟨25647311828291737923731261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17098207885527825282487507 25647311828291737923731261)
        ·
          refine ⟨9617741935609401721399223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25647311828291737923731261 9617741935609401721399223)
          ·
            refine ⟨14426612903414102582098835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9617741935609401721399223 14426612903414102582098835)
            ·
              refine ⟨21639919355121153873148253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14426612903414102582098835 21639919355121153873148253)
              ·
                refine ⟨8114969758170432702430595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21639919355121153873148253 8114969758170432702430595)
                ·
                  refine ⟨12172454637255649053645893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8114969758170432702430595 12172454637255649053645893)
                  ·
                    refine ⟨2282335244485434197558605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12172454637255649053645893 2282335244485434197558605)
                    ·
                      refine ⟨855875716682037824084477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2282335244485434197558605 855875716682037824084477)
                      ·
                        rfl

theorem cell23_1666812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_1666812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666812 prefixEnd_1666812 := by exact prefixLift 1666812
  have htrace : WordTrace (prefixWord ++ tailWord_1666812) baseStart_1666812 baseEnd_1666812 := by
    simpa [prefixWord, tailWord_1666812, baseEnd_1666812] using wordTrace_append hprefix tailTrace_1666812
  have hstable : (prefixWord ++ tailWord_1666812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666812).length < 2 ^ (prefixWord ++ tailWord_1666812).sum := by decide
  have hdescent : baseEnd_1666812 < baseStart_1666812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666815 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 8]
def baseStart_1666815 : Nat := 118140960795 + 1666815 * 2 ^ 59
def prefixEnd_1666815 : Nat := 4983230072969 + 3 ^ 40 * 1666815 * 2
def baseEnd_1666815 : Nat := 95097473013777923594107

theorem tailTrace_1666815 : CollatzResearch.WordTrace tailWord_1666815 prefixEnd_1666815 95097473013777923594107 := by
  unfold tailWord_1666815
  simp only [CollatzResearch.WordTrace]
  refine ⟨60793737456421399183425899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40529158304280932788950599 60793737456421399183425899)
  ·
    refine ⟨91190606184632098775138849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60793737456421399183425899 91190606184632098775138849)
    ·
      refine ⟨68392954638474074081354137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91190606184632098775138849 68392954638474074081354137)
      ·
        refine ⟨51294715978855555561015603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68392954638474074081354137 51294715978855555561015603)
        ·
          refine ⟨76942073968283333341523405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51294715978855555561015603 76942073968283333341523405)
          ·
            refine ⟨28853277738106250003071277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76942073968283333341523405 28853277738106250003071277)
            ·
              refine ⟨10819979151789843751151729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28853277738106250003071277 10819979151789843751151729)
              ·
                refine ⟨8114984363842382813363797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10819979151789843751151729 8114984363842382813363797)
                ·
                  refine ⟨95097473013777923594107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8114984363842382813363797 95097473013777923594107)
                  ·
                    rfl

theorem cell23_1666815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 8].length) (baseStart_1666815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666815 prefixEnd_1666815 := by exact prefixLift 1666815
  have htrace : WordTrace (prefixWord ++ tailWord_1666815) baseStart_1666815 baseEnd_1666815 := by
    simpa [prefixWord, tailWord_1666815, baseEnd_1666815] using wordTrace_append hprefix tailTrace_1666815
  have hstable : (prefixWord ++ tailWord_1666815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666815).length < 2 ^ (prefixWord ++ tailWord_1666815).sum := by decide
  have hdescent : baseEnd_1666815 < baseStart_1666815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666835 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 6]
def baseStart_1666835 : Nat := 118140960795 + 1666835 * 2 ^ 59
def prefixEnd_1666835 : Nat := 4983230072969 + 3 ^ 40 * 1666835 * 2
def baseEnd_1666835 : Nat := 855887526737091234096871

theorem tailTrace_1666835 : CollatzResearch.WordTrace tailWord_1666835 prefixEnd_1666835 855887526737091234096871 := by
  unfold tailWord_1666835
  simp only [CollatzResearch.WordTrace]
  refine ⟨60794466916348942599153959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40529644610899295066102639 60794466916348942599153959)
  ·
    refine ⟨91191700374523413898730939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60794466916348942599153959 91191700374523413898730939)
    ·
      refine ⟨136787550561785120848096409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91191700374523413898730939 136787550561785120848096409)
      ·
        refine ⟨102590662921338840636072307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136787550561785120848096409 102590662921338840636072307)
        ·
          refine ⟨153885994382008260954108461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102590662921338840636072307 153885994382008260954108461)
          ·
            refine ⟨57707247893253097857790673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153885994382008260954108461 57707247893253097857790673)
            ·
              refine ⟨43280435919939823393343005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57707247893253097857790673 43280435919939823393343005)
              ·
                refine ⟨16230163469977433772503627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43280435919939823393343005 16230163469977433772503627)
                ·
                  refine ⟨24345245204966150658755441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16230163469977433772503627 24345245204966150658755441)
                  ·
                    refine ⟨18258933903724612994066581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24345245204966150658755441 18258933903724612994066581)
                    ·
                      refine ⟨855887526737091234096871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18258933903724612994066581 855887526737091234096871)
                      ·
                        rfl

theorem cell23_1666835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_1666835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666835 prefixEnd_1666835 := by exact prefixLift 1666835
  have htrace : WordTrace (prefixWord ++ tailWord_1666835) baseStart_1666835 baseEnd_1666835 := by
    simpa [prefixWord, tailWord_1666835, baseEnd_1666835] using wordTrace_append hprefix tailTrace_1666835
  have hstable : (prefixWord ++ tailWord_1666835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666835).length < 2 ^ (prefixWord ++ tailWord_1666835).sum := by decide
  have hdescent : baseEnd_1666835 < baseStart_1666835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666849 : List Nat := [1, 2, 3, 2, 1, 3, 4, 1, 6]
def baseStart_1666849 : Nat := 118140960795 + 1666849 * 2 ^ 59
def prefixEnd_1666849 : Nat := 4983230072969 + 3 ^ 40 * 1666849 * 2
def baseEnd_1666849 : Nat := 95099412829583797702423

theorem tailTrace_1666849 : CollatzResearch.WordTrace tailWord_1666849 prefixEnd_1666849 95099412829583797702423 := by
  unfold tailWord_1666849
  simp only [CollatzResearch.WordTrace]
  refine ⟨60794977538298222990163601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40529985025532148660109067 60794977538298222990163601)
  ·
    refine ⟨45596233153723667242622701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60794977538298222990163601 45596233153723667242622701)
    ·
      refine ⟨17098587432646375215983513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45596233153723667242622701 17098587432646375215983513)
      ·
        refine ⟨12823940574484781411987635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17098587432646375215983513 12823940574484781411987635)
        ·
          refine ⟨19235910861727172117981453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12823940574484781411987635 19235910861727172117981453)
          ·
            refine ⟨7213466573147689544243045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19235910861727172117981453 7213466573147689544243045)
            ·
              refine ⟨1352524982465191789545571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7213466573147689544243045 1352524982465191789545571)
              ·
                refine ⟨2028787473697787684318357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1352524982465191789545571 2028787473697787684318357)
                ·
                  refine ⟨95099412829583797702423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2028787473697787684318357 95099412829583797702423)
                  ·
                    rfl

theorem cell23_1666849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 6].length) (baseStart_1666849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666849 prefixEnd_1666849 := by exact prefixLift 1666849
  have htrace : WordTrace (prefixWord ++ tailWord_1666849) baseStart_1666849 baseEnd_1666849 := by
    simpa [prefixWord, tailWord_1666849, baseEnd_1666849] using wordTrace_append hprefix tailTrace_1666849
  have hstable : (prefixWord ++ tailWord_1666849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666849).length < 2 ^ (prefixWord ++ tailWord_1666849).sum := by decide
  have hdescent : baseEnd_1666849 < baseStart_1666849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666919 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_1666919 : Nat := 118140960795 + 1666919 * 2 ^ 59
def prefixEnd_1666919 : Nat := 4983230072969 + 3 ^ 40 * 1666919 * 2
def baseEnd_1666919 : Nat := 855930659112068905446485

theorem tailTrace_1666919 : CollatzResearch.WordTrace tailWord_1666919 prefixEnd_1666919 855930659112068905446485 := by
  unfold tailWord_1666919
  simp only [CollatzResearch.WordTrace]
  refine ⟨60797530648044624945211811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40531687098696416630141207 60797530648044624945211811)
  ·
    refine ⟨91196295972066937417817717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60797530648044624945211811 91196295972066937417817717)
    ·
      refine ⟨8549652747381275382920411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91196295972066937417817717 8549652747381275382920411)
      ·
        refine ⟨12824479121071913074380617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8549652747381275382920411 12824479121071913074380617)
        ·
          refine ⟨9618359340803934805785463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12824479121071913074380617 9618359340803934805785463)
          ·
            refine ⟨14427539011205902208678195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9618359340803934805785463 14427539011205902208678195)
            ·
              refine ⟨21641308516808853313017293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14427539011205902208678195 21641308516808853313017293)
              ·
                refine ⟨8115490693803319992381485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21641308516808853313017293 8115490693803319992381485)
                ·
                  refine ⟨3043309010176244997143057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8115490693803319992381485 3043309010176244997143057)
                  ·
                    refine ⟨2282481757632183747857293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3043309010176244997143057 2282481757632183747857293)
                    ·
                      refine ⟨855930659112068905446485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2282481757632183747857293 855930659112068905446485)
                      ·
                        rfl

theorem cell23_1666919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_1666919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666919 prefixEnd_1666919 := by exact prefixLift 1666919
  have htrace : WordTrace (prefixWord ++ tailWord_1666919) baseStart_1666919 baseEnd_1666919 := by
    simpa [prefixWord, tailWord_1666919, baseEnd_1666919] using wordTrace_append hprefix tailTrace_1666919
  have hstable : (prefixWord ++ tailWord_1666919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666919).length < 2 ^ (prefixWord ++ tailWord_1666919).sum := by decide
  have hdescent : baseEnd_1666919 < baseStart_1666919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666990 : List Nat := [4, 1, 5, 1, 2, 1, 9]
def baseStart_1666990 : Nat := 118140960795 + 1666990 * 2 ^ 59
def prefixEnd_1666990 : Nat := 4983230072969 + 3 ^ 40 * 1666990 * 2
def baseEnd_1666990 : Nat := 10567495262204174415539

theorem tailTrace_1666990 : CollatzResearch.WordTrace tailWord_1666990 prefixEnd_1666990 10567495262204174415539 := by
  unfold tailWord_1666990
  simp only [CollatzResearch.WordTrace]
  refine ⟨7600015028848425508880803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40533413487191602714030949 7600015028848425508880803)
  ·
    refine ⟨11400022543272638263321205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7600015028848425508880803 11400022543272638263321205)
    ·
      refine ⟨1068752113431809837186363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11400022543272638263321205 1068752113431809837186363)
      ·
        refine ⟨1603128170147714755779545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1068752113431809837186363 1603128170147714755779545)
        ·
          refine ⟨1202346127610786066834659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1603128170147714755779545 1202346127610786066834659)
          ·
            refine ⟨1803519191416179100251989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202346127610786066834659 1803519191416179100251989)
            ·
              refine ⟨10567495262204174415539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1803519191416179100251989 10567495262204174415539)
              ·
                rfl

theorem cell23_1666990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 9].length) (baseStart_1666990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666990 prefixEnd_1666990 := by exact prefixLift 1666990
  have htrace : WordTrace (prefixWord ++ tailWord_1666990) baseStart_1666990 baseEnd_1666990 := by
    simpa [prefixWord, tailWord_1666990, baseEnd_1666990] using wordTrace_append hprefix tailTrace_1666990
  have hstable : (prefixWord ++ tailWord_1666990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666990).length < 2 ^ (prefixWord ++ tailWord_1666990).sum := by decide
  have hdescent : baseEnd_1666990 < baseStart_1666990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1666993 : List Nat := [1, 2, 2, 4, 2, 1, 2, 3, 1, 3, 2]
def baseStart_1666993 : Nat := 118140960795 + 1666993 * 2 ^ 59
def prefixEnd_1666993 : Nat := 4983230072969 + 3 ^ 40 * 1666993 * 2
def baseEnd_1666993 : Nat := 855968656680501615921145

theorem tailTrace_1666993 : CollatzResearch.WordTrace tailWord_1666993 prefixEnd_1666993 855968656680501615921145 := by
  unfold tailWord_1666993
  simp only [CollatzResearch.WordTrace]
  refine ⟨60800229649776535583405633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40533486433184357055603755 60800229649776535583405633)
  ·
    refine ⟨45600172237332401687554225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60800229649776535583405633 45600172237332401687554225)
    ·
      refine ⟨34200129177999301265665669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45600172237332401687554225 34200129177999301265665669)
      ·
        refine ⟨6412524220874868987312313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34200129177999301265665669 6412524220874868987312313)
        ·
          refine ⟨4809393165656151740484235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6412524220874868987312313 4809393165656151740484235)
          ·
            refine ⟨7214089748484227610726353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4809393165656151740484235 7214089748484227610726353)
            ·
              refine ⟨5410567311363170708044765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7214089748484227610726353 5410567311363170708044765)
              ·
                refine ⟨2028962741761189015516787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5410567311363170708044765 2028962741761189015516787)
                ·
                  refine ⟨3043444112641783523275181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2028962741761189015516787 3043444112641783523275181)
                  ·
                    refine ⟨1141291542240668821228193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3043444112641783523275181 1141291542240668821228193)
                    ·
                      refine ⟨855968656680501615921145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1141291542240668821228193 855968656680501615921145)
                      ·
                        rfl

theorem cell23_1666993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_1666993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1666993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1666993 prefixEnd_1666993 := by exact prefixLift 1666993
  have htrace : WordTrace (prefixWord ++ tailWord_1666993) baseStart_1666993 baseEnd_1666993 := by
    simpa [prefixWord, tailWord_1666993, baseEnd_1666993] using wordTrace_append hprefix tailTrace_1666993
  have hstable : (prefixWord ++ tailWord_1666993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1666993).length < 2 ^ (prefixWord ++ tailWord_1666993).sum := by decide
  have hdescent : baseEnd_1666993 < baseStart_1666993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1666993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667002 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6]
def baseStart_1667002 : Nat := 118140960795 + 1667002 * 2 ^ 59
def prefixEnd_1667002 : Nat := 4983230072969 + 3 ^ 40 * 1667002 * 2
def baseEnd_1667002 : Nat := 855973278006392080708603

theorem tailTrace_1667002 : CollatzResearch.WordTrace tailWord_1667002 prefixEnd_1667002 855973278006392080708603 := by
  unfold tailWord_1667002
  simp only [CollatzResearch.WordTrace]
  refine ⟨15200139476685982530120815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40533705271162620080322173 15200139476685982530120815)
  ·
    refine ⟨22800209215028973795181223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15200139476685982530120815 22800209215028973795181223)
    ·
      refine ⟨34200313822543460692771835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22800209215028973795181223 34200313822543460692771835)
      ·
        refine ⟨51300470733815191039157753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34200313822543460692771835 51300470733815191039157753)
        ·
          refine ⟨38475353050361393279368315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51300470733815191039157753 38475353050361393279368315)
          ·
            refine ⟨57713029575542089919052473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38475353050361393279368315 57713029575542089919052473)
            ·
              refine ⟨43284772181656567439289355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57713029575542089919052473 43284772181656567439289355)
              ·
                refine ⟨64927158272484851158934033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43284772181656567439289355 64927158272484851158934033)
                ·
                  refine ⟨48695368704363638369200525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64927158272484851158934033 48695368704363638369200525)
                  ·
                    refine ⟨18260763264136364388450197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48695368704363638369200525 18260763264136364388450197)
                    ·
                      refine ⟨855973278006392080708603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18260763264136364388450197 855973278006392080708603)
                      ·
                        rfl

theorem cell23_1667002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_1667002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667002 prefixEnd_1667002 := by exact prefixLift 1667002
  have htrace : WordTrace (prefixWord ++ tailWord_1667002) baseStart_1667002 baseEnd_1667002 := by
    simpa [prefixWord, tailWord_1667002, baseEnd_1667002] using wordTrace_append hprefix tailTrace_1667002
  have hstable : (prefixWord ++ tailWord_1667002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667002).length < 2 ^ (prefixWord ++ tailWord_1667002).sum := by decide
  have hdescent : baseEnd_1667002 < baseStart_1667002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1667023 : List Nat := [1, 1, 2, 1, 1, 5, 3, 3, 2, 2, 2]
def baseStart_1667023 : Nat := 118140960795 + 1667023 * 2 ^ 59
def prefixEnd_1667023 : Nat := 4983230072969 + 3 ^ 40 * 1667023 * 2
def baseEnd_1667023 : Nat := 855984061100136498546007

theorem tailTrace_1667023 : CollatzResearch.WordTrace tailWord_1667023 prefixEnd_1667023 855984061100136498546007 := by
  unfold tailWord_1667023
  simp only [CollatzResearch.WordTrace]
  refine ⟨60801323839667850706997723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40534215893111900471331815 60801323839667850706997723)
  ·
    refine ⟨91201985759501776060496585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60801323839667850706997723 91201985759501776060496585)
    ·
      refine ⟨68401489319626332045372439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91201985759501776060496585 68401489319626332045372439)
      ·
        refine ⟨102602233979439498068058659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68401489319626332045372439 102602233979439498068058659)
        ·
          refine ⟨153903350969159247102087989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102602233979439498068058659 153903350969159247102087989)
          ·
            refine ⟨14428439153358679415820749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 153903350969159247102087989 14428439153358679415820749)
            ·
              refine ⟨5410664682509504780932781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14428439153358679415820749 5410664682509504780932781)
              ·
                refine ⟨2028999255941064292849793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5410664682509504780932781 2028999255941064292849793)
                ·
                  refine ⟨1521749441955798219637345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2028999255941064292849793 1521749441955798219637345)
                  ·
                    refine ⟨1141312081466848664728009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1521749441955798219637345 1141312081466848664728009)
                    ·
                      refine ⟨855984061100136498546007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1141312081466848664728009 855984061100136498546007)
                      ·
                        rfl

theorem cell23_1667023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 2, 2].length) (baseStart_1667023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1667023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1667023 prefixEnd_1667023 := by exact prefixLift 1667023
  have htrace : WordTrace (prefixWord ++ tailWord_1667023) baseStart_1667023 baseEnd_1667023 := by
    simpa [prefixWord, tailWord_1667023, baseEnd_1667023] using wordTrace_append hprefix tailTrace_1667023
  have hstable : (prefixWord ++ tailWord_1667023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1667023).length < 2 ^ (prefixWord ++ tailWord_1667023).sum := by decide
  have hdescent : baseEnd_1667023 < baseStart_1667023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1667023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
