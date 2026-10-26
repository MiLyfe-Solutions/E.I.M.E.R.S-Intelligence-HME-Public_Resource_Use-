import V185TrunkScan20Chunk034

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_213748 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 5]
def baseStart_213748 : Nat := 118140960795 + 213748 * 2 ^ 59
def prefixEnd_213748 : Nat := 4983230072969 + 3 ^ 40 * 213748 * 2
def baseEnd_213748 : Nat := 97560411499853283259553

theorem tailTrace_213748 : CollatzResearch.WordTrace tailWord_213748 prefixEnd_213748 97560411499853283259553 := by
  unfold tailWord_213748
  simp only [CollatzResearch.WordTrace]
  refine ⟨3898015014817488048588949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5197353353089984064785265 3898015014817488048588949)
  ·
    refine ⟨182719453819569752277607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3898015014817488048588949 182719453819569752277607)
    ·
      refine ⟨274079180729354628416411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182719453819569752277607 274079180729354628416411)
      ·
        refine ⟨411118771094031942624617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274079180729354628416411 411118771094031942624617)
        ·
          refine ⟨308339078320523956968463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411118771094031942624617 308339078320523956968463)
          ·
            refine ⟨462508617480785935452695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308339078320523956968463 462508617480785935452695)
            ·
              refine ⟨693762926221178903179043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462508617480785935452695 693762926221178903179043)
              ·
                refine ⟨1040644389331768354768565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693762926221178903179043 1040644389331768354768565)
                ·
                  refine ⟨97560411499853283259553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1040644389331768354768565 97560411499853283259553)
                  ·
                    rfl

theorem cell20_213748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_213748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213748 prefixEnd_213748 := by exact prefixLift 213748
  have htrace : WordTrace (prefixWord ++ tailWord_213748) baseStart_213748 baseEnd_213748 := by
    simpa [prefixWord, tailWord_213748, baseEnd_213748] using wordTrace_append hprefix tailTrace_213748
  have hstable : (prefixWord ++ tailWord_213748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213748).length < 2 ^ (prefixWord ++ tailWord_213748).sum := by decide
  have hdescent : baseEnd_213748 < baseStart_213748 := by decide
  rcases family_descends (prefixWord ++ tailWord_213748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213789 : List Nat := [1, 4, 2, 4, 2, 1, 1, 3, 2]
def baseStart_213789 : Nat := 118140960795 + 213789 * 2 ^ 59
def prefixEnd_213789 : Nat := 4983230072969 + 3 ^ 40 * 213789 * 2
def baseEnd_213789 : Nat := 97579125017039362892719

theorem tailTrace_213789 : CollatzResearch.WordTrace tailWord_213789 prefixEnd_213789 97579125017039362892719 := by
  unfold tailWord_213789
  simp only [CollatzResearch.WordTrace]
  refine ⟨7797525422486440099420421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5198350281657626732946947 7797525422486440099420421)
  ·
    refine ⟨1462036016716207518641329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7797525422486440099420421 1462036016716207518641329)
    ·
      refine ⟨1096527012537155638980997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1462036016716207518641329 1096527012537155638980997)
      ·
        refine ⟨205598814850716682308937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1096527012537155638980997 205598814850716682308937)
        ·
          refine ⟨154199111138037511731703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205598814850716682308937 154199111138037511731703)
          ·
            refine ⟨231298666707056267597555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154199111138037511731703 231298666707056267597555)
            ·
              refine ⟨346948000060584401396333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231298666707056267597555 346948000060584401396333)
              ·
                refine ⟨130105500022719150523625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346948000060584401396333 130105500022719150523625)
                ·
                  refine ⟨97579125017039362892719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130105500022719150523625 97579125017039362892719)
                  ·
                    rfl

theorem cell20_213789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_213789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213789 prefixEnd_213789 := by exact prefixLift 213789
  have htrace : WordTrace (prefixWord ++ tailWord_213789) baseStart_213789 baseEnd_213789 := by
    simpa [prefixWord, tailWord_213789, baseEnd_213789] using wordTrace_append hprefix tailTrace_213789
  have hstable : (prefixWord ++ tailWord_213789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213789).length < 2 ^ (prefixWord ++ tailWord_213789).sum := by decide
  have hdescent : baseEnd_213789 < baseStart_213789 := by decide
  rcases family_descends (prefixWord ++ tailWord_213789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213811 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 5]
def baseStart_213811 : Nat := 118140960795 + 213811 * 2 ^ 59
def prefixEnd_213811 : Nat := 4983230072969 + 3 ^ 40 * 213811 * 2
def baseEnd_213811 : Nat := 97589166416505064159295

theorem tailTrace_213811 : CollatzResearch.WordTrace tailWord_213811 prefixEnd_213811 97589166416505064159295 := by
  unfold tailWord_213811
  simp only [CollatzResearch.WordTrace]
  refine ⟨7798327828406737856721287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5198885218937825237814191 7798327828406737856721287)
  ·
    refine ⟨11697491742610106785081931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7798327828406737856721287 11697491742610106785081931)
    ·
      refine ⟨17546237613915160177622897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11697491742610106785081931 17546237613915160177622897)
      ·
        refine ⟨13159678210436370133217173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17546237613915160177622897 13159678210436370133217173)
        ·
          refine ⟨616859916114204849994555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13159678210436370133217173 616859916114204849994555)
          ·
            refine ⟨925289874171307274991833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616859916114204849994555 925289874171307274991833)
            ·
              refine ⟨693967405628480456243875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 925289874171307274991833 693967405628480456243875)
              ·
                refine ⟨1040951108442720684365813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693967405628480456243875 1040951108442720684365813)
                ·
                  refine ⟨97589166416505064159295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1040951108442720684365813 97589166416505064159295)
                  ·
                    rfl

theorem cell20_213811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_213811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213811 prefixEnd_213811 := by exact prefixLift 213811
  have htrace : WordTrace (prefixWord ++ tailWord_213811) baseStart_213811 baseEnd_213811 := by
    simpa [prefixWord, tailWord_213811, baseEnd_213811] using wordTrace_append hprefix tailTrace_213811
  have hstable : (prefixWord ++ tailWord_213811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213811).length < 2 ^ (prefixWord ++ tailWord_213811).sum := by decide
  have hdescent : baseEnd_213811 < baseStart_213811 := by decide
  rcases family_descends (prefixWord ++ tailWord_213811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213821 : List Nat := [1, 4, 1, 4, 2, 1, 2, 5]
def baseStart_213821 : Nat := 118140960795 + 213821 * 2 ^ 59
def prefixEnd_213821 : Nat := 4983230072969 + 3 ^ 40 * 213821 * 2
def baseEnd_213821 : Nat := 32531243562996491275307

theorem tailTrace_213821 : CollatzResearch.WordTrace tailWord_213821 prefixEnd_213821 32531243562996491275307 := by
  unfold tailWord_213821
  simp only [CollatzResearch.WordTrace]
  refine ⟨7798692558370509564585317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5199128372247006376390211 7798692558370509564585317)
  ·
    refine ⟨1462254854694470543359747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7798692558370509564585317 1462254854694470543359747)
    ·
      refine ⟨2193382282041705815039621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1462254854694470543359747 2193382282041705815039621)
      ·
        refine ⟨411259177882819840319929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2193382282041705815039621 411259177882819840319929)
        ·
          refine ⟨308444383412114880239947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411259177882819840319929 308444383412114880239947)
          ·
            refine ⟨462666575118172320359921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308444383412114880239947 462666575118172320359921)
            ·
              refine ⟨346999931338629240269941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462666575118172320359921 346999931338629240269941)
              ·
                refine ⟨32531243562996491275307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 346999931338629240269941 32531243562996491275307)
                ·
                  rfl

theorem cell20_213821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 5].length) (baseStart_213821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213821 prefixEnd_213821 := by exact prefixLift 213821
  have htrace : WordTrace (prefixWord ++ tailWord_213821) baseStart_213821 baseEnd_213821 := by
    simpa [prefixWord, tailWord_213821, baseEnd_213821] using wordTrace_append hprefix tailTrace_213821
  have hstable : (prefixWord ++ tailWord_213821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213821).length < 2 ^ (prefixWord ++ tailWord_213821).sum := by decide
  have hdescent : baseEnd_213821 < baseStart_213821 := by decide
  rcases family_descends (prefixWord ++ tailWord_213821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213863 : List Nat := [1, 1, 5, 1, 2, 10]
def baseStart_213863 : Nat := 118140960795 + 213863 * 2 ^ 59
def prefixEnd_213863 : Nat := 4983230072969 + 3 ^ 40 * 213863 * 2
def baseEnd_213863 : Nat := 3615292616052740534287

theorem tailTrace_213863 : CollatzResearch.WordTrace tailWord_213863 prefixEnd_213863 3615292616052740534287 := by
  unfold tailWord_213863
  simp only [CollatzResearch.WordTrace]
  refine ⟨7800224424218350737614243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5200149616145567158409495 7800224424218350737614243)
  ·
    refine ⟨11700336636327526106421365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7800224424218350737614243 11700336636327526106421365)
    ·
      refine ⟨1096906559655705572477003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11700336636327526106421365 1096906559655705572477003)
      ·
        refine ⟨1645359839483558358715505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1096906559655705572477003 1645359839483558358715505)
        ·
          refine ⟨1234019879612668769036629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1645359839483558358715505 1234019879612668769036629)
          ·
            refine ⟨3615292616052740534287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1234019879612668769036629 3615292616052740534287)
            ·
              rfl

theorem cell20_213863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 10].length) (baseStart_213863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213863 prefixEnd_213863 := by exact prefixLift 213863
  have htrace : WordTrace (prefixWord ++ tailWord_213863) baseStart_213863 baseEnd_213863 := by
    simpa [prefixWord, tailWord_213863, baseEnd_213863] using wordTrace_append hprefix tailTrace_213863
  have hstable : (prefixWord ++ tailWord_213863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213863).length < 2 ^ (prefixWord ++ tailWord_213863).sum := by decide
  have hdescent : baseEnd_213863 < baseStart_213863 := by decide
  rcases family_descends (prefixWord ++ tailWord_213863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213887 : List Nat := [1, 1, 2, 2, 1, 1, 6, 3, 3]
def baseStart_213887 : Nat := 118140960795 + 213887 * 2 ^ 59
def prefixEnd_213887 : Nat := 4983230072969 + 3 ^ 40 * 213887 * 2
def baseEnd_213887 : Nat := 97623854887386577625651

theorem tailTrace_213887 : CollatzResearch.WordTrace tailWord_213887 prefixEnd_213887 97623854887386577625651 := by
  unfold tailWord_213887
  simp only [CollatzResearch.WordTrace]
  refine ⟨7801099776131402836487915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5200733184087601890991943 7801099776131402836487915)
  ·
    refine ⟨11701649664197104254731873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7801099776131402836487915 11701649664197104254731873)
    ·
      refine ⟨8776237248147828191048905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11701649664197104254731873 8776237248147828191048905)
      ·
        refine ⟨6582177936110871143286679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8776237248147828191048905 6582177936110871143286679)
        ·
          refine ⟨9873266904166306714930019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6582177936110871143286679 9873266904166306714930019)
          ·
            refine ⟨14809900356249460072395029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9873266904166306714930019 14809900356249460072395029)
            ·
              refine ⟨694214079199193440893517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14809900356249460072395029 694214079199193440893517)
              ·
                refine ⟨260330279699697540335069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 694214079199193440893517 260330279699697540335069)
                ·
                  refine ⟨97623854887386577625651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260330279699697540335069 97623854887386577625651)
                  ·
                    rfl

theorem cell20_213887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 3].length) (baseStart_213887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213887 prefixEnd_213887 := by exact prefixLift 213887
  have htrace : WordTrace (prefixWord ++ tailWord_213887) baseStart_213887 baseEnd_213887 := by
    simpa [prefixWord, tailWord_213887, baseEnd_213887] using wordTrace_append hprefix tailTrace_213887
  have hstable : (prefixWord ++ tailWord_213887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213887).length < 2 ^ (prefixWord ++ tailWord_213887).sum := by decide
  have hdescent : baseEnd_213887 < baseStart_213887 := by decide
  rcases family_descends (prefixWord ++ tailWord_213887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213921 : List Nat := [1, 2, 3, 4, 1, 3, 1, 2, 3]
def baseStart_213921 : Nat := 118140960795 + 213921 * 2 ^ 59
def prefixEnd_213921 : Nat := 4983230072969 + 3 ^ 40 * 213921 * 2
def baseEnd_213921 : Nat := 97639373413833570492179

theorem tailTrace_213921 : CollatzResearch.WordTrace tailWord_213921 prefixEnd_213921 97639373413833570492179 := by
  unfold tailWord_213921
  simp only [CollatzResearch.WordTrace]
  refine ⟨7802339858008226643225617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5201559905338817762150411 7802339858008226643225617)
  ·
    refine ⟨5851754893506169982419213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7802339858008226643225617 5851754893506169982419213)
    ·
      refine ⟨2194408085064813743407205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5851754893506169982419213 2194408085064813743407205)
      ·
        refine ⟨411451515949652576888851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2194408085064813743407205 411451515949652576888851)
        ·
          refine ⟨617177273924478865333277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411451515949652576888851 617177273924478865333277)
          ·
            refine ⟨231441477721679574499979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 617177273924478865333277 231441477721679574499979)
            ·
              refine ⟨347162216582519361749969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231441477721679574499979 347162216582519361749969)
              ·
                refine ⟨260371662436889521312477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347162216582519361749969 260371662436889521312477)
                ·
                  refine ⟨97639373413833570492179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260371662436889521312477 97639373413833570492179)
                  ·
                    rfl

theorem cell20_213921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 3].length) (baseStart_213921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213921 prefixEnd_213921 := by exact prefixLift 213921
  have htrace : WordTrace (prefixWord ++ tailWord_213921) baseStart_213921 baseEnd_213921 := by
    simpa [prefixWord, tailWord_213921, baseEnd_213921] using wordTrace_append hprefix tailTrace_213921
  have hstable : (prefixWord ++ tailWord_213921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213921).length < 2 ^ (prefixWord ++ tailWord_213921).sum := by decide
  have hdescent : baseEnd_213921 < baseStart_213921 := by decide
  rcases family_descends (prefixWord ++ tailWord_213921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213966 : List Nat := [4, 1, 1, 1, 2, 3, 3, 3, 2]
def baseStart_213966 : Nat := 118140960795 + 213966 * 2 ^ 59
def prefixEnd_213966 : Nat := 4983230072969 + 3 ^ 40 * 213966 * 2
def baseEnd_213966 : Nat := 97659912640013413991995

theorem tailTrace_213966 : CollatzResearch.WordTrace tailWord_213966 prefixEnd_213966 97659912640013413991995 := by
  unfold tailWord_213966
  simp only [CollatzResearch.WordTrace]
  refine ⟨975497642855649916076719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5202654095230132885742501 975497642855649916076719)
  ·
    refine ⟨1463246464283474874115079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 975497642855649916076719 1463246464283474874115079)
    ·
      refine ⟨2194869696425212311172619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1463246464283474874115079 2194869696425212311172619)
      ·
        refine ⟨3292304544637818466758929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2194869696425212311172619 3292304544637818466758929)
        ·
          refine ⟨2469228408478363850069197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3292304544637818466758929 2469228408478363850069197)
          ·
            refine ⟨925960653179386443775949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2469228408478363850069197 925960653179386443775949)
            ·
              refine ⟨347235244942269916415981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 925960653179386443775949 347235244942269916415981)
              ·
                refine ⟨130213216853351218655993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347235244942269916415981 130213216853351218655993)
                ·
                  refine ⟨97659912640013413991995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130213216853351218655993 97659912640013413991995)
                  ·
                    rfl

theorem cell20_213966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_213966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213966 prefixEnd_213966 := by exact prefixLift 213966
  have htrace : WordTrace (prefixWord ++ tailWord_213966) baseStart_213966 baseEnd_213966 := by
    simpa [prefixWord, tailWord_213966, baseEnd_213966] using wordTrace_append hprefix tailTrace_213966
  have hstable : (prefixWord ++ tailWord_213966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213966).length < 2 ^ (prefixWord ++ tailWord_213966).sum := by decide
  have hdescent : baseEnd_213966 < baseStart_213966 := by decide
  rcases family_descends (prefixWord ++ tailWord_213966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213973 : List Nat := [1, 3, 2, 3, 4, 1, 6]
def baseStart_213973 : Nat := 118140960795 + 213973 * 2 ^ 59
def prefixEnd_213973 : Nat := 4983230072969 + 3 ^ 40 * 213973 * 2
def baseEnd_213973 : Nat := 10851456403416944528737

theorem tailTrace_213973 : CollatzResearch.WordTrace tailWord_213973 prefixEnd_213973 10851456403416944528737 := by
  unfold tailWord_213973
  simp only [CollatzResearch.WordTrace]
  refine ⟨7804236453819839524118573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5202824302546559682745715 7804236453819839524118573)
  ·
    refine ⟨2926588670182439821544465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7804236453819839524118573 2926588670182439821544465)
    ·
      refine ⟨2194941502636829866158349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2926588670182439821544465 2194941502636829866158349)
      ·
        refine ⟨823103063488811199809381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2194941502636829866158349 823103063488811199809381)
        ·
          refine ⟨154331824404152099964259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 823103063488811199809381 154331824404152099964259)
          ·
            refine ⟨231497736606228149946389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154331824404152099964259 231497736606228149946389)
            ·
              refine ⟨10851456403416944528737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 231497736606228149946389 10851456403416944528737)
              ·
                rfl

theorem cell20_213973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 6].length) (baseStart_213973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213973 prefixEnd_213973 := by exact prefixLift 213973
  have htrace : WordTrace (prefixWord ++ tailWord_213973) baseStart_213973 baseEnd_213973 := by
    simpa [prefixWord, tailWord_213973, baseEnd_213973] using wordTrace_append hprefix tailTrace_213973
  have hstable : (prefixWord ++ tailWord_213973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213973).length < 2 ^ (prefixWord ++ tailWord_213973).sum := by decide
  have hdescent : baseEnd_213973 < baseStart_213973 := by decide
  rcases family_descends (prefixWord ++ tailWord_213973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213977 : List Nat := [1, 2, 1, 2, 5, 1, 8]
def baseStart_213977 : Nat := 118140960795 + 213977 * 2 ^ 59
def prefixEnd_213977 : Nat := 4983230072969 + 3 ^ 40 * 213977 * 2
def baseEnd_213977 : Nat := 10851659259971807180587

theorem tailTrace_213977 : CollatzResearch.WordTrace tailWord_213977 prefixEnd_213977 10851659259971807180587 := by
  unfold tailWord_213977
  simp only [CollatzResearch.WordTrace]
  refine ⟨7804382345805348207264185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5202921563870232138176123 7804382345805348207264185)
  ·
    refine ⟨5853286759354011155448139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7804382345805348207264185 5853286759354011155448139)
    ·
      refine ⟨8779930139031016733172209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5853286759354011155448139 8779930139031016733172209)
      ·
        refine ⟨6584947604273262549879157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8779930139031016733172209 6584947604273262549879157)
        ·
          refine ⟨617338837900618364051171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6584947604273262549879157 617338837900618364051171)
          ·
            refine ⟨926008256850927546076757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617338837900618364051171 926008256850927546076757)
            ·
              refine ⟨10851659259971807180587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 926008256850927546076757 10851659259971807180587)
              ·
                rfl

theorem cell20_213977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 8].length) (baseStart_213977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213977 prefixEnd_213977 := by exact prefixLift 213977
  have htrace : WordTrace (prefixWord ++ tailWord_213977) baseStart_213977 baseEnd_213977 := by
    simpa [prefixWord, tailWord_213977, baseEnd_213977] using wordTrace_append hprefix tailTrace_213977
  have hstable : (prefixWord ++ tailWord_213977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213977).length < 2 ^ (prefixWord ++ tailWord_213977).sum := by decide
  have hdescent : baseEnd_213977 < baseStart_213977 := by decide
  rcases family_descends (prefixWord ++ tailWord_213977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213983 : List Nat := [1, 1, 2, 3, 5, 1, 3, 2, 2]
def baseStart_213983 : Nat := 118140960795 + 213983 * 2 ^ 59
def prefixEnd_213983 : Nat := 4983230072969 + 3 ^ 40 * 213983 * 2
def baseEnd_213983 : Nat := 97667671903236910425259

theorem tailTrace_213983 : CollatzResearch.WordTrace tailWord_213983 prefixEnd_213983 97667671903236910425259 := by
  unfold tailWord_213983
  simp only [CollatzResearch.WordTrace]
  refine ⟨7804601183783611231982603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5203067455855740821321735 7804601183783611231982603)
  ·
    refine ⟨11706901775675416847973905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7804601183783611231982603 11706901775675416847973905)
    ·
      refine ⟨8780176331756562635980429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11706901775675416847973905 8780176331756562635980429)
      ·
        refine ⟨3292566124408710988492661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8780176331756562635980429 3292566124408710988492661)
        ·
          refine ⟨308678074163316655171187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3292566124408710988492661 308678074163316655171187)
          ·
            refine ⟨463017111244974982756781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308678074163316655171187 463017111244974982756781)
            ·
              refine ⟨173631416716865618533793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 463017111244974982756781 173631416716865618533793)
              ·
                refine ⟨130223562537649213900345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173631416716865618533793 130223562537649213900345)
                ·
                  refine ⟨97667671903236910425259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130223562537649213900345 97667671903236910425259)
                  ·
                    rfl

theorem cell20_213983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 2].length) (baseStart_213983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213983 prefixEnd_213983 := by exact prefixLift 213983
  have htrace : WordTrace (prefixWord ++ tailWord_213983) baseStart_213983 baseEnd_213983 := by
    simpa [prefixWord, tailWord_213983, baseEnd_213983] using wordTrace_append hprefix tailTrace_213983
  have hstable : (prefixWord ++ tailWord_213983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213983).length < 2 ^ (prefixWord ++ tailWord_213983).sum := by decide
  have hdescent : baseEnd_213983 < baseStart_213983 := by decide
  rcases family_descends (prefixWord ++ tailWord_213983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213994 : List Nat := [3, 1, 3, 1, 2, 3, 2, 5]
def baseStart_213994 : Nat := 118140960795 + 213994 * 2 ^ 59
def prefixEnd_213994 : Nat := 4983230072969 + 3 ^ 40 * 213994 * 2
def baseEnd_213994 : Nat := 32557564200989920352849

theorem tailTrace_213994 : CollatzResearch.WordTrace tailWord_213994 prefixEnd_213994 32557564200989920352849 := by
  unfold tailWord_213994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1951250596685940027658259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5203334924495840073755357 1951250596685940027658259)
  ·
    refine ⟨2926875895028910041487389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1951250596685940027658259 2926875895028910041487389)
    ·
      refine ⟨1097578460635841265557771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2926875895028910041487389 1097578460635841265557771)
      ·
        refine ⟨1646367690953761898336657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1097578460635841265557771 1646367690953761898336657)
        ·
          refine ⟨1234775768215321423752493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1646367690953761898336657 1234775768215321423752493)
          ·
            refine ⟨463040913080745533907185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1234775768215321423752493 463040913080745533907185)
            ·
              refine ⟨347280684810559150430389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463040913080745533907185 347280684810559150430389)
              ·
                refine ⟨32557564200989920352849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 347280684810559150430389 32557564200989920352849)
                ·
                  rfl

theorem cell20_213994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_213994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_213994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_213994 prefixEnd_213994 := by exact prefixLift 213994
  have htrace : WordTrace (prefixWord ++ tailWord_213994) baseStart_213994 baseEnd_213994 := by
    simpa [prefixWord, tailWord_213994, baseEnd_213994] using wordTrace_append hprefix tailTrace_213994
  have hstable : (prefixWord ++ tailWord_213994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213994).length < 2 ^ (prefixWord ++ tailWord_213994).sum := by decide
  have hdescent : baseEnd_213994 < baseStart_213994 := by decide
  rcases family_descends (prefixWord ++ tailWord_213994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214034 : List Nat := [3, 2, 5, 1, 1, 2, 2, 2, 2]
def baseStart_214034 : Nat := 118140960795 + 214034 * 2 ^ 59
def prefixEnd_214034 : Nat := 4983230072969 + 3 ^ 40 * 214034 * 2
def baseEnd_214034 : Nat := 97690949692907399725051

theorem tailTrace_214034 : CollatzResearch.WordTrace tailWord_214034 prefixEnd_214034 97690949692907399725051 := by
  unfold tailWord_214034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1951615326649711735522289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5204307537732564628059437 1951615326649711735522289)
  ·
    refine ⟨1463711494987283801641717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1951615326649711735522289 1463711494987283801641717)
    ·
      refine ⟨137222952655057856403911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1463711494987283801641717 137222952655057856403911)
      ·
        refine ⟨205834428982586784605867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137222952655057856403911 205834428982586784605867)
        ·
          refine ⟨308751643473880176908801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205834428982586784605867 308751643473880176908801)
          ·
            refine ⟨231563732605410132681601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308751643473880176908801 231563732605410132681601)
            ·
              refine ⟨173672799454057599511201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231563732605410132681601 173672799454057599511201)
              ·
                refine ⟨130254599590543199633401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173672799454057599511201 130254599590543199633401)
                ·
                  refine ⟨97690949692907399725051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130254599590543199633401 97690949692907399725051)
                  ·
                    rfl

theorem cell20_214034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_214034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214034 prefixEnd_214034 := by exact prefixLift 214034
  have htrace : WordTrace (prefixWord ++ tailWord_214034) baseStart_214034 baseEnd_214034 := by
    simpa [prefixWord, tailWord_214034, baseEnd_214034] using wordTrace_append hprefix tailTrace_214034
  have hstable : (prefixWord ++ tailWord_214034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214034).length < 2 ^ (prefixWord ++ tailWord_214034).sum := by decide
  have hdescent : baseEnd_214034 < baseStart_214034 := by decide
  rcases family_descends (prefixWord ++ tailWord_214034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214101 : List Nat := [1, 3, 2, 2, 1, 2, 1, 6, 2]
def baseStart_214101 : Nat := 118140960795 + 214101 * 2 ^ 59
def prefixEnd_214101 : Nat := 4983230072969 + 3 ^ 40 * 214101 * 2
def baseEnd_214101 : Nat := 97721530318552944491443

theorem tailTrace_214101 : CollatzResearch.WordTrace tailWord_214101 prefixEnd_214101 97721530318552944491443 := by
  unfold tailWord_214101
  simp only [CollatzResearch.WordTrace]
  refine ⟨7808904997356117384778157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5205936664904078256518771 7808904997356117384778157)
  ·
    refine ⟨2928339374008544019291809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7808904997356117384778157 2928339374008544019291809)
    ·
      refine ⟨2196254530506408014468857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2928339374008544019291809 2196254530506408014468857)
      ·
        refine ⟨1647190897879806010851643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2196254530506408014468857 1647190897879806010851643)
        ·
          refine ⟨2470786346819709016277465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1647190897879806010851643 2470786346819709016277465)
          ·
            refine ⟨1853089760114781762208099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2470786346819709016277465 1853089760114781762208099)
            ·
              refine ⟨2779634640172172643312149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1853089760114781762208099 2779634640172172643312149)
              ·
                refine ⟨130295373758070592655257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2779634640172172643312149 130295373758070592655257)
                ·
                  refine ⟨97721530318552944491443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130295373758070592655257 97721530318552944491443)
                  ·
                    rfl

theorem cell20_214101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_214101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214101 prefixEnd_214101 := by exact prefixLift 214101
  have htrace : WordTrace (prefixWord ++ tailWord_214101) baseStart_214101 baseEnd_214101 := by
    simpa [prefixWord, tailWord_214101, baseEnd_214101] using wordTrace_append hprefix tailTrace_214101
  have hstable : (prefixWord ++ tailWord_214101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214101).length < 2 ^ (prefixWord ++ tailWord_214101).sum := by decide
  have hdescent : baseEnd_214101 < baseStart_214101 := by decide
  rcases family_descends (prefixWord ++ tailWord_214101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214125 : List Nat := [1, 5, 1, 1, 2, 4, 2, 4]
def baseStart_214125 : Nat := 118140960795 + 214125 * 2 ^ 59
def prefixEnd_214125 : Nat := 4983230072969 + 3 ^ 40 * 214125 * 2
def baseEnd_214125 : Nat := 32577494857505175897115

theorem tailTrace_214125 : CollatzResearch.WordTrace tailWord_214125 prefixEnd_214125 32577494857505175897115 := by
  unfold tailWord_214125
  simp only [CollatzResearch.WordTrace]
  refine ⟨7809780349269169483651829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5206520232846112989101219 7809780349269169483651829)
  ·
    refine ⟨732166907743984639092359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7809780349269169483651829 732166907743984639092359)
    ·
      refine ⟨1098250361615976958638539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 732166907743984639092359 1098250361615976958638539)
      ·
        refine ⟨1647375542423965437957809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1098250361615976958638539 1647375542423965437957809)
        ·
          refine ⟨1235531656817974078468357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1647375542423965437957809 1235531656817974078468357)
          ·
            refine ⟨231662185653370139712817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1235531656817974078468357 231662185653370139712817)
            ·
              refine ⟨173746639240027604784613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231662185653370139712817 173746639240027604784613)
              ·
                refine ⟨32577494857505175897115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173746639240027604784613 32577494857505175897115)
                ·
                  rfl

theorem cell20_214125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 4].length) (baseStart_214125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214125 prefixEnd_214125 := by exact prefixLift 214125
  have htrace : WordTrace (prefixWord ++ tailWord_214125) baseStart_214125 baseEnd_214125 := by
    simpa [prefixWord, tailWord_214125, baseEnd_214125] using wordTrace_append hprefix tailTrace_214125
  have hstable : (prefixWord ++ tailWord_214125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214125).length < 2 ^ (prefixWord ++ tailWord_214125).sum := by decide
  have hdescent : baseEnd_214125 < baseStart_214125 := by decide
  rcases family_descends (prefixWord ++ tailWord_214125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214136 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 5]
def baseStart_214136 : Nat := 118140960795 + 214136 * 2 ^ 59
def prefixEnd_214136 : Nat := 4983230072969 + 3 ^ 40 * 214136 * 2
def baseEnd_214136 : Nat := 97737505272248378324633

theorem tailTrace_214136 : CollatzResearch.WordTrace tailWord_214136 prefixEnd_214136 97737505272248378324633 := by
  unfold tailWord_214136
  simp only [CollatzResearch.WordTrace]
  refine ⟨3905090776114659181151131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5206787701486212241534841 3905090776114659181151131)
  ·
    refine ⟨5857636164171988771726697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3905090776114659181151131 5857636164171988771726697)
    ·
      refine ⟨4393227123128991578795023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5857636164171988771726697 4393227123128991578795023)
      ·
        refine ⟨6589840684693487368192535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4393227123128991578795023 6589840684693487368192535)
        ·
          refine ⟨9884761027040231052288803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6589840684693487368192535 9884761027040231052288803)
          ·
            refine ⟨14827141540560346578433205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9884761027040231052288803 14827141540560346578433205)
            ·
              refine ⟨1390044519427532491728113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14827141540560346578433205 1390044519427532491728113)
              ·
                refine ⟨1042533389570649368796085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1390044519427532491728113 1042533389570649368796085)
                ·
                  refine ⟨97737505272248378324633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1042533389570649368796085 97737505272248378324633)
                  ·
                    rfl

theorem cell20_214136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_214136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214136 prefixEnd_214136 := by exact prefixLift 214136
  have htrace : WordTrace (prefixWord ++ tailWord_214136) baseStart_214136 baseEnd_214136 := by
    simpa [prefixWord, tailWord_214136, baseEnd_214136] using wordTrace_append hprefix tailTrace_214136
  have hstable : (prefixWord ++ tailWord_214136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214136).length < 2 ^ (prefixWord ++ tailWord_214136).sum := by decide
  have hdescent : baseEnd_214136 < baseStart_214136 := by decide
  rcases family_descends (prefixWord ++ tailWord_214136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214167 : List Nat := [1, 1, 3, 3, 3, 1, 1, 7]
def baseStart_214167 : Nat := 118140960795 + 214167 * 2 ^ 59
def prefixEnd_214167 : Nat := 4983230072969 + 3 ^ 40 * 214167 * 2
def baseEnd_214167 : Nat := 32583884838983349430391

theorem tailTrace_214167 : CollatzResearch.WordTrace tailWord_214167 prefixEnd_214167 32583884838983349430391 := by
  unfold tailWord_214167
  simp only [CollatzResearch.WordTrace]
  refine ⟨7811312215117010656680755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5207541476744673771120503 7811312215117010656680755)
  ·
    refine ⟨11716968322675515985021133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7811312215117010656680755 11716968322675515985021133)
    ·
      refine ⟨4393863121003318494382925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11716968322675515985021133 4393863121003318494382925)
      ·
        refine ⟨1647698670376244435393597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4393863121003318494382925 1647698670376244435393597)
        ·
          refine ⟨617887001391091663272599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1647698670376244435393597 617887001391091663272599)
          ·
            refine ⟨926830502086637494908899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617887001391091663272599 926830502086637494908899)
            ·
              refine ⟨1390245753129956242363349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926830502086637494908899 1390245753129956242363349)
              ·
                refine ⟨32583884838983349430391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1390245753129956242363349 32583884838983349430391)
                ·
                  rfl

theorem cell20_214167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 7].length) (baseStart_214167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214167 prefixEnd_214167 := by exact prefixLift 214167
  have htrace : WordTrace (prefixWord ++ tailWord_214167) baseStart_214167 baseEnd_214167 := by
    simpa [prefixWord, tailWord_214167, baseEnd_214167] using wordTrace_append hprefix tailTrace_214167
  have hstable : (prefixWord ++ tailWord_214167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214167).length < 2 ^ (prefixWord ++ tailWord_214167).sum := by decide
  have hdescent : baseEnd_214167 < baseStart_214167 := by decide
  rcases family_descends (prefixWord ++ tailWord_214167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214170 : List Nat := [3, 1, 1, 5, 1, 2, 1, 3, 3]
def baseStart_214170 : Nat := 118140960795 + 214170 * 2 ^ 59
def prefixEnd_214170 : Nat := 4983230072969 + 3 ^ 40 * 214170 * 2
def baseEnd_214170 : Nat := 97753023798695371191161

theorem tailTrace_214170 : CollatzResearch.WordTrace tailWord_214170 prefixEnd_214170 97753023798695371191161 := by
  unfold tailWord_214170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1952855408526535542259991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5207614422737428112693309 1952855408526535542259991)
  ·
    refine ⟨2929283112789803313389987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1952855408526535542259991 2929283112789803313389987)
    ·
      refine ⟨4393924669184704970084981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2929283112789803313389987 4393924669184704970084981)
      ·
        refine ⟨411930437736066090945467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4393924669184704970084981 411930437736066090945467)
        ·
          refine ⟨617895656604099136418201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411930437736066090945467 617895656604099136418201)
          ·
            refine ⟨463421742453074352313651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 617895656604099136418201 463421742453074352313651)
            ·
              refine ⟨695132613679611528470477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463421742453074352313651 695132613679611528470477)
              ·
                refine ⟨260674730129854323176429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 695132613679611528470477 260674730129854323176429)
                ·
                  refine ⟨97753023798695371191161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260674730129854323176429 97753023798695371191161)
                  ·
                    rfl

theorem cell20_214170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_214170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214170 prefixEnd_214170 := by exact prefixLift 214170
  have htrace : WordTrace (prefixWord ++ tailWord_214170) baseStart_214170 baseEnd_214170 := by
    simpa [prefixWord, tailWord_214170, baseEnd_214170] using wordTrace_append hprefix tailTrace_214170
  have hstable : (prefixWord ++ tailWord_214170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214170).length < 2 ^ (prefixWord ++ tailWord_214170).sum := by decide
  have hdescent : baseEnd_214170 < baseStart_214170 := by decide
  rcases family_descends (prefixWord ++ tailWord_214170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214208 : List Nat := [2, 1, 1, 2, 6, 1, 2, 2, 3]
def baseStart_214208 : Nat := 118140960795 + 214208 * 2 ^ 59
def prefixEnd_214208 : Nat := 4983230072969 + 3 ^ 40 * 214208 * 2
def baseEnd_214208 : Nat := 97770368034136127924339

theorem tailTrace_214208 : CollatzResearch.WordTrace tailWord_214208 prefixEnd_214208 97770368034136127924339 := by
  unfold tailWord_214208
  simp only [CollatzResearch.WordTrace]
  refine ⟨3906403803984237329461639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5208538405312316439282185 3906403803984237329461639)
  ·
    refine ⟨5859605705976355994192459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3906403803984237329461639 5859605705976355994192459)
    ·
      refine ⟨8789408558964533991288689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5859605705976355994192459 8789408558964533991288689)
      ·
        refine ⟨6592056419223400493466517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8789408558964533991288689 6592056419223400493466517)
        ·
          refine ⟨309002644651096898131243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6592056419223400493466517 309002644651096898131243)
          ·
            refine ⟨463503966976645347196865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309002644651096898131243 463503966976645347196865)
            ·
              refine ⟨347627975232484010397649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 463503966976645347196865 347627975232484010397649)
              ·
                refine ⟨260720981424363007798237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347627975232484010397649 260720981424363007798237)
                ·
                  refine ⟨97770368034136127924339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260720981424363007798237 97770368034136127924339)
                  ·
                    rfl

theorem cell20_214208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_214208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214208 prefixEnd_214208 := by exact prefixLift 214208
  have htrace : WordTrace (prefixWord ++ tailWord_214208) baseStart_214208 baseEnd_214208 := by
    simpa [prefixWord, tailWord_214208, baseEnd_214208] using wordTrace_append hprefix tailTrace_214208
  have hstable : (prefixWord ++ tailWord_214208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214208).length < 2 ^ (prefixWord ++ tailWord_214208).sum := by decide
  have hdescent : baseEnd_214208 < baseStart_214208 := by decide
  rcases family_descends (prefixWord ++ tailWord_214208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214214 : List Nat := [6, 1, 2, 2, 2, 1, 1, 5]
def baseStart_214214 : Nat := 118140960795 + 214214 * 2 ^ 59
def prefixEnd_214214 : Nat := 4983230072969 + 3 ^ 40 * 214214 * 2
def baseEnd_214214 : Nat := 32591035532542257908105

theorem tailTrace_214214 : CollatzResearch.WordTrace tailWord_214214 prefixEnd_214214 32591035532542257908105 := by
  unfold tailWord_214214
  simp only [CollatzResearch.WordTrace]
  refine ⟨244157076435835552613803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5208684297297825122427797 244157076435835552613803)
  ·
    refine ⟨366235614653753328920705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244157076435835552613803 366235614653753328920705)
    ·
      refine ⟨274676710990314996690529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366235614653753328920705 274676710990314996690529)
      ·
        refine ⟨206007533242736247517897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274676710990314996690529 206007533242736247517897)
        ·
          refine ⟨154505649932052185638423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206007533242736247517897 154505649932052185638423)
          ·
            refine ⟨231758474898078278457635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154505649932052185638423 231758474898078278457635)
            ·
              refine ⟨347637712347117417686453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231758474898078278457635 347637712347117417686453)
              ·
                refine ⟨32591035532542257908105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 347637712347117417686453 32591035532542257908105)
                ·
                  rfl

theorem cell20_214214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_214214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214214 prefixEnd_214214 := by exact prefixLift 214214
  have htrace : WordTrace (prefixWord ++ tailWord_214214) baseStart_214214 baseEnd_214214 := by
    simpa [prefixWord, tailWord_214214, baseEnd_214214] using wordTrace_append hprefix tailTrace_214214
  have hstable : (prefixWord ++ tailWord_214214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214214).length < 2 ^ (prefixWord ++ tailWord_214214).sum := by decide
  have hdescent : baseEnd_214214 < baseStart_214214 := by decide
  rcases family_descends (prefixWord ++ tailWord_214214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214257 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 8]
def baseStart_214257 : Nat := 118140960795 + 214257 * 2 ^ 59
def prefixEnd_214257 : Nat := 4983230072969 + 3 ^ 40 * 214257 * 2
def baseEnd_214257 : Nat := 97792732969309735290805

theorem tailTrace_214257 : CollatzResearch.WordTrace tailWord_214257 prefixEnd_214257 97792732969309735290805 := by
  unfold tailWord_214257
  simp only [CollatzResearch.WordTrace]
  refine ⟨7814594784790956027457025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5209729856527304018304683 7814594784790956027457025)
  ·
    refine ⟨5860946088593217020592769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7814594784790956027457025 5860946088593217020592769)
    ·
      refine ⟨4395709566444912765444577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5860946088593217020592769 4395709566444912765444577)
      ·
        refine ⟨3296782174833684574083433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4395709566444912765444577 3296782174833684574083433)
        ·
          refine ⟨2472586631125263430562575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3296782174833684574083433 2472586631125263430562575)
          ·
            refine ⟨3708879946687895145843863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472586631125263430562575 3708879946687895145843863)
            ·
              refine ⟨5563319920031842718765795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3708879946687895145843863 5563319920031842718765795)
              ·
                refine ⟨8344979880047764078148693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5563319920031842718765795 8344979880047764078148693)
                ·
                  refine ⟨97792732969309735290805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8344979880047764078148693 97792732969309735290805)
                  ·
                    rfl

theorem cell20_214257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_214257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214257 prefixEnd_214257 := by exact prefixLift 214257
  have htrace : WordTrace (prefixWord ++ tailWord_214257) baseStart_214257 baseEnd_214257 := by
    simpa [prefixWord, tailWord_214257, baseEnd_214257] using wordTrace_append hprefix tailTrace_214257
  have hstable : (prefixWord ++ tailWord_214257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214257).length < 2 ^ (prefixWord ++ tailWord_214257).sum := by decide
  have hdescent : baseEnd_214257 < baseStart_214257 := by decide
  rcases family_descends (prefixWord ++ tailWord_214257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214270 : List Nat := [4, 2, 2, 1, 1, 2, 2, 4, 2]
def baseStart_214270 : Nat := 118140960795 + 214270 * 2 ^ 59
def prefixEnd_214270 : Nat := 4983230072969 + 3 ^ 40 * 214270 * 2
def baseEnd_214270 : Nat := 97798666523539467857419

theorem tailTrace_214270 : CollatzResearch.WordTrace tailWord_214270 prefixEnd_214270 97798666523539467857419 := by
  unfold tailWord_214270
  simp only [CollatzResearch.WordTrace]
  refine ⟨976883616717982405960033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5210045955829239498453509 976883616717982405960033)
  ·
    refine ⟨732662712538486804470025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 976883616717982405960033 732662712538486804470025)
    ·
      refine ⟨549497034403865103352519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 732662712538486804470025 549497034403865103352519)
      ·
        refine ⟨824245551605797655028779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 549497034403865103352519 824245551605797655028779)
        ·
          refine ⟨1236368327408696482543169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824245551605797655028779 1236368327408696482543169)
          ·
            refine ⟨927276245556522361907377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1236368327408696482543169 927276245556522361907377)
            ·
              refine ⟨695457184167391771430533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 927276245556522361907377 695457184167391771430533)
              ·
                refine ⟨130398222031385957143225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 695457184167391771430533 130398222031385957143225)
                ·
                  refine ⟨97798666523539467857419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130398222031385957143225 97798666523539467857419)
                  ·
                    rfl

theorem cell20_214270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_214270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214270 prefixEnd_214270 := by exact prefixLift 214270
  have htrace : WordTrace (prefixWord ++ tailWord_214270) baseStart_214270 baseEnd_214270 := by
    simpa [prefixWord, tailWord_214270, baseEnd_214270] using wordTrace_append hprefix tailTrace_214270
  have hstable : (prefixWord ++ tailWord_214270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214270).length < 2 ^ (prefixWord ++ tailWord_214270).sum := by decide
  have hdescent : baseEnd_214270 < baseStart_214270 := by decide
  rcases family_descends (prefixWord ++ tailWord_214270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214284 : List Nat := [2, 2, 1, 2, 2, 4, 3, 1, 3]
def baseStart_214284 : Nat := 118140960795 + 214284 * 2 ^ 59
def prefixEnd_214284 : Nat := 4983230072969 + 3 ^ 40 * 214284 * 2
def baseEnd_214284 : Nat := 97805056505017641390695

theorem tailTrace_214284 : CollatzResearch.WordTrace tailWord_214284 prefixEnd_214284 97805056505017641390695 := by
  unfold tailWord_214284
  simp only [CollatzResearch.WordTrace]
  refine ⟨3907789777846569819344953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5210386370462093092459937 3907789777846569819344953)
  ·
    refine ⟨2930842333384927364508715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3907789777846569819344953 2930842333384927364508715)
    ·
      refine ⟨4396263500077391046763073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2930842333384927364508715 4396263500077391046763073)
      ·
        refine ⟨3297197625058043285072305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4396263500077391046763073 3297197625058043285072305)
        ·
          refine ⟨2472898218793532463804229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3297197625058043285072305 2472898218793532463804229)
          ·
            refine ⟨463668416023787336963293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2472898218793532463804229 463668416023787336963293)
            ·
              refine ⟨173875656008920251361235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 463668416023787336963293 173875656008920251361235)
              ·
                refine ⟨260813484013380377041853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173875656008920251361235 260813484013380377041853)
                ·
                  refine ⟨97805056505017641390695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260813484013380377041853 97805056505017641390695)
                  ·
                    rfl

theorem cell20_214284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_214284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214284 prefixEnd_214284 := by exact prefixLift 214284
  have htrace : WordTrace (prefixWord ++ tailWord_214284) baseStart_214284 baseEnd_214284 := by
    simpa [prefixWord, tailWord_214284, baseEnd_214284] using wordTrace_append hprefix tailTrace_214284
  have hstable : (prefixWord ++ tailWord_214284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214284).length < 2 ^ (prefixWord ++ tailWord_214284).sum := by decide
  have hdescent : baseEnd_214284 < baseStart_214284 := by decide
  rcases family_descends (prefixWord ++ tailWord_214284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214298 : List Nat := [3, 1, 1, 3, 3, 1, 4, 4]
def baseStart_214298 : Nat := 118140960795 + 214298 * 2 ^ 59
def prefixEnd_214298 : Nat := 4983230072969 + 3 ^ 40 * 214298 * 2
def baseEnd_214298 : Nat := 32603815495498604974657

theorem tailTrace_214298 : CollatzResearch.WordTrace tailWord_214298 prefixEnd_214298 32603815495498604974657 := by
  unfold tailWord_214298
  simp only [CollatzResearch.WordTrace]
  refine ⟨1954022544410605007424887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5210726785094946686466365 1954022544410605007424887)
  ·
    refine ⟨2931033816615907511137331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1954022544410605007424887 2931033816615907511137331)
    ·
      refine ⟨4396550724923861266705997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2931033816615907511137331 4396550724923861266705997)
      ·
        refine ⟨1648706521846447975014749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4396550724923861266705997 1648706521846447975014749)
        ·
          refine ⟨618264945692417990630531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1648706521846447975014749 618264945692417990630531)
          ·
            refine ⟨927397418538626985945797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618264945692417990630531 927397418538626985945797)
            ·
              refine ⟨173887015975992559864837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 927397418538626985945797 173887015975992559864837)
              ·
                refine ⟨32603815495498604974657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173887015975992559864837 32603815495498604974657)
                ·
                  rfl

theorem cell20_214298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_214298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214298 prefixEnd_214298 := by exact prefixLift 214298
  have htrace : WordTrace (prefixWord ++ tailWord_214298) baseStart_214298 baseEnd_214298 := by
    simpa [prefixWord, tailWord_214298, baseEnd_214298] using wordTrace_append hprefix tailTrace_214298
  have hstable : (prefixWord ++ tailWord_214298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214298).length < 2 ^ (prefixWord ++ tailWord_214298).sum := by decide
  have hdescent : baseEnd_214298 < baseStart_214298 := by decide
  rcases family_descends (prefixWord ++ tailWord_214298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214343 : List Nat := [1, 1, 4, 1, 2, 4, 1, 3, 3]
def baseStart_214343 : Nat := 118140960795 + 214343 * 2 ^ 59
def prefixEnd_214343 : Nat := 4983230072969 + 3 ^ 40 * 214343 * 2
def baseEnd_214343 : Nat := 97831985712675658423787

theorem tailTrace_214343 : CollatzResearch.WordTrace tailWord_214343 prefixEnd_214343 97831985712675658423787 := by
  unfold tailWord_214343
  simp only [CollatzResearch.WordTrace]
  refine ⟨7817731462479392715087683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5211820974986261810058455 7817731462479392715087683)
  ·
    refine ⟨11726597193719089072631525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7817731462479392715087683 11726597193719089072631525)
    ·
      refine ⟨2198736973822329201118411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11726597193719089072631525 2198736973822329201118411)
      ·
        refine ⟨3298105460733493801677617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2198736973822329201118411 3298105460733493801677617)
        ·
          refine ⟨2473579095550120351258213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3298105460733493801677617 2473579095550120351258213)
          ·
            refine ⟨463796080415647565860915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2473579095550120351258213 463796080415647565860915)
            ·
              refine ⟨695694120623471348791373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463796080415647565860915 695694120623471348791373)
              ·
                refine ⟨260885295233801755796765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 695694120623471348791373 260885295233801755796765)
                ·
                  refine ⟨97831985712675658423787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260885295233801755796765 97831985712675658423787)
                  ·
                    rfl

theorem cell20_214343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 3].length) (baseStart_214343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214343 prefixEnd_214343 := by exact prefixLift 214343
  have htrace : WordTrace (prefixWord ++ tailWord_214343) baseStart_214343 baseEnd_214343 := by
    simpa [prefixWord, tailWord_214343, baseEnd_214343] using wordTrace_append hprefix tailTrace_214343
  have hstable : (prefixWord ++ tailWord_214343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214343).length < 2 ^ (prefixWord ++ tailWord_214343).sum := by decide
  have hdescent : baseEnd_214343 < baseStart_214343 := by decide
  rcases family_descends (prefixWord ++ tailWord_214343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214357 : List Nat := [1, 3, 2, 2, 3, 1, 2, 6]
def baseStart_214357 : Nat := 118140960795 + 214357 * 2 ^ 59
def prefixEnd_214357 : Nat := 4983230072969 + 3 ^ 40 * 214357 * 2
def baseEnd_214357 : Nat := 32612791898051277319021

theorem tailTrace_214357 : CollatzResearch.WordTrace tailWord_214357 prefixEnd_214357 32612791898051277319021 := by
  unfold tailWord_214357
  simp only [CollatzResearch.WordTrace]
  refine ⟨7818242084428673106097325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5212161389619115404064883 7818242084428673106097325)
  ·
    refine ⟨2931840781660752414786497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7818242084428673106097325 2931840781660752414786497)
    ·
      refine ⟨2198880586245564311089873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2931840781660752414786497 2198880586245564311089873)
      ·
        refine ⟨1649160439684173233317405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2198880586245564311089873 1649160439684173233317405)
        ·
          refine ⟨618435164881564962494027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1649160439684173233317405 618435164881564962494027)
          ·
            refine ⟨927652747322347443741041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618435164881564962494027 927652747322347443741041)
            ·
              refine ⟨695739560491760582805781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 927652747322347443741041 695739560491760582805781)
              ·
                refine ⟨32612791898051277319021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 695739560491760582805781 32612791898051277319021)
                ·
                  rfl

theorem cell20_214357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 6].length) (baseStart_214357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214357 prefixEnd_214357 := by exact prefixLift 214357
  have htrace : WordTrace (prefixWord ++ tailWord_214357) baseStart_214357 baseEnd_214357 := by
    simpa [prefixWord, tailWord_214357, baseEnd_214357] using wordTrace_append hprefix tailTrace_214357
  have hstable : (prefixWord ++ tailWord_214357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214357).length < 2 ^ (prefixWord ++ tailWord_214357).sum := by decide
  have hdescent : baseEnd_214357 < baseStart_214357 := by decide
  rcases family_descends (prefixWord ++ tailWord_214357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214381 : List Nat := [1, 5, 1, 1, 1, 3, 1, 4, 3]
def baseStart_214381 : Nat := 118140960795 + 214381 * 2 ^ 59
def prefixEnd_214381 : Nat := 4983230072969 + 3 ^ 40 * 214381 * 2
def baseEnd_214381 : Nat := 97849329948116415156965

theorem tailTrace_214381 : CollatzResearch.WordTrace tailWord_214381 prefixEnd_214381 97849329948116415156965 := by
  unfold tailWord_214381
  simp only [CollatzResearch.WordTrace]
  refine ⟨7819117436341725204970997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5212744957561150136647331 7819117436341725204970997)
  ·
    refine ⟨733042259657036737966031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7819117436341725204970997 733042259657036737966031)
    ·
      refine ⟨1099563389485555106949047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 733042259657036737966031 1099563389485555106949047)
      ·
        refine ⟨1649345084228332660423571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1099563389485555106949047 1649345084228332660423571)
        ·
          refine ⟨2474017626342498990635357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1649345084228332660423571 2474017626342498990635357)
          ·
            refine ⟨927756609878437121488259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2474017626342498990635357 927756609878437121488259)
            ·
              refine ⟨1391634914817655682232389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927756609878437121488259 1391634914817655682232389)
              ·
                refine ⟨260931546528310440418573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1391634914817655682232389 260931546528310440418573)
                ·
                  refine ⟨97849329948116415156965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260931546528310440418573 97849329948116415156965)
                  ·
                    rfl

theorem cell20_214381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_214381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214381 prefixEnd_214381 := by exact prefixLift 214381
  have htrace : WordTrace (prefixWord ++ tailWord_214381) baseStart_214381 baseEnd_214381 := by
    simpa [prefixWord, tailWord_214381, baseEnd_214381] using wordTrace_append hprefix tailTrace_214381
  have hstable : (prefixWord ++ tailWord_214381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214381).length < 2 ^ (prefixWord ++ tailWord_214381).sum := by decide
  have hdescent : baseEnd_214381 < baseStart_214381 := by decide
  rcases family_descends (prefixWord ++ tailWord_214381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214478 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_214478 : Nat := 118140960795 + 214478 * 2 ^ 59
def prefixEnd_214478 : Nat := 4983230072969 + 3 ^ 40 * 214478 * 2
def baseEnd_214478 : Nat := 97893603391215188923235

theorem tailTrace_214478 : CollatzResearch.WordTrace tailWord_214478 prefixEnd_214478 97893603391215188923235 := by
  unfold tailWord_214478
  simp only [CollatzResearch.WordTrace]
  refine ⟨977831914623788846406511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5215103544660207180834725 977831914623788846406511)
  ·
    refine ⟨1466747871935683269609767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 977831914623788846406511 1466747871935683269609767)
    ·
      refine ⟨2200121807903524904414651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1466747871935683269609767 2200121807903524904414651)
      ·
        refine ⟨3300182711855287356621977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2200121807903524904414651 3300182711855287356621977)
        ·
          refine ⟨2475137033891465517466483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3300182711855287356621977 2475137033891465517466483)
          ·
            refine ⟨3712705550837198276199725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475137033891465517466483 3712705550837198276199725)
            ·
              refine ⟨1392264581563949353574897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3712705550837198276199725 1392264581563949353574897)
              ·
                refine ⟨1044198436172962015181173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1392264581563949353574897 1044198436172962015181173)
                ·
                  refine ⟨97893603391215188923235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1044198436172962015181173 97893603391215188923235)
                  ·
                    rfl

theorem cell20_214478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_214478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214478 prefixEnd_214478 := by exact prefixLift 214478
  have htrace : WordTrace (prefixWord ++ tailWord_214478) baseStart_214478 baseEnd_214478 := by
    simpa [prefixWord, tailWord_214478, baseEnd_214478] using wordTrace_append hprefix tailTrace_214478
  have hstable : (prefixWord ++ tailWord_214478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214478).length < 2 ^ (prefixWord ++ tailWord_214478).sum := by decide
  have hdescent : baseEnd_214478 < baseStart_214478 := by decide
  rcases family_descends (prefixWord ++ tailWord_214478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214512 : List Nat := [2, 1, 1, 1, 3, 6, 2, 1, 3]
def baseStart_214512 : Nat := 118140960795 + 214512 * 2 ^ 59
def prefixEnd_214512 : Nat := 4983230072969 + 3 ^ 40 * 214512 * 2
def baseEnd_214512 : Nat := 97909121917662181789763

theorem tailTrace_214512 : CollatzResearch.WordTrace tailWord_214512 prefixEnd_214512 97909121917662181789763 := by
  unfold tailWord_214512
  simp only [CollatzResearch.WordTrace]
  refine ⟨3911947699433567288994895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5215930265911423051993193 3911947699433567288994895)
  ·
    refine ⟨5867921549150350933492343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3911947699433567288994895 5867921549150350933492343)
    ·
      refine ⟨8801882323725526400238515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5867921549150350933492343 8801882323725526400238515)
      ·
        refine ⟨13202823485588289600357773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8801882323725526400238515 13202823485588289600357773)
        ·
          refine ⟨4951058807095608600134165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13202823485588289600357773 4951058807095608600134165)
          ·
            refine ⟨232080881582606653131289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4951058807095608600134165 232080881582606653131289)
            ·
              refine ⟨174060661186954989848467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232080881582606653131289 174060661186954989848467)
              ·
                refine ⟨261090991780432484772701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174060661186954989848467 261090991780432484772701)
                ·
                  refine ⟨97909121917662181789763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261090991780432484772701 97909121917662181789763)
                  ·
                    rfl

theorem cell20_214512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 3].length) (baseStart_214512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214512 prefixEnd_214512 := by exact prefixLift 214512
  have htrace : WordTrace (prefixWord ++ tailWord_214512) baseStart_214512 baseEnd_214512 := by
    simpa [prefixWord, tailWord_214512, baseEnd_214512] using wordTrace_append hprefix tailTrace_214512
  have hstable : (prefixWord ++ tailWord_214512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214512).length < 2 ^ (prefixWord ++ tailWord_214512).sum := by decide
  have hdescent : baseEnd_214512 < baseStart_214512 := by decide
  rcases family_descends (prefixWord ++ tailWord_214512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214557 : List Nat := [1, 4, 2, 2, 1, 1, 3, 4, 2]
def baseStart_214557 : Nat := 118140960795 + 214557 * 2 ^ 59
def prefixEnd_214557 : Nat := 4983230072969 + 3 ^ 40 * 214557 * 2
def baseEnd_214557 : Nat := 97929661143842025289579

theorem tailTrace_214557 : CollatzResearch.WordTrace tailWord_214557 prefixEnd_214557 97929661143842025289579 := by
  unfold tailWord_214557
  simp only [CollatzResearch.WordTrace]
  refine ⟨7825536683704107263377925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5217024455802738175585283 7825536683704107263377925)
  ·
    refine ⟨1467288128194520111883361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7825536683704107263377925 1467288128194520111883361)
    ·
      refine ⟨1100466096145890083912521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1467288128194520111883361 1100466096145890083912521)
      ·
        refine ⟨825349572109417562934391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1100466096145890083912521 825349572109417562934391)
        ·
          refine ⟨1238024358164126344401587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825349572109417562934391 1238024358164126344401587)
          ·
            refine ⟨1857036537246189516602381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238024358164126344401587 1857036537246189516602381)
            ·
              refine ⟨696388701467321068725893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1857036537246189516602381 696388701467321068725893)
              ·
                refine ⟨130572881525122700386105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 696388701467321068725893 130572881525122700386105)
                ·
                  refine ⟨97929661143842025289579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130572881525122700386105 97929661143842025289579)
                  ·
                    rfl

theorem cell20_214557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_214557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214557 prefixEnd_214557 := by exact prefixLift 214557
  have htrace : WordTrace (prefixWord ++ tailWord_214557) baseStart_214557 baseEnd_214557 := by
    simpa [prefixWord, tailWord_214557, baseEnd_214557] using wordTrace_append hprefix tailTrace_214557
  have hstable : (prefixWord ++ tailWord_214557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214557).length < 2 ^ (prefixWord ++ tailWord_214557).sum := by decide
  have hdescent : baseEnd_214557 < baseStart_214557 := by decide
  rcases family_descends (prefixWord ++ tailWord_214557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214605 : List Nat := [1, 6, 1, 1, 3, 2, 1, 2, 3]
def baseStart_214605 : Nat := 118140960795 + 214605 * 2 ^ 59
def prefixEnd_214605 : Nat := 4983230072969 + 3 ^ 40 * 214605 * 2
def baseEnd_214605 : Nat := 97951569651767191689383

theorem tailTrace_214605 : CollatzResearch.WordTrace tailWord_214605 prefixEnd_214605 97951569651767191689383 := by
  unfold tailWord_214605
  simp only [CollatzResearch.WordTrace]
  refine ⟨7827287387530211461125269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5218191591686807640750179 7827287387530211461125269)
  ·
    refine ⟨366904096290478662240247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7827287387530211461125269 366904096290478662240247)
    ·
      refine ⟨550356144435717993360371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366904096290478662240247 550356144435717993360371)
      ·
        refine ⟨825534216653576990040557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550356144435717993360371 825534216653576990040557)
        ·
          refine ⟨309575331245091371265209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 825534216653576990040557 309575331245091371265209)
          ·
            refine ⟨232181498433818528448907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309575331245091371265209 232181498433818528448907)
            ·
              refine ⟨348272247650727792673361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232181498433818528448907 348272247650727792673361)
              ·
                refine ⟨261204185738045844505021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348272247650727792673361 261204185738045844505021)
                ·
                  refine ⟨97951569651767191689383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261204185738045844505021 97951569651767191689383)
                  ·
                    rfl

theorem cell20_214605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_214605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214605 prefixEnd_214605 := by exact prefixLift 214605
  have htrace : WordTrace (prefixWord ++ tailWord_214605) baseStart_214605 baseEnd_214605 := by
    simpa [prefixWord, tailWord_214605, baseEnd_214605] using wordTrace_append hprefix tailTrace_214605
  have hstable : (prefixWord ++ tailWord_214605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214605).length < 2 ^ (prefixWord ++ tailWord_214605).sum := by decide
  have hdescent : baseEnd_214605 < baseStart_214605 := by decide
  rcases family_descends (prefixWord ++ tailWord_214605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214640 : List Nat := [2, 1, 1, 1, 6, 3, 2, 4]
def baseStart_214640 : Nat := 118140960795 + 214640 * 2 ^ 59
def prefixEnd_214640 : Nat := 4983230072969 + 3 ^ 40 * 214640 * 2
def baseEnd_214640 : Nat := 32655848201820875174191

theorem tailTrace_214640 : CollatzResearch.WordTrace tailWord_214640 prefixEnd_214640 32655848201820875174191 := by
  unfold tailWord_214640
  simp only [CollatzResearch.WordTrace]
  refine ⟨3914281971201706219324687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5219042628268941625766249 3914281971201706219324687)
  ·
    refine ⟨5871422956802559328987031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3914281971201706219324687 5871422956802559328987031)
    ·
      refine ⟨8807134435203838993480547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5871422956802559328987031 8807134435203838993480547)
      ·
        refine ⟨13210701652805758490220821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8807134435203838993480547 13210701652805758490220821)
        ·
          refine ⟨619251639975269929229101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13210701652805758490220821 619251639975269929229101)
          ·
            refine ⟨232219364990726223460913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 619251639975269929229101 232219364990726223460913)
            ·
              refine ⟨174164523743044667595685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232219364990726223460913 174164523743044667595685)
              ·
                refine ⟨32655848201820875174191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174164523743044667595685 32655848201820875174191)
                ·
                  rfl

theorem cell20_214640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_214640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214640 prefixEnd_214640 := by exact prefixLift 214640
  have htrace : WordTrace (prefixWord ++ tailWord_214640) baseStart_214640 baseEnd_214640 := by
    simpa [prefixWord, tailWord_214640, baseEnd_214640] using wordTrace_append hprefix tailTrace_214640
  have hstable : (prefixWord ++ tailWord_214640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214640).length < 2 ^ (prefixWord ++ tailWord_214640).sum := by decide
  have hdescent : baseEnd_214640 < baseStart_214640 := by decide
  rcases family_descends (prefixWord ++ tailWord_214640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214651 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 7]
def baseStart_214651 : Nat := 118140960795 + 214651 * 2 ^ 59
def prefixEnd_214651 : Nat := 4983230072969 + 3 ^ 40 * 214651 * 2
def baseEnd_214651 : Nat := 97972565305195476155861

theorem tailTrace_214651 : CollatzResearch.WordTrace tailWord_214651 prefixEnd_214651 97972565305195476155861 := by
  unfold tailWord_214651
  simp only [CollatzResearch.WordTrace]
  refine ⟨7828965145363561317299807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5219310096909040878199871 7828965145363561317299807)
  ·
    refine ⟨11743447718045341975949711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7828965145363561317299807 11743447718045341975949711)
    ·
      refine ⟨17615171577068012963924567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11743447718045341975949711 17615171577068012963924567)
      ·
        refine ⟨26422757365602019445886851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17615171577068012963924567 26422757365602019445886851)
        ·
          refine ⟨39634136048403029168830277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26422757365602019445886851 39634136048403029168830277)
          ·
            refine ⟨7431400509075567969155677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39634136048403029168830277 7431400509075567969155677)
            ·
              refine ⟨2786775190903337988433379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7431400509075567969155677 2786775190903337988433379)
              ·
                refine ⟨4180162786355006982650069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2786775190903337988433379 4180162786355006982650069)
                ·
                  refine ⟨97972565305195476155861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4180162786355006982650069 97972565305195476155861)
                  ·
                    rfl

theorem cell20_214651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_214651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214651 prefixEnd_214651 := by exact prefixLift 214651
  have htrace : WordTrace (prefixWord ++ tailWord_214651) baseStart_214651 baseEnd_214651 := by
    simpa [prefixWord, tailWord_214651, baseEnd_214651] using wordTrace_append hprefix tailTrace_214651
  have hstable : (prefixWord ++ tailWord_214651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214651).length < 2 ^ (prefixWord ++ tailWord_214651).sum := by decide
  have hdescent : baseEnd_214651 < baseStart_214651 := by decide
  rcases family_descends (prefixWord ++ tailWord_214651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214668 : List Nat := [2, 2, 1, 2, 1, 1, 4, 4, 3]
def baseStart_214668 : Nat := 118140960795 + 214668 * 2 ^ 59
def prefixEnd_214668 : Nat := 4983230072969 + 3 ^ 40 * 214668 * 2
def baseEnd_214668 : Nat := 97980324568418972589125

theorem tailTrace_214668 : CollatzResearch.WordTrace tailWord_214668 prefixEnd_214668 97980324568418972589125 := by
  unfold tailWord_214668
  simp only [CollatzResearch.WordTrace]
  refine ⟨3914792593150986610334329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5219723457534648813779105 3914792593150986610334329)
  ·
    refine ⟨2936094444863239957750747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3914792593150986610334329 2936094444863239957750747)
    ·
      refine ⟨4404141667294859936626121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2936094444863239957750747 4404141667294859936626121)
      ·
        refine ⟨3303106250471144952469591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4404141667294859936626121 3303106250471144952469591)
        ·
          refine ⟨4954659375706717428704387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3303106250471144952469591 4954659375706717428704387)
          ·
            refine ⟨7431989063560076143056581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4954659375706717428704387 7431989063560076143056581)
            ·
              refine ⟨1393497949417514276823109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7431989063560076143056581 1393497949417514276823109)
              ·
                refine ⟨261280865515783926904333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1393497949417514276823109 261280865515783926904333)
                ·
                  refine ⟨97980324568418972589125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261280865515783926904333 97980324568418972589125)
                  ·
                    rfl

theorem cell20_214668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_214668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214668 prefixEnd_214668 := by exact prefixLift 214668
  have htrace : WordTrace (prefixWord ++ tailWord_214668) baseStart_214668 baseEnd_214668 := by
    simpa [prefixWord, tailWord_214668, baseEnd_214668] using wordTrace_append hprefix tailTrace_214668
  have hstable : (prefixWord ++ tailWord_214668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214668).length < 2 ^ (prefixWord ++ tailWord_214668).sum := by decide
  have hdescent : baseEnd_214668 < baseStart_214668 := by decide
  rcases family_descends (prefixWord ++ tailWord_214668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214722 : List Nat := [3, 5, 1, 2, 1, 1, 1, 4, 2]
def baseStart_214722 : Nat := 118140960795 + 214722 * 2 ^ 59
def prefixEnd_214722 : Nat := 4983230072969 + 3 ^ 40 * 214722 * 2
def baseEnd_214722 : Nat := 98004971639834784788905

theorem tailTrace_214722 : CollatzResearch.WordTrace tailWord_214722 prefixEnd_214722 98004971639834784788905 := by
  unfold tailWord_214722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1957888682026585110783605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5221036485404226962089613 1957888682026585110783605)
  ·
    refine ⟨183552063939992354135963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1957888682026585110783605 183552063939992354135963)
    ·
      refine ⟨275328095909988531203945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183552063939992354135963 275328095909988531203945)
      ·
        refine ⟨206496071932491398402959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275328095909988531203945 206496071932491398402959)
        ·
          refine ⟨309744107898737097604439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206496071932491398402959 309744107898737097604439)
          ·
            refine ⟨464616161848105646406659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309744107898737097604439 464616161848105646406659)
            ·
              refine ⟨696924242772158469609989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464616161848105646406659 696924242772158469609989)
              ·
                refine ⟨130673295519779713051873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 696924242772158469609989 130673295519779713051873)
                ·
                  refine ⟨98004971639834784788905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130673295519779713051873 98004971639834784788905)
                  ·
                    rfl

theorem cell20_214722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_214722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214722 prefixEnd_214722 := by exact prefixLift 214722
  have htrace : WordTrace (prefixWord ++ tailWord_214722) baseStart_214722 baseEnd_214722 := by
    simpa [prefixWord, tailWord_214722, baseEnd_214722] using wordTrace_append hprefix tailTrace_214722
  have hstable : (prefixWord ++ tailWord_214722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214722).length < 2 ^ (prefixWord ++ tailWord_214722).sum := by decide
  have hdescent : baseEnd_214722 < baseStart_214722 := by decide
  rcases family_descends (prefixWord ++ tailWord_214722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214733 : List Nat := [1, 6, 2, 1, 1, 3, 1, 5]
def baseStart_214733 : Nat := 118140960795 + 214733 * 2 ^ 59
def prefixEnd_214733 : Nat := 4983230072969 + 3 ^ 40 * 214733 * 2
def baseEnd_214733 : Nat := 32669997446522545140731

theorem tailTrace_214733 : CollatzResearch.WordTrace tailWord_214733 prefixEnd_214733 32669997446522545140731 := by
  unfold tailWord_214733
  simp only [CollatzResearch.WordTrace]
  refine ⟨7831955931066489321784853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5221303954044326214523235 7831955931066489321784853)
  ·
    refine ⟨367122934268741686958665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7831955931066489321784853 367122934268741686958665)
    ·
      refine ⟨275342200701556265218999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367122934268741686958665 275342200701556265218999)
      ·
        refine ⟨413013301052334397828499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275342200701556265218999 413013301052334397828499)
        ·
          refine ⟨619519951578501596742749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413013301052334397828499 619519951578501596742749)
          ·
            refine ⟨232319981841938098778531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 619519951578501596742749 232319981841938098778531)
            ·
              refine ⟨348479972762907148167797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232319981841938098778531 348479972762907148167797)
              ·
                refine ⟨32669997446522545140731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 348479972762907148167797 32669997446522545140731)
                ·
                  rfl

theorem cell20_214733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 5].length) (baseStart_214733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214733 prefixEnd_214733 := by exact prefixLift 214733
  have htrace : WordTrace (prefixWord ++ tailWord_214733) baseStart_214733 baseEnd_214733 := by
    simpa [prefixWord, tailWord_214733, baseEnd_214733] using wordTrace_append hprefix tailTrace_214733
  have hstable : (prefixWord ++ tailWord_214733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214733).length < 2 ^ (prefixWord ++ tailWord_214733).sum := by decide
  have hdescent : baseEnd_214733 < baseStart_214733 := by decide
  rcases family_descends (prefixWord ++ tailWord_214733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214737 : List Nat := [1, 2, 2, 1, 2, 6, 1, 5]
def baseStart_214737 : Nat := 118140960795 + 214737 * 2 ^ 59
def prefixEnd_214737 : Nat := 4983230072969 + 3 ^ 40 * 214737 * 2
def baseEnd_214737 : Nat := 32670606016187133096281

theorem tailTrace_214737 : CollatzResearch.WordTrace tailWord_214737 prefixEnd_214737 32670606016187133096281 := by
  unfold tailWord_214737
  simp only [CollatzResearch.WordTrace]
  refine ⟨7832101823051998004930465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5221401215367998669953643 7832101823051998004930465)
  ·
    refine ⟨5874076367288998503697849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7832101823051998004930465 5874076367288998503697849)
    ·
      refine ⟨4405557275466748877773387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5874076367288998503697849 4405557275466748877773387)
      ·
        refine ⟨6608335913200123316660081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4405557275466748877773387 6608335913200123316660081)
        ·
          refine ⟨4956251934900092487495061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6608335913200123316660081 4956251934900092487495061)
          ·
            refine ⟨232324309448441835351331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4956251934900092487495061 232324309448441835351331)
            ·
              refine ⟨348486464172662753026997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232324309448441835351331 348486464172662753026997)
              ·
                refine ⟨32670606016187133096281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 348486464172662753026997 32670606016187133096281)
                ·
                  rfl

theorem cell20_214737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 5].length) (baseStart_214737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214737 prefixEnd_214737 := by exact prefixLift 214737
  have htrace : WordTrace (prefixWord ++ tailWord_214737) baseStart_214737 baseEnd_214737 := by
    simpa [prefixWord, tailWord_214737, baseEnd_214737] using wordTrace_append hprefix tailTrace_214737
  have hstable : (prefixWord ++ tailWord_214737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214737).length < 2 ^ (prefixWord ++ tailWord_214737).sum := by decide
  have hdescent : baseEnd_214737 < baseStart_214737 := by decide
  rcases family_descends (prefixWord ++ tailWord_214737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214744 : List Nat := [2, 1, 2, 2, 3, 1, 1, 5, 3]
def baseStart_214744 : Nat := 118140960795 + 214744 * 2 ^ 59
def prefixEnd_214744 : Nat := 4983230072969 + 3 ^ 40 * 214744 * 2
def baseEnd_214744 : Nat := 98015013039300486055481

theorem tailTrace_214744 : CollatzResearch.WordTrace tailWord_214744 prefixEnd_214744 98015013039300486055481 := by
  unfold tailWord_214744
  simp only [CollatzResearch.WordTrace]
  refine ⟨3916178567013319100217643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5221571422684425466956857 3916178567013319100217643)
  ·
    refine ⟨5874267850519978650326465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3916178567013319100217643 5874267850519978650326465)
    ·
      refine ⟨4405700887889983987744849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5874267850519978650326465 4405700887889983987744849)
      ·
        refine ⟨3304275665917487990808637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4405700887889983987744849 3304275665917487990808637)
        ·
          refine ⟨1239103374719057996553239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3304275665917487990808637 1239103374719057996553239)
          ·
            refine ⟨1858655062078586994829859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239103374719057996553239 1858655062078586994829859)
            ·
              refine ⟨2787982593117880492244789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1858655062078586994829859 2787982593117880492244789)
              ·
                refine ⟨261373368104801296147949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2787982593117880492244789 261373368104801296147949)
                ·
                  refine ⟨98015013039300486055481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261373368104801296147949 98015013039300486055481)
                  ·
                    rfl

theorem cell20_214744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_214744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214744 prefixEnd_214744 := by exact prefixLift 214744
  have htrace : WordTrace (prefixWord ++ tailWord_214744) baseStart_214744 baseEnd_214744 := by
    simpa [prefixWord, tailWord_214744, baseEnd_214744] using wordTrace_append hprefix tailTrace_214744
  have hstable : (prefixWord ++ tailWord_214744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214744).length < 2 ^ (prefixWord ++ tailWord_214744).sum := by decide
  have hdescent : baseEnd_214744 < baseStart_214744 := by decide
  rcases family_descends (prefixWord ++ tailWord_214744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214751 : List Nat := [1, 1, 2, 3, 2, 2, 3, 2, 4]
def baseStart_214751 : Nat := 118140960795 + 214751 * 2 ^ 59
def prefixEnd_214751 : Nat := 4983230072969 + 3 ^ 40 * 214751 * 2
def baseEnd_214751 : Nat := 98018208030039572822119

theorem tailTrace_214751 : CollatzResearch.WordTrace tailWord_214751 prefixEnd_214751 98018208030039572822119 := by
  unfold tailWord_214751
  simp only [CollatzResearch.WordTrace]
  refine ⟨7832612445001278395940107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5221741630000852263960071 7832612445001278395940107)
  ·
    refine ⟨11748918667501917593910161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7832612445001278395940107 11748918667501917593910161)
    ·
      refine ⟨8811689000626438195432621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11748918667501917593910161 8811689000626438195432621)
      ·
        refine ⟨3304383375234914323287233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8811689000626438195432621 3304383375234914323287233)
        ·
          refine ⟨2478287531426185742465425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3304383375234914323287233 2478287531426185742465425)
          ·
            refine ⟨1858715648569639306849069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2478287531426185742465425 1858715648569639306849069)
            ·
              refine ⟨697018368213614740068401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1858715648569639306849069 697018368213614740068401)
              ·
                refine ⟨522763776160211055051301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697018368213614740068401 522763776160211055051301)
                ·
                  refine ⟨98018208030039572822119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 522763776160211055051301 98018208030039572822119)
                  ·
                    rfl

theorem cell20_214751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_214751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214751 prefixEnd_214751 := by exact prefixLift 214751
  have htrace : WordTrace (prefixWord ++ tailWord_214751) baseStart_214751 baseEnd_214751 := by
    simpa [prefixWord, tailWord_214751, baseEnd_214751] using wordTrace_append hprefix tailTrace_214751
  have hstable : (prefixWord ++ tailWord_214751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214751).length < 2 ^ (prefixWord ++ tailWord_214751).sum := by decide
  have hdescent : baseEnd_214751 < baseStart_214751 := by decide
  rcases family_descends (prefixWord ++ tailWord_214751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214820 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 5]
def baseStart_214820 : Nat := 118140960795 + 214820 * 2 ^ 59
def prefixEnd_214820 : Nat := 4983230072969 + 3 ^ 40 * 214820 * 2
def baseEnd_214820 : Nat := 98049701510181999521837

theorem tailTrace_214820 : CollatzResearch.WordTrace tailWord_214820 prefixEnd_214820 98049701510181999521837 := by
  unfold tailWord_214820
  simp only [CollatzResearch.WordTrace]
  refine ⟨3917564540875651590100957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5223419387834202120134609 3917564540875651590100957)
  ·
    refine ⟨1469086702828369346287859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3917564540875651590100957 1469086702828369346287859)
    ·
      refine ⟨2203630054242554019431789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1469086702828369346287859 2203630054242554019431789)
      ·
        refine ⟨826361270340957757286921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2203630054242554019431789 826361270340957757286921)
        ·
          refine ⟨619770952755718317965191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 826361270340957757286921 619770952755718317965191)
          ·
            refine ⟨929656429133577476947787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619770952755718317965191 929656429133577476947787)
            ·
              refine ⟨1394484643700366215421681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929656429133577476947787 1394484643700366215421681)
              ·
                refine ⟨1045863482775274661566261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1394484643700366215421681 1045863482775274661566261)
                ·
                  refine ⟨98049701510181999521837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1045863482775274661566261 98049701510181999521837)
                  ·
                    rfl

theorem cell20_214820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_214820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214820 prefixEnd_214820 := by exact prefixLift 214820
  have htrace : WordTrace (prefixWord ++ tailWord_214820) baseStart_214820 baseEnd_214820 := by
    simpa [prefixWord, tailWord_214820, baseEnd_214820] using wordTrace_append hprefix tailTrace_214820
  have hstable : (prefixWord ++ tailWord_214820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214820).length < 2 ^ (prefixWord ++ tailWord_214820).sum := by decide
  have hdescent : baseEnd_214820 < baseStart_214820 := by decide
  rcases family_descends (prefixWord ++ tailWord_214820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214830 : List Nat := [4, 1, 3, 2, 2, 2, 6]
def baseStart_214830 : Nat := 118140960795 + 214830 * 2 ^ 59
def prefixEnd_214830 : Nat := 4983230072969 + 3 ^ 40 * 214830 * 2
def baseEnd_214830 : Nat := 10894918420296267687607

theorem tailTrace_214830 : CollatzResearch.WordTrace tailWord_214830 prefixEnd_214830 10894918420296267687607 := by
  unfold tailWord_214830
  simp only [CollatzResearch.WordTrace]
  refine ⟨979436726464384361008243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5223662541143383258710629 979436726464384361008243)
  ·
    refine ⟨1469155089696576541512365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 979436726464384361008243 1469155089696576541512365)
    ·
      refine ⟨550933158636216203067137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1469155089696576541512365 550933158636216203067137)
      ·
        refine ⟨413199868977162152300353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550933158636216203067137 413199868977162152300353)
        ·
          refine ⟨309899901732871614225265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413199868977162152300353 309899901732871614225265)
          ·
            refine ⟨232424926299653710668949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309899901732871614225265 232424926299653710668949)
            ·
              refine ⟨10894918420296267687607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 232424926299653710668949 10894918420296267687607)
              ·
                rfl

theorem cell20_214830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 6].length) (baseStart_214830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214830 prefixEnd_214830 := by exact prefixLift 214830
  have htrace : WordTrace (prefixWord ++ tailWord_214830) baseStart_214830 baseEnd_214830 := by
    simpa [prefixWord, tailWord_214830, baseEnd_214830] using wordTrace_append hprefix tailTrace_214830
  have hstable : (prefixWord ++ tailWord_214830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214830).length < 2 ^ (prefixWord ++ tailWord_214830).sum := by decide
  have hdescent : baseEnd_214830 < baseStart_214830 := by decide
  rcases family_descends (prefixWord ++ tailWord_214830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214834 : List Nat := [3, 2, 1, 1, 3, 2, 8]
def baseStart_214834 : Nat := 118140960795 + 214834 * 2 ^ 59
def prefixEnd_214834 : Nat := 4983230072969 + 3 ^ 40 * 214834 * 2
def baseEnd_214834 : Nat := 10895121276851130339457

theorem tailTrace_214834 : CollatzResearch.WordTrace tailWord_214834 prefixEnd_214834 10895121276851130339457 := by
  unfold tailWord_214834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1958909925925145892802889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5223759802467055714141037 1958909925925145892802889)
  ·
    refine ⟨1469182444443859419602167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1958909925925145892802889 1469182444443859419602167)
    ·
      refine ⟨2203773666665789129403251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1469182444443859419602167 2203773666665789129403251)
      ·
        refine ⟨3305660499998683694104877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2203773666665789129403251 3305660499998683694104877)
        ·
          refine ⟨1239622687499506385289329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3305660499998683694104877 1239622687499506385289329)
          ·
            refine ⟨929717015624629788966997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1239622687499506385289329 929717015624629788966997)
            ·
              refine ⟨10895121276851130339457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 929717015624629788966997 10895121276851130339457)
              ·
                rfl

theorem cell20_214834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 8].length) (baseStart_214834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214834 prefixEnd_214834 := by exact prefixLift 214834
  have htrace : WordTrace (prefixWord ++ tailWord_214834) baseStart_214834 baseEnd_214834 := by
    simpa [prefixWord, tailWord_214834, baseEnd_214834] using wordTrace_append hprefix tailTrace_214834
  have hstable : (prefixWord ++ tailWord_214834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214834).length < 2 ^ (prefixWord ++ tailWord_214834).sum := by decide
  have hdescent : baseEnd_214834 < baseStart_214834 := by decide
  rcases family_descends (prefixWord ++ tailWord_214834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214844 : List Nat := [2, 2, 2, 2, 1, 1, 2, 6, 2]
def baseStart_214844 : Nat := 118140960795 + 214844 * 2 ^ 59
def prefixEnd_214844 : Nat := 4983230072969 + 3 ^ 40 * 214844 * 2
def baseEnd_214844 : Nat := 98060655764144582721739

theorem tailTrace_214844 : CollatzResearch.WordTrace tailWord_214844 prefixEnd_214844 98060655764144582721739 := by
  unfold tailWord_214844
  simp only [CollatzResearch.WordTrace]
  refine ⟨3918002216832177639537793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5224002955776236852717057 3918002216832177639537793)
  ·
    refine ⟨2938501662624133229653345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3918002216832177639537793 2938501662624133229653345)
    ·
      refine ⟨2203876246968099922240009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2938501662624133229653345 2203876246968099922240009)
      ·
        refine ⟨1652907185226074941680007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2203876246968099922240009 1652907185226074941680007)
        ·
          refine ⟨2479360777839112412520011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1652907185226074941680007 2479360777839112412520011)
          ·
            refine ⟨3719041166758668618780017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2479360777839112412520011 3719041166758668618780017)
            ·
              refine ⟨2789280875069001464085013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3719041166758668618780017 2789280875069001464085013)
              ·
                refine ⟨130747541018859443628985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2789280875069001464085013 130747541018859443628985)
                ·
                  refine ⟨98060655764144582721739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130747541018859443628985 98060655764144582721739)
                  ·
                    rfl

theorem cell20_214844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_214844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214844 prefixEnd_214844 := by exact prefixLift 214844
  have htrace : WordTrace (prefixWord ++ tailWord_214844) baseStart_214844 baseEnd_214844 := by
    simpa [prefixWord, tailWord_214844, baseEnd_214844] using wordTrace_append hprefix tailTrace_214844
  have hstable : (prefixWord ++ tailWord_214844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214844).length < 2 ^ (prefixWord ++ tailWord_214844).sum := by decide
  have hdescent : baseEnd_214844 < baseStart_214844 := by decide
  rcases family_descends (prefixWord ++ tailWord_214844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214858 : List Nat := [3, 1, 2, 1, 1, 1, 5, 3, 3]
def baseStart_214858 : Nat := 118140960795 + 214858 * 2 ^ 59
def prefixEnd_214858 : Nat := 4983230072969 + 3 ^ 40 * 214858 * 2
def baseEnd_214858 : Nat := 98067045745622756255015

theorem tailTrace_214858 : CollatzResearch.WordTrace tailWord_214858 prefixEnd_214858 98067045745622756255015 := by
  unfold tailWord_214858
  simp only [CollatzResearch.WordTrace]
  refine ⟨1959128763903408917521307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5224343370409090446723485 1959128763903408917521307)
  ·
    refine ⟨2938693145855113376281961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1959128763903408917521307 2938693145855113376281961)
    ·
      refine ⟨2204019859391335032211471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2938693145855113376281961 2204019859391335032211471)
      ·
        refine ⟨3306029789087002548317207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2204019859391335032211471 3306029789087002548317207)
        ·
          refine ⟨4959044683630503822475811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3306029789087002548317207 4959044683630503822475811)
          ·
            refine ⟨7438567025445755733713717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4959044683630503822475811 7438567025445755733713717)
            ·
              refine ⟨697365658635539600035661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7438567025445755733713717 697365658635539600035661)
              ·
                refine ⟨261512121988327350013373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 697365658635539600035661 261512121988327350013373)
                ·
                  refine ⟨98067045745622756255015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261512121988327350013373 98067045745622756255015)
                  ·
                    rfl

theorem cell20_214858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_214858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214858 prefixEnd_214858 := by exact prefixLift 214858
  have htrace : WordTrace (prefixWord ++ tailWord_214858) baseStart_214858 baseEnd_214858 := by
    simpa [prefixWord, tailWord_214858, baseEnd_214858] using wordTrace_append hprefix tailTrace_214858
  have hstable : (prefixWord ++ tailWord_214858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214858).length < 2 ^ (prefixWord ++ tailWord_214858).sum := by decide
  have hdescent : baseEnd_214858 < baseStart_214858 := by decide
  rcases family_descends (prefixWord ++ tailWord_214858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214920 : List Nat := [2, 1, 3, 3, 3, 1, 1, 2, 4]
def baseStart_214920 : Nat := 118140960795 + 214920 * 2 ^ 59
def prefixEnd_214920 : Nat := 4983230072969 + 3 ^ 40 * 214920 * 2
def baseEnd_214920 : Nat := 98095344235026096188095

theorem tailTrace_214920 : CollatzResearch.WordTrace tailWord_214920 prefixEnd_214920 98095344235026096188095 := by
  unfold tailWord_214920
  simp only [CollatzResearch.WordTrace]
  refine ⟨3919388190694510129421107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5225850920926013505894809 3919388190694510129421107)
  ·
    refine ⟨5879082286041765194131661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3919388190694510129421107 5879082286041765194131661)
    ·
      refine ⟨2204655857265661947799373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5879082286041765194131661 2204655857265661947799373)
      ·
        refine ⟨826745946474623230424765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2204655857265661947799373 826745946474623230424765)
        ·
          refine ⟨310029729927983711409287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 826745946474623230424765 310029729927983711409287)
          ·
            refine ⟨465044594891975567113931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310029729927983711409287 465044594891975567113931)
            ·
              refine ⟨697566892337963350670897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465044594891975567113931 697566892337963350670897)
              ·
                refine ⟨523175169253472513003173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697566892337963350670897 523175169253472513003173)
                ·
                  refine ⟨98095344235026096188095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 523175169253472513003173 98095344235026096188095)
                  ·
                    rfl

theorem cell20_214920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_214920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214920 prefixEnd_214920 := by exact prefixLift 214920
  have htrace : WordTrace (prefixWord ++ tailWord_214920) baseStart_214920 baseEnd_214920 := by
    simpa [prefixWord, tailWord_214920, baseEnd_214920] using wordTrace_append hprefix tailTrace_214920
  have hstable : (prefixWord ++ tailWord_214920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214920).length < 2 ^ (prefixWord ++ tailWord_214920).sum := by decide
  have hdescent : baseEnd_214920 < baseStart_214920 := by decide
  rcases family_descends (prefixWord ++ tailWord_214920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214948 : List Nat := [2, 3, 1, 2, 1, 4, 7]
def baseStart_214948 : Nat := 118140960795 + 214948 * 2 ^ 59
def prefixEnd_214948 : Nat := 4983230072969 + 3 ^ 40 * 214948 * 2
def baseEnd_214948 : Nat := 10900902688664715917183

theorem tailTrace_214948 : CollatzResearch.WordTrace tailWord_214948 prefixEnd_214948 10900902688664715917183 := by
  unfold tailWord_214948
  simp only [CollatzResearch.WordTrace]
  refine ⟨3919898812643790520430749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5226531750191720693907665 3919898812643790520430749)
  ·
    refine ⟨1469962054741421445161531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3919898812643790520430749 1469962054741421445161531)
    ·
      refine ⟨2204943082112132167742297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1469962054741421445161531 2204943082112132167742297)
      ·
        refine ⟨1653707311584099125806723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2204943082112132167742297 1653707311584099125806723)
        ·
          refine ⟨2480560967376148688710085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1653707311584099125806723 2480560967376148688710085)
          ·
            refine ⟨465105181383027879133141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2480560967376148688710085 465105181383027879133141)
            ·
              refine ⟨10900902688664715917183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 465105181383027879133141 10900902688664715917183)
              ·
                rfl

theorem cell20_214948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 7].length) (baseStart_214948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214948 prefixEnd_214948 := by exact prefixLift 214948
  have htrace : WordTrace (prefixWord ++ tailWord_214948) baseStart_214948 baseEnd_214948 := by
    simpa [prefixWord, tailWord_214948, baseEnd_214948] using wordTrace_append hprefix tailTrace_214948
  have hstable : (prefixWord ++ tailWord_214948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214948).length < 2 ^ (prefixWord ++ tailWord_214948).sum := by decide
  have hdescent : baseEnd_214948 < baseStart_214948 := by decide
  rcases family_descends (prefixWord ++ tailWord_214948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214951 : List Nat := [1, 1, 6, 1, 2, 1, 3, 2, 3]
def baseStart_214951 : Nat := 118140960795 + 214951 * 2 ^ 59
def prefixEnd_214951 : Nat := 4983230072969 + 3 ^ 40 * 214951 * 2
def baseEnd_214951 : Nat := 98109493479727766154635

theorem tailTrace_214951 : CollatzResearch.WordTrace tailWord_214951 prefixEnd_214951 98109493479727766154635 := by
  unfold tailWord_214951
  simp only [CollatzResearch.WordTrace]
  refine ⟨7839907044276712553220707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5226604696184475035480471 7839907044276712553220707)
  ·
    refine ⟨11759860566415068829831061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7839907044276712553220707 11759860566415068829831061)
    ·
      refine ⟨551243464050706351398331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11759860566415068829831061 551243464050706351398331)
      ·
        refine ⟨826865196076059527097497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551243464050706351398331 826865196076059527097497)
        ·
          refine ⟨620148897057044645323123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 826865196076059527097497 620148897057044645323123)
          ·
            refine ⟨930223345585566967984685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620148897057044645323123 930223345585566967984685)
            ·
              refine ⟨348833754594587612994257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 930223345585566967984685 348833754594587612994257)
              ·
                refine ⟨261625315945940709745693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348833754594587612994257 261625315945940709745693)
                ·
                  refine ⟨98109493479727766154635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261625315945940709745693 98109493479727766154635)
                  ·
                    rfl

theorem cell20_214951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 3].length) (baseStart_214951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_214951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_214951 prefixEnd_214951 := by exact prefixLift 214951
  have htrace : WordTrace (prefixWord ++ tailWord_214951) baseStart_214951 baseEnd_214951 := by
    simpa [prefixWord, tailWord_214951, baseEnd_214951] using wordTrace_append hprefix tailTrace_214951
  have hstable : (prefixWord ++ tailWord_214951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214951).length < 2 ^ (prefixWord ++ tailWord_214951).sum := by decide
  have hdescent : baseEnd_214951 < baseStart_214951 := by decide
  rcases family_descends (prefixWord ++ tailWord_214951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215068 : List Nat := [2, 2, 3, 1, 3, 3, 2, 2, 2]
def baseStart_215068 : Nat := 118140960795 + 215068 * 2 ^ 59
def prefixEnd_215068 : Nat := 4983230072969 + 3 ^ 40 * 215068 * 2
def baseEnd_215068 : Nat := 98162895467795359254157

theorem tailTrace_215068 : CollatzResearch.WordTrace tailWord_215068 prefixEnd_215068 98162895467795359254157 := by
  unfold tailWord_215068
  simp only [CollatzResearch.WordTrace]
  refine ⟨3922087192426420767614929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5229449589901894356819905 3922087192426420767614929)
  ·
    refine ⟨2941565394319815575711197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3922087192426420767614929 2941565394319815575711197)
    ·
      refine ⟨1103087022869930840891699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2941565394319815575711197 1103087022869930840891699)
      ·
        refine ⟨1654630534304896261337549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1103087022869930840891699 1654630534304896261337549)
        ·
          refine ⟨620486450364336098001581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1654630534304896261337549 620486450364336098001581)
          ·
            refine ⟨232682418886626036750593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 620486450364336098001581 232682418886626036750593)
            ·
              refine ⟨174511814164969527562945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232682418886626036750593 174511814164969527562945)
              ·
                refine ⟨130883860623727145672209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174511814164969527562945 130883860623727145672209)
                ·
                  refine ⟨98162895467795359254157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130883860623727145672209 98162895467795359254157)
                  ·
                    rfl

theorem cell20_215068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_215068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215068 prefixEnd_215068 := by exact prefixLift 215068
  have htrace : WordTrace (prefixWord ++ tailWord_215068) baseStart_215068 baseEnd_215068 := by
    simpa [prefixWord, tailWord_215068, baseEnd_215068] using wordTrace_append hprefix tailTrace_215068
  have hstable : (prefixWord ++ tailWord_215068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215068).length < 2 ^ (prefixWord ++ tailWord_215068).sum := by decide
  have hdescent : baseEnd_215068 < baseStart_215068 := by decide
  rcases family_descends (prefixWord ++ tailWord_215068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215083 : List Nat := [1, 1, 1, 1, 2, 1, 4, 9]
def baseStart_215083 : Nat := 118140960795 + 215083 * 2 ^ 59
def prefixEnd_215083 : Nat := 4983230072969 + 3 ^ 40 * 215083 * 2
def baseEnd_215083 : Nat := 32723247292173991251365

theorem tailTrace_215083 : CollatzResearch.WordTrace tailWord_215083 prefixEnd_215083 32723247292173991251365 := by
  unfold tailWord_215083
  simp only [CollatzResearch.WordTrace]
  refine ⟨7844721479798499097025903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5229814319865666064683935 7844721479798499097025903)
  ·
    refine ⟨11767082219697748645538855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7844721479798499097025903 11767082219697748645538855)
    ·
      refine ⟨17650623329546622968308283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11767082219697748645538855 17650623329546622968308283)
      ·
        refine ⟨26475934994319934452462425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17650623329546622968308283 26475934994319934452462425)
        ·
          refine ⟨19856951245739950839346819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26475934994319934452462425 19856951245739950839346819)
          ·
            refine ⟨29785426868609926259020229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19856951245739950839346819 29785426868609926259020229)
            ·
              refine ⟨5584767537864361173566293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29785426868609926259020229 5584767537864361173566293)
              ·
                refine ⟨32723247292173991251365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5584767537864361173566293 32723247292173991251365)
                ·
                  rfl

theorem cell20_215083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 9].length) (baseStart_215083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215083 prefixEnd_215083 := by exact prefixLift 215083
  have htrace : WordTrace (prefixWord ++ tailWord_215083) baseStart_215083 baseEnd_215083 := by
    simpa [prefixWord, tailWord_215083, baseEnd_215083] using wordTrace_append hprefix tailTrace_215083
  have hstable : (prefixWord ++ tailWord_215083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215083).length < 2 ^ (prefixWord ++ tailWord_215083).sum := by decide
  have hdescent : baseEnd_215083 < baseStart_215083 := by decide
  rcases family_descends (prefixWord ++ tailWord_215083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215110 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_215110 : Nat := 118140960795 + 215110 * 2 ^ 59
def prefixEnd_215110 : Nat := 4983230072969 + 3 ^ 40 * 215110 * 2
def baseEnd_215110 : Nat := 98182065412229879853985

theorem tailTrace_215110 : CollatzResearch.WordTrace tailWord_215110 prefixEnd_215110 98182065412229879853985 := by
  unfold tailWord_215110
  simp only [CollatzResearch.WordTrace]
  refine ⟨245178320334396334633087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5230470833800455138839189 245178320334396334633087)
  ·
    refine ⟨367767480501594501949631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245178320334396334633087 367767480501594501949631)
    ·
      refine ⟨551651220752391752924447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367767480501594501949631 551651220752391752924447)
      ·
        refine ⟨827476831128587629386671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551651220752391752924447 827476831128587629386671)
        ·
          refine ⟨1241215246692881444080007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827476831128587629386671 1241215246692881444080007)
          ·
            refine ⟨1861822870039322166120011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241215246692881444080007 1861822870039322166120011)
            ·
              refine ⟨2792734305058983249180017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1861822870039322166120011 2792734305058983249180017)
              ·
                refine ⟨2094550728794237436885013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2792734305058983249180017 2094550728794237436885013)
                ·
                  refine ⟨98182065412229879853985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2094550728794237436885013 98182065412229879853985)
                  ·
                    rfl

theorem cell20_215110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_215110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215110 prefixEnd_215110 := by exact prefixLift 215110
  have htrace : WordTrace (prefixWord ++ tailWord_215110) baseStart_215110 baseEnd_215110 := by
    simpa [prefixWord, tailWord_215110, baseEnd_215110] using wordTrace_append hprefix tailTrace_215110
  have hstable : (prefixWord ++ tailWord_215110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215110).length < 2 ^ (prefixWord ++ tailWord_215110).sum := by decide
  have hdescent : baseEnd_215110 < baseStart_215110 := by decide
  rcases family_descends (prefixWord ++ tailWord_215110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215114 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_215114 : Nat := 118140960795 + 215114 * 2 ^ 59
def prefixEnd_215114 : Nat := 4983230072969 + 3 ^ 40 * 215114 * 2
def baseEnd_215114 : Nat := 98183891121223643720635

theorem tailTrace_215114 : CollatzResearch.WordTrace tailWord_215114 prefixEnd_215114 98183891121223643720635 := by
  unfold tailWord_215114
  simp only [CollatzResearch.WordTrace]
  refine ⟨1961463035671547847851099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5230568095124127594269597 1961463035671547847851099)
  ·
    refine ⟨2942194553507321771776649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1961463035671547847851099 2942194553507321771776649)
    ·
      refine ⟨2206645915130491328832487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2942194553507321771776649 2206645915130491328832487)
      ·
        refine ⟨3309968872695736993248731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2206645915130491328832487 3309968872695736993248731)
        ·
          refine ⟨4964953309043605489873097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3309968872695736993248731 4964953309043605489873097)
          ·
            refine ⟨3723714981782704117404823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4964953309043605489873097 3723714981782704117404823)
            ·
              refine ⟨5585572472674056176107235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3723714981782704117404823 5585572472674056176107235)
              ·
                refine ⟨8378358709011084264160853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5585572472674056176107235 8378358709011084264160853)
                ·
                  refine ⟨98183891121223643720635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8378358709011084264160853 98183891121223643720635)
                  ·
                    rfl

theorem cell20_215114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_215114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215114 prefixEnd_215114 := by exact prefixLift 215114
  have htrace : WordTrace (prefixWord ++ tailWord_215114) baseStart_215114 baseEnd_215114 := by
    simpa [prefixWord, tailWord_215114, baseEnd_215114] using wordTrace_append hprefix tailTrace_215114
  have hstable : (prefixWord ++ tailWord_215114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215114).length < 2 ^ (prefixWord ++ tailWord_215114).sum := by decide
  have hdescent : baseEnd_215114 < baseStart_215114 := by decide
  rcases family_descends (prefixWord ++ tailWord_215114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215141 : List Nat := [1, 3, 1, 3, 2, 3, 3, 1, 3]
def baseStart_215141 : Nat := 118140960795 + 215141 * 2 ^ 59
def prefixEnd_215141 : Nat := 4983230072969 + 3 ^ 40 * 215141 * 2
def baseEnd_215141 : Nat := 98196214656931549820525

theorem tailTrace_215141 : CollatzResearch.WordTrace tailWord_215141 prefixEnd_215141 98196214656931549820525 := by
  unfold tailWord_215141
  simp only [CollatzResearch.WordTrace]
  refine ⟨7846836913588375002637277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5231224609058916668424851 7846836913588375002637277)
  ·
    refine ⟨2942563842595640625988979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7846836913588375002637277 2942563842595640625988979)
    ·
      refine ⟨4413845763893460938983469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2942563842595640625988979 4413845763893460938983469)
      ·
        refine ⟨1655192161460047852118801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4413845763893460938983469 1655192161460047852118801)
        ·
          refine ⟨1241394121095035889089101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1655192161460047852118801 1241394121095035889089101)
          ·
            refine ⟨465522795410638458408413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1241394121095035889089101 465522795410638458408413)
            ·
              refine ⟨174571048278989421903155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 465522795410638458408413 174571048278989421903155)
              ·
                refine ⟨261856572418484132854733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174571048278989421903155 261856572418484132854733)
                ·
                  refine ⟨98196214656931549820525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261856572418484132854733 98196214656931549820525)
                  ·
                    rfl

theorem cell20_215141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_215141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215141 prefixEnd_215141 := by exact prefixLift 215141
  have htrace : WordTrace (prefixWord ++ tailWord_215141) baseStart_215141 baseEnd_215141 := by
    simpa [prefixWord, tailWord_215141, baseEnd_215141] using wordTrace_append hprefix tailTrace_215141
  have hstable : (prefixWord ++ tailWord_215141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215141).length < 2 ^ (prefixWord ++ tailWord_215141).sum := by decide
  have hdescent : baseEnd_215141 < baseStart_215141 := by decide
  rcases family_descends (prefixWord ++ tailWord_215141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215165 : List Nat := [1, 4, 1, 1, 3, 4, 1, 3, 2]
def baseStart_215165 : Nat := 118140960795 + 215165 * 2 ^ 59
def prefixEnd_215165 : Nat := 4983230072969 + 3 ^ 40 * 215165 * 2
def baseEnd_215165 : Nat := 98207168910894133020427

theorem tailTrace_215165 : CollatzResearch.WordTrace tailWord_215165 prefixEnd_215165 98207168910894133020427 := by
  unfold tailWord_215165
  simp only [CollatzResearch.WordTrace]
  refine ⟨7847712265501427101510949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5231808177000951401007299 7847712265501427101510949)
  ·
    refine ⟨1471446049781517581533303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7847712265501427101510949 1471446049781517581533303)
    ·
      refine ⟨2207169074672276372299955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1471446049781517581533303 2207169074672276372299955)
      ·
        refine ⟨3310753612008414558449933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2207169074672276372299955 3310753612008414558449933)
        ·
          refine ⟨1241532604503155459418725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3310753612008414558449933 1241532604503155459418725)
          ·
            refine ⟨232787363344341648641011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1241532604503155459418725 232787363344341648641011)
            ·
              refine ⟨349181045016512472961517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232787363344341648641011 349181045016512472961517)
              ·
                refine ⟨130942891881192177360569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349181045016512472961517 130942891881192177360569)
                ·
                  refine ⟨98207168910894133020427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130942891881192177360569 98207168910894133020427)
                  ·
                    rfl

theorem cell20_215165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_215165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215165 prefixEnd_215165 := by exact prefixLift 215165
  have htrace : WordTrace (prefixWord ++ tailWord_215165) baseStart_215165 baseEnd_215165 := by
    simpa [prefixWord, tailWord_215165, baseEnd_215165] using wordTrace_append hprefix tailTrace_215165
  have hstable : (prefixWord ++ tailWord_215165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215165).length < 2 ^ (prefixWord ++ tailWord_215165).sum := by decide
  have hdescent : baseEnd_215165 < baseStart_215165 := by decide
  rcases family_descends (prefixWord ++ tailWord_215165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215176 : List Nat := [2, 1, 3, 4, 1, 1, 8]
def baseStart_215176 : Nat := 118140960795 + 215176 * 2 ^ 59
def prefixEnd_215176 : Nat := 4983230072969 + 3 ^ 40 * 215176 * 2
def baseEnd_215176 : Nat := 10912465512291887072635

theorem tailTrace_215176 : CollatzResearch.WordTrace tailWord_215176 prefixEnd_215176 10912465512291887072635 := by
  unfold tailWord_215176
  simp only [CollatzResearch.WordTrace]
  refine ⟨3924056734230787990080691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5232075645641050653440921 3924056734230787990080691)
  ·
    refine ⟨5886085101346181985121037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3924056734230787990080691 5886085101346181985121037)
    ·
      refine ⟨2207281913004818244420389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5886085101346181985121037 2207281913004818244420389)
      ·
        refine ⟨413865358688403420828823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2207281913004818244420389 413865358688403420828823)
        ·
          refine ⟨620798038032605131243235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413865358688403420828823 620798038032605131243235)
          ·
            refine ⟨931197057048907696864853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620798038032605131243235 931197057048907696864853)
            ·
              refine ⟨10912465512291887072635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 931197057048907696864853 10912465512291887072635)
              ·
                rfl

theorem cell20_215176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 8].length) (baseStart_215176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215176 prefixEnd_215176 := by exact prefixLift 215176
  have htrace : WordTrace (prefixWord ++ tailWord_215176) baseStart_215176 baseEnd_215176 := by
    simpa [prefixWord, tailWord_215176, baseEnd_215176] using wordTrace_append hprefix tailTrace_215176
  have hstable : (prefixWord ++ tailWord_215176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215176).length < 2 ^ (prefixWord ++ tailWord_215176).sum := by decide
  have hdescent : baseEnd_215176 < baseStart_215176 := by decide
  rcases family_descends (prefixWord ++ tailWord_215176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215182 : List Nat := [4, 1, 1, 3, 3, 1, 3, 2, 2]
def baseStart_215182 : Nat := 118140960795 + 215182 * 2 ^ 59
def prefixEnd_215182 : Nat := 4983230072969 + 3 ^ 40 * 215182 * 2
def baseEnd_215182 : Nat := 98214928174117629453691

theorem tailTrace_215182 : CollatzResearch.WordTrace tailWord_215182 prefixEnd_215182 98214928174117629453691 := by
  unfold tailWord_215182
  simp only [CollatzResearch.WordTrace]
  refine ⟨981041538304979875609975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5232221537626559336586533 981041538304979875609975)
  ·
    refine ⟨1471562307457469813414963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 981041538304979875609975 1471562307457469813414963)
    ·
      refine ⟨2207343461186204720122445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1471562307457469813414963 2207343461186204720122445)
      ·
        refine ⟨827753797944826770045917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2207343461186204720122445 827753797944826770045917)
        ·
          refine ⟨310407674229310038767219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 827753797944826770045917 310407674229310038767219)
          ·
            refine ⟨465611511343965058150829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310407674229310038767219 465611511343965058150829)
            ·
              refine ⟨174604316753986896806561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 465611511343965058150829 174604316753986896806561)
              ·
                refine ⟨130953237565490172604921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174604316753986896806561 130953237565490172604921)
                ·
                  refine ⟨98214928174117629453691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130953237565490172604921 98214928174117629453691)
                  ·
                    rfl

theorem cell20_215182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_215182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215182 prefixEnd_215182 := by exact prefixLift 215182
  have htrace : WordTrace (prefixWord ++ tailWord_215182) baseStart_215182 baseEnd_215182 := by
    simpa [prefixWord, tailWord_215182, baseEnd_215182] using wordTrace_append hprefix tailTrace_215182
  have hstable : (prefixWord ++ tailWord_215182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215182).length < 2 ^ (prefixWord ++ tailWord_215182).sum := by decide
  have hdescent : baseEnd_215182 < baseStart_215182 := by decide
  rcases family_descends (prefixWord ++ tailWord_215182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215200 : List Nat := [2, 1, 1, 4, 2, 3, 1, 3, 3]
def baseStart_215200 : Nat := 118140960795 + 215200 * 2 ^ 59
def prefixEnd_215200 : Nat := 4983230072969 + 3 ^ 40 * 215200 * 2
def baseEnd_215200 : Nat := 98223143864589566853617

theorem tailTrace_215200 : CollatzResearch.WordTrace tailWord_215200 prefixEnd_215200 98223143864589566853617 := by
  unfold tailWord_215200
  simp only [CollatzResearch.WordTrace]
  refine ⟨3924494410187314039517527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5232659213583085386023369 3924494410187314039517527)
  ·
    refine ⟨5886741615280971059276291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3924494410187314039517527 5886741615280971059276291)
    ·
      refine ⟨8830112422921456588914437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5886741615280971059276291 8830112422921456588914437)
      ·
        refine ⟨1655646079297773110421457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8830112422921456588914437 1655646079297773110421457)
        ·
          refine ⟨1241734559473329832816093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1655646079297773110421457 1241734559473329832816093)
          ·
            refine ⟨465650459802498687306035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1241734559473329832816093 465650459802498687306035)
            ·
              refine ⟨698475689703748030959053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465650459802498687306035 698475689703748030959053)
              ·
                refine ⟨261928383638905511609645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 698475689703748030959053 261928383638905511609645)
                ·
                  refine ⟨98223143864589566853617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261928383638905511609645 98223143864589566853617)
                  ·
                    rfl

theorem cell20_215200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_215200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215200 prefixEnd_215200 := by exact prefixLift 215200
  have htrace : WordTrace (prefixWord ++ tailWord_215200) baseStart_215200 baseEnd_215200 := by
    simpa [prefixWord, tailWord_215200, baseEnd_215200] using wordTrace_append hprefix tailTrace_215200
  have hstable : (prefixWord ++ tailWord_215200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215200).length < 2 ^ (prefixWord ++ tailWord_215200).sum := by decide
  have hdescent : baseEnd_215200 < baseStart_215200 := by decide
  rcases family_descends (prefixWord ++ tailWord_215200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215234 : List Nat := [3, 5, 1, 1, 1, 1, 1, 4, 3]
def baseStart_215234 : Nat := 118140960795 + 215234 * 2 ^ 59
def prefixEnd_215234 : Nat := 4983230072969 + 3 ^ 40 * 215234 * 2
def baseEnd_215234 : Nat := 98238662391036559720145

theorem tailTrace_215234 : CollatzResearch.WordTrace tailWord_215234 prefixEnd_215234 98238662391036559720145 := by
  unfold tailWord_215234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1962557225562862971443189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5233485934834301257181837 1962557225562862971443189)
  ·
    refine ⟨183989739896518403572799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1962557225562862971443189 183989739896518403572799)
    ·
      refine ⟨275984609844777605359199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183989739896518403572799 275984609844777605359199)
      ·
        refine ⟨413976914767166408038799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275984609844777605359199 413976914767166408038799)
        ·
          refine ⟨620965372150749612058199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413976914767166408038799 620965372150749612058199)
          ·
            refine ⟨931448058226124418087299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620965372150749612058199 931448058226124418087299)
            ·
              refine ⟨1397172087339186627130949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 931448058226124418087299 1397172087339186627130949)
              ·
                refine ⟨261969766376097492587053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1397172087339186627130949 261969766376097492587053)
                ·
                  refine ⟨98238662391036559720145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261969766376097492587053 98238662391036559720145)
                  ·
                    rfl

theorem cell20_215234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_215234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215234 prefixEnd_215234 := by exact prefixLift 215234
  have htrace : WordTrace (prefixWord ++ tailWord_215234) baseStart_215234 baseEnd_215234 := by
    simpa [prefixWord, tailWord_215234, baseEnd_215234] using wordTrace_append hprefix tailTrace_215234
  have hstable : (prefixWord ++ tailWord_215234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215234).length < 2 ^ (prefixWord ++ tailWord_215234).sum := by decide
  have hdescent : baseEnd_215234 < baseStart_215234 := by decide
  rcases family_descends (prefixWord ++ tailWord_215234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215269 : List Nat := [1, 3, 1, 4, 2, 2, 3, 4]
def baseStart_215269 : Nat := 118140960795 + 215269 * 2 ^ 59
def prefixEnd_215269 : Nat := 4983230072969 + 3 ^ 40 * 215269 * 2
def baseEnd_215269 : Nat := 32751545781577331184445

theorem tailTrace_215269 : CollatzResearch.WordTrace tailWord_215269 prefixEnd_215269 32751545781577331184445 := by
  unfold tailWord_215269
  simp only [CollatzResearch.WordTrace]
  refine ⟨7851505457124652863296861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5234336971416435242197907 7851505457124652863296861)
  ·
    refine ⟨2944314546421744823736323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7851505457124652863296861 2944314546421744823736323)
    ·
      refine ⟨4416471819632617235604485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2944314546421744823736323 4416471819632617235604485)
      ·
        refine ⟨828088466181115731675841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4416471819632617235604485 828088466181115731675841)
        ·
          refine ⟨621066349635836798756881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 828088466181115731675841 621066349635836798756881)
          ·
            refine ⟨465799762226877599067661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 621066349635836798756881 465799762226877599067661)
            ·
              refine ⟨174674910835079099650373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 465799762226877599067661 174674910835079099650373)
              ·
                refine ⟨32751545781577331184445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174674910835079099650373 32751545781577331184445)
                ·
                  rfl

theorem cell20_215269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 4].length) (baseStart_215269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215269 prefixEnd_215269 := by exact prefixLift 215269
  have htrace : WordTrace (prefixWord ++ tailWord_215269) baseStart_215269 baseEnd_215269 := by
    simpa [prefixWord, tailWord_215269, baseEnd_215269] using wordTrace_append hprefix tailTrace_215269
  have hstable : (prefixWord ++ tailWord_215269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215269).length < 2 ^ (prefixWord ++ tailWord_215269).sum := by decide
  have hdescent : baseEnd_215269 < baseStart_215269 := by decide
  rcases family_descends (prefixWord ++ tailWord_215269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215297 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 5]
def baseStart_215297 : Nat := 118140960795 + 215297 * 2 ^ 59
def prefixEnd_215297 : Nat := 4983230072969 + 3 ^ 40 * 215297 * 2
def baseEnd_215297 : Nat := 98267417307688340619887

theorem tailTrace_215297 : CollatzResearch.WordTrace tailWord_215297 prefixEnd_215297 98267417307688340619887 := by
  unfold tailWord_215297
  simp only [CollatzResearch.WordTrace]
  refine ⟨7852526701023213645316145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5235017800682142430210763 7852526701023213645316145)
  ·
    refine ⟨5889395025767410233987109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7852526701023213645316145 5889395025767410233987109)
    ·
      refine ⟨1104261567331389418872583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5889395025767410233987109 1104261567331389418872583)
      ·
        refine ⟨1656392350997084128308875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1104261567331389418872583 1656392350997084128308875)
        ·
          refine ⟨2484588526495626192463313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1656392350997084128308875 2484588526495626192463313)
          ·
            refine ⟨1863441394871719644347485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2484588526495626192463313 1863441394871719644347485)
            ·
              refine ⟨698790523076894866630307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1863441394871719644347485 698790523076894866630307)
              ·
                refine ⟨1048185784615342299945461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698790523076894866630307 1048185784615342299945461)
                ·
                  refine ⟨98267417307688340619887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1048185784615342299945461 98267417307688340619887)
                  ·
                    rfl

theorem cell20_215297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_215297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215297 prefixEnd_215297 := by exact prefixLift 215297
  have htrace : WordTrace (prefixWord ++ tailWord_215297) baseStart_215297 baseEnd_215297 := by
    simpa [prefixWord, tailWord_215297, baseEnd_215297] using wordTrace_append hprefix tailTrace_215297
  have hstable : (prefixWord ++ tailWord_215297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215297).length < 2 ^ (prefixWord ++ tailWord_215297).sum := by decide
  have hdescent : baseEnd_215297 < baseStart_215297 := by decide
  rcases family_descends (prefixWord ++ tailWord_215297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215300 : List Nat := [2, 3, 2, 2, 3, 1, 2, 1, 4]
def baseStart_215300 : Nat := 118140960795 + 215300 * 2 ^ 59
def prefixEnd_215300 : Nat := 4983230072969 + 3 ^ 40 * 215300 * 2
def baseEnd_215300 : Nat := 98268786589433663519875

theorem tailTrace_215300 : CollatzResearch.WordTrace tailWord_215300 prefixEnd_215300 98268786589433663519875 := by
  unfold tailWord_215300
  simp only [CollatzResearch.WordTrace]
  refine ⟨3926318060006172578837677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5235090746674896771783569 3926318060006172578837677)
  ·
    refine ⟨1472369272502314717064129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3926318060006172578837677 1472369272502314717064129)
    ·
      refine ⟨1104276954376736037798097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1472369272502314717064129 1104276954376736037798097)
      ·
        refine ⟨828207715782552028348573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1104276954376736037798097 828207715782552028348573)
        ·
          refine ⟨310577893418457010630715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 828207715782552028348573 310577893418457010630715)
          ·
            refine ⟨465866840127685515946073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310577893418457010630715 465866840127685515946073)
            ·
              refine ⟨349400130095764136959555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465866840127685515946073 349400130095764136959555)
              ·
                refine ⟨524100195143646205439333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349400130095764136959555 524100195143646205439333)
                ·
                  refine ⟨98268786589433663519875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 524100195143646205439333 98268786589433663519875)
                  ·
                    rfl

theorem cell20_215300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_215300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215300 prefixEnd_215300 := by exact prefixLift 215300
  have htrace : WordTrace (prefixWord ++ tailWord_215300) baseStart_215300 baseEnd_215300 := by
    simpa [prefixWord, tailWord_215300, baseEnd_215300] using wordTrace_append hprefix tailTrace_215300
  have hstable : (prefixWord ++ tailWord_215300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215300).length < 2 ^ (prefixWord ++ tailWord_215300).sum := by decide
  have hdescent : baseEnd_215300 < baseStart_215300 := by decide
  rcases family_descends (prefixWord ++ tailWord_215300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215328 : List Nat := [2, 1, 1, 5, 2, 2, 1, 6]
def baseStart_215328 : Nat := 118140960795 + 215328 * 2 ^ 59
def prefixEnd_215328 : Nat := 4983230072969 + 3 ^ 40 * 215328 * 2
def baseEnd_215328 : Nat := 32760522184130003528809

theorem tailTrace_215328 : CollatzResearch.WordTrace tailWord_215328 prefixEnd_215328 32760522184130003528809 := by
  unfold tailWord_215328
  simp only [CollatzResearch.WordTrace]
  refine ⟨3926828681955452969847319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5235771575940603959796425 3926828681955452969847319)
  ·
    refine ⟨5890243022933179454770979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3926828681955452969847319 5890243022933179454770979)
    ·
      refine ⟨8835364534399769182156469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5890243022933179454770979 8835364534399769182156469)
      ·
        refine ⟨828315425099978360827169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8835364534399769182156469 828315425099978360827169)
        ·
          refine ⟨621236568824983770620377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 828315425099978360827169 621236568824983770620377)
          ·
            refine ⟨465927426618737827965283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 621236568824983770620377 465927426618737827965283)
            ·
              refine ⟨698891139928106741947925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465927426618737827965283 698891139928106741947925)
              ·
                refine ⟨32760522184130003528809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 698891139928106741947925 32760522184130003528809)
                ·
                  rfl

theorem cell20_215328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_215328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215328 prefixEnd_215328 := by exact prefixLift 215328
  have htrace : WordTrace (prefixWord ++ tailWord_215328) baseStart_215328 baseEnd_215328 := by
    simpa [prefixWord, tailWord_215328, baseEnd_215328] using wordTrace_append hprefix tailTrace_215328
  have hstable : (prefixWord ++ tailWord_215328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215328).length < 2 ^ (prefixWord ++ tailWord_215328).sum := by decide
  have hdescent : baseEnd_215328 < baseStart_215328 := by decide
  rcases family_descends (prefixWord ++ tailWord_215328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215345 : List Nat := [1, 2, 2, 3, 5, 1, 6]
def baseStart_215345 : Nat := 118140960795 + 215345 * 2 ^ 59
def prefixEnd_215345 : Nat := 4983230072969 + 3 ^ 40 * 215345 * 2
def baseEnd_215345 : Nat := 10921036201734834113299

theorem tailTrace_215345 : CollatzResearch.WordTrace tailWord_215345 prefixEnd_215345 10921036201734834113299 := by
  unfold tailWord_215345
  simp only [CollatzResearch.WordTrace]
  refine ⟨7854277404849317843063489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5236184936566211895375659 7854277404849317843063489)
  ·
    refine ⟨5890708053636988382297617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7854277404849317843063489 5890708053636988382297617)
    ·
      refine ⟨4418031040227741286723213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5890708053636988382297617 4418031040227741286723213)
      ·
        refine ⟨1656761640085402982521205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4418031040227741286723213 1656761640085402982521205)
        ·
          refine ⟨155321403758006529611363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1656761640085402982521205 155321403758006529611363)
          ·
            refine ⟨232982105637009794417045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155321403758006529611363 232982105637009794417045)
            ·
              refine ⟨10921036201734834113299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 232982105637009794417045 10921036201734834113299)
              ·
                rfl

theorem cell20_215345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 6].length) (baseStart_215345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215345 prefixEnd_215345 := by exact prefixLift 215345
  have htrace : WordTrace (prefixWord ++ tailWord_215345) baseStart_215345 baseEnd_215345 := by
    simpa [prefixWord, tailWord_215345, baseEnd_215345] using wordTrace_append hprefix tailTrace_215345
  have hstable : (prefixWord ++ tailWord_215345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215345).length < 2 ^ (prefixWord ++ tailWord_215345).sum := by decide
  have hdescent : baseEnd_215345 < baseStart_215345 := by decide
  rcases family_descends (prefixWord ++ tailWord_215345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215404 : List Nat := [2, 2, 1, 1, 7, 7]
def baseStart_215404 : Nat := 118140960795 + 215404 * 2 ^ 59
def prefixEnd_215404 : Nat := 4983230072969 + 3 ^ 40 * 215404 * 2
def baseEnd_215404 : Nat := 3641342778639686076029

theorem tailTrace_215404 : CollatzResearch.WordTrace tailWord_215404 prefixEnd_215404 3641342778639686076029 := by
  unfold tailWord_215404
  simp only [CollatzResearch.WordTrace]
  refine ⟨3928214655817785459730633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5237619541090380612974177 3928214655817785459730633)
  ·
    refine ⟨2946160991863339094797975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3928214655817785459730633 2946160991863339094797975)
    ·
      refine ⟨4419241487795008642196963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2946160991863339094797975 4419241487795008642196963)
      ·
        refine ⟨6628862231692512963295445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4419241487795008642196963 6628862231692512963295445)
        ·
          refine ⟨155363958555293272577237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 6628862231692512963295445 155363958555293272577237)
          ·
            refine ⟨3641342778639686076029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 155363958555293272577237 3641342778639686076029)
            ·
              rfl

theorem cell20_215404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 7].length) (baseStart_215404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215404 prefixEnd_215404 := by exact prefixLift 215404
  have htrace : WordTrace (prefixWord ++ tailWord_215404) baseStart_215404 baseEnd_215404 := by
    simpa [prefixWord, tailWord_215404, baseEnd_215404] using wordTrace_append hprefix tailTrace_215404
  have hstable : (prefixWord ++ tailWord_215404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215404).length < 2 ^ (prefixWord ++ tailWord_215404).sum := by decide
  have hdescent : baseEnd_215404 < baseStart_215404 := by decide
  rcases family_descends (prefixWord ++ tailWord_215404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215473 : List Nat := [1, 2, 2, 4, 1, 3, 2, 1, 4]
def baseStart_215473 : Nat := 118140960795 + 215473 * 2 ^ 59
def prefixEnd_215473 : Nat := 4983230072969 + 3 ^ 40 * 215473 * 2
def baseEnd_215473 : Nat := 98347748503413950752501

theorem tailTrace_215473 : CollatzResearch.WordTrace tailWord_215473 prefixEnd_215473 98347748503413950752501 := by
  unfold tailWord_215473
  simp only [CollatzResearch.WordTrace]
  refine ⟨7858945948385595703723073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5239297298923730469148715 7858945948385595703723073)
  ·
    refine ⟨5894209461289196777792305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7858945948385595703723073 5894209461289196777792305)
    ·
      refine ⟨4420657095966897583344229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5894209461289196777792305 4420657095966897583344229)
      ·
        refine ⟨828873205493793296877043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4420657095966897583344229 828873205493793296877043)
        ·
          refine ⟨1243309808240689945315565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 828873205493793296877043 1243309808240689945315565)
          ·
            refine ⟨466241178090258729493337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1243309808240689945315565 466241178090258729493337)
            ·
              refine ⟨349680883567694047120003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466241178090258729493337 349680883567694047120003)
              ·
                refine ⟨524521325351541070680005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349680883567694047120003 524521325351541070680005)
                ·
                  refine ⟨98347748503413950752501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 524521325351541070680005 98347748503413950752501)
                  ·
                    rfl

theorem cell20_215473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_215473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215473 prefixEnd_215473 := by exact prefixLift 215473
  have htrace : WordTrace (prefixWord ++ tailWord_215473) baseStart_215473 baseEnd_215473 := by
    simpa [prefixWord, tailWord_215473, baseEnd_215473] using wordTrace_append hprefix tailTrace_215473
  have hstable : (prefixWord ++ tailWord_215473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215473).length < 2 ^ (prefixWord ++ tailWord_215473).sum := by decide
  have hdescent : baseEnd_215473 < baseStart_215473 := by decide
  rcases family_descends (prefixWord ++ tailWord_215473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215538 : List Nat := [3, 2, 1, 4, 2, 2, 2, 1, 3]
def baseStart_215538 : Nat := 118140960795 + 215538 * 2 ^ 59
def prefixEnd_215538 : Nat := 4983230072969 + 3 ^ 40 * 215538 * 2
def baseEnd_215538 : Nat := 98377416274562613585569

theorem tailTrace_215538 : CollatzResearch.WordTrace tailWord_215538 prefixEnd_215538 98377416274562613585569 := by
  unfold tailWord_215538
  simp only [CollatzResearch.WordTrace]
  refine ⟨1965329173287527951209817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5240877795433407869892845 1965329173287527951209817)
  ·
    refine ⟨1473996879965645963407363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1965329173287527951209817 1473996879965645963407363)
    ·
      refine ⟨2210995319948468945111045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1473996879965645963407363 2210995319948468945111045)
      ·
        refine ⟨414561622490337927208321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2210995319948468945111045 414561622490337927208321)
        ·
          refine ⟨310921216867753445406241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414561622490337927208321 310921216867753445406241)
          ·
            refine ⟨233190912650815084054681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310921216867753445406241 233190912650815084054681)
            ·
              refine ⟨174893184488111313041011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233190912650815084054681 174893184488111313041011)
              ·
                refine ⟨262339776732166969561517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174893184488111313041011 262339776732166969561517)
                ·
                  refine ⟨98377416274562613585569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262339776732166969561517 98377416274562613585569)
                  ·
                    rfl

theorem cell20_215538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_215538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215538 prefixEnd_215538 := by exact prefixLift 215538
  have htrace : WordTrace (prefixWord ++ tailWord_215538) baseStart_215538 baseEnd_215538 := by
    simpa [prefixWord, tailWord_215538, baseEnd_215538] using wordTrace_append hprefix tailTrace_215538
  have hstable : (prefixWord ++ tailWord_215538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215538).length < 2 ^ (prefixWord ++ tailWord_215538).sum := by decide
  have hdescent : baseEnd_215538 < baseStart_215538 := by decide
  rcases family_descends (prefixWord ++ tailWord_215538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215539 : List Nat := [1, 1, 1, 2, 2, 2, 6, 5]
def baseStart_215539 : Nat := 118140960795 + 215539 * 2 ^ 59
def prefixEnd_215539 : Nat := 4983230072969 + 3 ^ 40 * 215539 * 2
def baseEnd_215539 : Nat := 32792624233937018184077

theorem tailTrace_215539 : CollatzResearch.WordTrace tailWord_215539 prefixEnd_215539 32792624233937018184077 := by
  unfold tailWord_215539
  simp only [CollatzResearch.WordTrace]
  refine ⟨7861353166146488975625671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5240902110764325983750447 7861353166146488975625671)
  ·
    refine ⟨11792029749219733463438507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7861353166146488975625671 11792029749219733463438507)
    ·
      refine ⟨17688044623829600195157761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11792029749219733463438507 17688044623829600195157761)
      ·
        refine ⟨13266033467872200146368321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17688044623829600195157761 13266033467872200146368321)
        ·
          refine ⟨9949525100904150109776241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13266033467872200146368321 9949525100904150109776241)
          ·
            refine ⟨7462143825678112582332181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9949525100904150109776241 7462143825678112582332181)
            ·
              refine ⟨349787991828661527296821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7462143825678112582332181 349787991828661527296821)
              ·
                refine ⟨32792624233937018184077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 349787991828661527296821 32792624233937018184077)
                ·
                  rfl

theorem cell20_215539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 5].length) (baseStart_215539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215539 prefixEnd_215539 := by exact prefixLift 215539
  have htrace : WordTrace (prefixWord ++ tailWord_215539) baseStart_215539 baseEnd_215539 := by
    simpa [prefixWord, tailWord_215539, baseEnd_215539] using wordTrace_append hprefix tailTrace_215539
  have hstable : (prefixWord ++ tailWord_215539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215539).length < 2 ^ (prefixWord ++ tailWord_215539).sum := by decide
  have hdescent : baseEnd_215539 < baseStart_215539 := by decide
  rcases family_descends (prefixWord ++ tailWord_215539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215542 : List Nat := [5, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_215542 : Nat := 118140960795 + 215542 * 2 ^ 59
def prefixEnd_215542 : Nat := 4983230072969 + 3 ^ 40 * 215542 * 2
def baseEnd_215542 : Nat := 98379241983556377452219

theorem tailTrace_215542 : CollatzResearch.WordTrace tailWord_215542 prefixEnd_215542 98379241983556377452219 := by
  unfold tailWord_215542
  simp only [CollatzResearch.WordTrace]
  refine ⟨491341411570976280499055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5240975056757080325323253 491341411570976280499055)
  ·
    refine ⟨737012117356464420748583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 491341411570976280499055 737012117356464420748583)
    ·
      refine ⟨1105518176034696631122875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 737012117356464420748583 1105518176034696631122875)
      ·
        refine ⟨1658277264052044946684313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1105518176034696631122875 1658277264052044946684313)
        ·
          refine ⟨1243707948039033710013235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1658277264052044946684313 1243707948039033710013235)
          ·
            refine ⟨1865561922058550565019853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243707948039033710013235 1865561922058550565019853)
            ·
              refine ⟨699585720771956461882445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1865561922058550565019853 699585720771956461882445)
              ·
                refine ⟨262344645289483673205917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 699585720771956461882445 262344645289483673205917)
                ·
                  refine ⟨98379241983556377452219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262344645289483673205917 98379241983556377452219)
                  ·
                    rfl

theorem cell20_215542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_215542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215542 prefixEnd_215542 := by exact prefixLift 215542
  have htrace : WordTrace (prefixWord ++ tailWord_215542) baseStart_215542 baseEnd_215542 := by
    simpa [prefixWord, tailWord_215542, baseEnd_215542] using wordTrace_append hprefix tailTrace_215542
  have hstable : (prefixWord ++ tailWord_215542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215542).length < 2 ^ (prefixWord ++ tailWord_215542).sum := by decide
  have hdescent : baseEnd_215542 < baseStart_215542 := by decide
  rcases family_descends (prefixWord ++ tailWord_215542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215546 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_215546 : Nat := 118140960795 + 215546 * 2 ^ 59
def prefixEnd_215546 : Nat := 4983230072969 + 3 ^ 40 * 215546 * 2
def baseEnd_215546 : Nat := 98381067692550141318869

theorem tailTrace_215546 : CollatzResearch.WordTrace tailWord_215546 prefixEnd_215546 98381067692550141318869 := by
  unfold tailWord_215546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1965402119280282292782623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5241072318080752780753661 1965402119280282292782623)
  ·
    refine ⟨2948103178920423439173935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1965402119280282292782623 2948103178920423439173935)
    ·
      refine ⟨4422154768380635158760903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2948103178920423439173935 4422154768380635158760903)
      ·
        refine ⟨6633232152570952738141355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4422154768380635158760903 6633232152570952738141355)
        ·
          refine ⟨9949848228856429107212033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6633232152570952738141355 9949848228856429107212033)
          ·
            refine ⟨7462386171642321830409025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9949848228856429107212033 7462386171642321830409025)
            ·
              refine ⟨5596789628731741372806769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7462386171642321830409025 5596789628731741372806769)
              ·
                refine ⟨4197592221548806029605077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5596789628731741372806769 4197592221548806029605077)
                ·
                  refine ⟨98381067692550141318869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4197592221548806029605077 98381067692550141318869)
                  ·
                    rfl

theorem cell20_215546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_215546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215546 prefixEnd_215546 := by exact prefixLift 215546
  have htrace : WordTrace (prefixWord ++ tailWord_215546) baseStart_215546 baseEnd_215546 := by
    simpa [prefixWord, tailWord_215546, baseEnd_215546] using wordTrace_append hprefix tailTrace_215546
  have hstable : (prefixWord ++ tailWord_215546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215546).length < 2 ^ (prefixWord ++ tailWord_215546).sum := by decide
  have hdescent : baseEnd_215546 < baseStart_215546 := by decide
  rcases family_descends (prefixWord ++ tailWord_215546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215556 : List Nat := [2, 3, 2, 3, 1, 1, 2, 6]
def baseStart_215556 : Nat := 118140960795 + 215556 * 2 ^ 59
def prefixEnd_215556 : Nat := 4983230072969 + 3 ^ 40 * 215556 * 2
def baseEnd_215556 : Nat := 32795210655011516995165

theorem tailTrace_215556 : CollatzResearch.WordTrace tailWord_215556 prefixEnd_215556 32795210655011516995165 := by
  unfold tailWord_215556
  simp only [CollatzResearch.WordTrace]
  refine ⟨3930986603542450439497261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5241315471389933919329681 3930986603542450439497261)
  ·
    refine ⟨1474119976328418914811473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3930986603542450439497261 1474119976328418914811473)
    ·
      refine ⟨1105589982246314186108605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1474119976328418914811473 1105589982246314186108605)
      ·
        refine ⟨414596243342367819790727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1105589982246314186108605 414596243342367819790727)
        ·
          refine ⟨621894365013551729686091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414596243342367819790727 621894365013551729686091)
          ·
            refine ⟨932841547520327594529137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621894365013551729686091 932841547520327594529137)
            ·
              refine ⟨699631160640245695896853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 932841547520327594529137 699631160640245695896853)
              ·
                refine ⟨32795210655011516995165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 699631160640245695896853 32795210655011516995165)
                ·
                  rfl

theorem cell20_215556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_215556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215556 prefixEnd_215556 := by exact prefixLift 215556
  have htrace : WordTrace (prefixWord ++ tailWord_215556) baseStart_215556 baseEnd_215556 := by
    simpa [prefixWord, tailWord_215556, baseEnd_215556] using wordTrace_append hprefix tailTrace_215556
  have hstable : (prefixWord ++ tailWord_215556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215556).length < 2 ^ (prefixWord ++ tailWord_215556).sum := by decide
  have hdescent : baseEnd_215556 < baseStart_215556 := by decide
  rcases family_descends (prefixWord ++ tailWord_215556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215580 : List Nat := [2, 2, 3, 1, 2, 3, 2, 2, 3]
def baseStart_215580 : Nat := 118140960795 + 215580 * 2 ^ 59
def prefixEnd_215580 : Nat := 4983230072969 + 3 ^ 40 * 215580 * 2
def baseEnd_215580 : Nat := 98396586218997134185397

theorem tailTrace_215580 : CollatzResearch.WordTrace tailWord_215580 prefixEnd_215580 98396586218997134185397 := by
  unfold tailWord_215580
  simp only [CollatzResearch.WordTrace]
  refine ⟨3931424279498976488934097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5241899039331968651912129 3931424279498976488934097)
  ·
    refine ⟨2948568209624232366700573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3931424279498976488934097 2948568209624232366700573)
    ·
      refine ⟨1105713078609087137512715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2948568209624232366700573 1105713078609087137512715)
      ·
        refine ⟨1658569617913630706269073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1105713078609087137512715 1658569617913630706269073)
        ·
          refine ⟨1243927213435223029701805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1658569617913630706269073 1243927213435223029701805)
          ·
            refine ⟨466472705038208636138177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1243927213435223029701805 466472705038208636138177)
            ·
              refine ⟨349854528778656477103633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466472705038208636138177 349854528778656477103633)
              ·
                refine ⟨262390896583992357827725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349854528778656477103633 262390896583992357827725)
                ·
                  refine ⟨98396586218997134185397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262390896583992357827725 98396586218997134185397)
                  ·
                    rfl

theorem cell20_215580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_215580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215580 prefixEnd_215580 := by exact prefixLift 215580
  have htrace : WordTrace (prefixWord ++ tailWord_215580) baseStart_215580 baseEnd_215580 := by
    simpa [prefixWord, tailWord_215580, baseEnd_215580] using wordTrace_append hprefix tailTrace_215580
  have hstable : (prefixWord ++ tailWord_215580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215580).length < 2 ^ (prefixWord ++ tailWord_215580).sum := by decide
  have hdescent : baseEnd_215580 < baseStart_215580 := by decide
  rcases family_descends (prefixWord ++ tailWord_215580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215594 : List Nat := [3, 1, 4, 1, 1, 2, 3, 5]
def baseStart_215594 : Nat := 118140960795 + 215594 * 2 ^ 59
def prefixEnd_215594 : Nat := 4983230072969 + 3 ^ 40 * 215594 * 2
def baseEnd_215594 : Nat := 32800992066825102572891

theorem tailTrace_215594 : CollatzResearch.WordTrace tailWord_215594 prefixEnd_215594 32800992066825102572891 := by
  unfold tailWord_215594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1965839795236808342219459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5242239453964822245918557 1965839795236808342219459)
  ·
    refine ⟨2948759692855212513329189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1965839795236808342219459 2948759692855212513329189)
    ·
      refine ⟨552892442410352346249223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2948759692855212513329189 552892442410352346249223)
      ·
        refine ⟨829338663615528519373835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552892442410352346249223 829338663615528519373835)
        ·
          refine ⟨1244007995423292779060753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829338663615528519373835 1244007995423292779060753)
          ·
            refine ⟨933005996567469584295565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1244007995423292779060753 933005996567469584295565)
            ·
              refine ⟨349877248712801094110837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 933005996567469584295565 349877248712801094110837)
              ·
                refine ⟨32800992066825102572891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 349877248712801094110837 32800992066825102572891)
                ·
                  rfl

theorem cell20_215594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_215594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215594 prefixEnd_215594 := by exact prefixLift 215594
  have htrace : WordTrace (prefixWord ++ tailWord_215594) baseStart_215594 baseEnd_215594 := by
    simpa [prefixWord, tailWord_215594, baseEnd_215594] using wordTrace_append hprefix tailTrace_215594
  have hstable : (prefixWord ++ tailWord_215594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215594).length < 2 ^ (prefixWord ++ tailWord_215594).sum := by decide
  have hdescent : baseEnd_215594 < baseStart_215594 := by decide
  rcases family_descends (prefixWord ++ tailWord_215594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215601 : List Nat := [1, 2, 2, 3, 1, 1, 4, 3, 3]
def baseStart_215601 : Nat := 118140960795 + 215601 * 2 ^ 59
def prefixEnd_215601 : Nat := 4983230072969 + 3 ^ 40 * 215601 * 2
def baseEnd_215601 : Nat := 98406171191214394485311

theorem tailTrace_215601 : CollatzResearch.WordTrace tailWord_215601 prefixEnd_215601 98406171191214394485311 := by
  unfold tailWord_215601
  simp only [CollatzResearch.WordTrace]
  refine ⟨7863614491921873564382657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5242409661281249042921771 7863614491921873564382657)
  ·
    refine ⟨5897710868941405173286993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7863614491921873564382657 5897710868941405173286993)
    ·
      refine ⟨4423283151706053879965245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5897710868941405173286993 4423283151706053879965245)
      ·
        refine ⟨1658731181889770204986967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4423283151706053879965245 1658731181889770204986967)
        ·
          refine ⟨2488096772834655307480451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1658731181889770204986967 2488096772834655307480451)
          ·
            refine ⟨3732145159251982961220677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2488096772834655307480451 3732145159251982961220677)
            ·
              refine ⟨699777217359746805228877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3732145159251982961220677 699777217359746805228877)
              ·
                refine ⟨262416456509905051960829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 699777217359746805228877 262416456509905051960829)
                ·
                  refine ⟨98406171191214394485311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262416456509905051960829 98406171191214394485311)
                  ·
                    rfl

theorem cell20_215601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_215601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215601 prefixEnd_215601 := by exact prefixLift 215601
  have htrace : WordTrace (prefixWord ++ tailWord_215601) baseStart_215601 baseEnd_215601 := by
    simpa [prefixWord, tailWord_215601, baseEnd_215601] using wordTrace_append hprefix tailTrace_215601
  have hstable : (prefixWord ++ tailWord_215601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215601).length < 2 ^ (prefixWord ++ tailWord_215601).sum := by decide
  have hdescent : baseEnd_215601 < baseStart_215601 := by decide
  rcases family_descends (prefixWord ++ tailWord_215601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215608 : List Nat := [2, 1, 2, 1, 4, 1, 3, 2, 4]
def baseStart_215608 : Nat := 118140960795 + 215608 * 2 ^ 59
def prefixEnd_215608 : Nat := 4983230072969 + 3 ^ 40 * 215608 * 2
def baseEnd_215608 : Nat := 98409366181953481251949

theorem tailTrace_215608 : CollatzResearch.WordTrace tailWord_215608 prefixEnd_215608 98409366181953481251949 := by
  unfold tailWord_215608
  simp only [CollatzResearch.WordTrace]
  refine ⟨3931934901448256879943739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5242579868597675839924985 3931934901448256879943739)
  ·
    refine ⟨5897902352172385319915609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3931934901448256879943739 5897902352172385319915609)
    ·
      refine ⟨4423426764129288989936707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5897902352172385319915609 4423426764129288989936707)
      ·
        refine ⟨6635140146193933484905061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4423426764129288989936707 6635140146193933484905061)
        ·
          refine ⟨1244088777411362528419699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6635140146193933484905061 1244088777411362528419699)
          ·
            refine ⟨1866133166117043792629549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244088777411362528419699 1866133166117043792629549)
            ·
              refine ⟨699799937293891422236081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1866133166117043792629549 699799937293891422236081)
              ·
                refine ⟨524849952970418566677061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 699799937293891422236081 524849952970418566677061)
                ·
                  refine ⟨98409366181953481251949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 524849952970418566677061 98409366181953481251949)
                  ·
                    rfl

theorem cell20_215608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_215608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215608 prefixEnd_215608 := by exact prefixLift 215608
  have htrace : WordTrace (prefixWord ++ tailWord_215608) baseStart_215608 baseEnd_215608 := by
    simpa [prefixWord, tailWord_215608, baseEnd_215608] using wordTrace_append hprefix tailTrace_215608
  have hstable : (prefixWord ++ tailWord_215608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215608).length < 2 ^ (prefixWord ++ tailWord_215608).sum := by decide
  have hdescent : baseEnd_215608 < baseStart_215608 := by decide
  rcases family_descends (prefixWord ++ tailWord_215608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215666 : List Nat := [3, 2, 1, 2, 5, 1, 2, 4]
def baseStart_215666 : Nat := 118140960795 + 215666 * 2 ^ 59
def prefixEnd_215666 : Nat := 4983230072969 + 3 ^ 40 * 215666 * 2
def baseEnd_215666 : Nat := 32811946320787685772793

theorem tailTrace_215666 : CollatzResearch.WordTrace tailWord_215666 prefixEnd_215666 32811946320787685772793 := by
  unfold tailWord_215666
  simp only [CollatzResearch.WordTrace]
  refine ⟨1966496309171597416374713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5243990157790926443665901 1966496309171597416374713)
  ·
    refine ⟨1474872231878698062281035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1966496309171597416374713 1474872231878698062281035)
    ·
      refine ⟨2212308347818047093421553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1474872231878698062281035 2212308347818047093421553)
      ·
        refine ⟨1659231260863535320066165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2212308347818047093421553 1659231260863535320066165)
        ·
          refine ⟨155552930705956436256203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1659231260863535320066165 155552930705956436256203)
          ·
            refine ⟨233329396058934654384305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155552930705956436256203 233329396058934654384305)
            ·
              refine ⟨174997047044200990788229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233329396058934654384305 174997047044200990788229)
              ·
                refine ⟨32811946320787685772793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174997047044200990788229 32811946320787685772793)
                ·
                  rfl

theorem cell20_215666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_215666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215666 prefixEnd_215666 := by exact prefixLift 215666
  have htrace : WordTrace (prefixWord ++ tailWord_215666) baseStart_215666 baseEnd_215666 := by
    simpa [prefixWord, tailWord_215666, baseEnd_215666] using wordTrace_append hprefix tailTrace_215666
  have hstable : (prefixWord ++ tailWord_215666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215666).length < 2 ^ (prefixWord ++ tailWord_215666).sum := by decide
  have hdescent : baseEnd_215666 < baseStart_215666 := by decide
  rcases family_descends (prefixWord ++ tailWord_215666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215667 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 6]
def baseStart_215667 : Nat := 118140960795 + 215667 * 2 ^ 59
def prefixEnd_215667 : Nat := 4983230072969 + 3 ^ 40 * 215667 * 2
def baseEnd_215667 : Nat := 98436295389611498285041

theorem tailTrace_215667 : CollatzResearch.WordTrace tailWord_215667 prefixEnd_215667 98436295389611498285041 := by
  unfold tailWord_215667
  simp only [CollatzResearch.WordTrace]
  refine ⟨7866021709682766836285255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5244014473121844557523503 7866021709682766836285255)
  ·
    refine ⟨11799032564524150254427883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7866021709682766836285255 11799032564524150254427883)
    ·
      refine ⟨17698548846786225381641825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11799032564524150254427883 17698548846786225381641825)
      ·
        refine ⟨13273911635089669036231369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17698548846786225381641825 13273911635089669036231369)
        ·
          refine ⟨9955433726317251777173527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13273911635089669036231369 9955433726317251777173527)
          ·
            refine ⟨14933150589475877665760291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9955433726317251777173527 14933150589475877665760291)
            ·
              refine ⟨22399725884213816498640437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14933150589475877665760291 22399725884213816498640437)
              ·
                refine ⟨2099974301645045296747541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22399725884213816498640437 2099974301645045296747541)
                ·
                  refine ⟨98436295389611498285041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2099974301645045296747541 98436295389611498285041)
                  ·
                    rfl

theorem cell20_215667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_215667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215667 prefixEnd_215667 := by exact prefixLift 215667
  have htrace : WordTrace (prefixWord ++ tailWord_215667) baseStart_215667 baseEnd_215667 := by
    simpa [prefixWord, tailWord_215667, baseEnd_215667] using wordTrace_append hprefix tailTrace_215667
  have hstable : (prefixWord ++ tailWord_215667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215667).length < 2 ^ (prefixWord ++ tailWord_215667).sum := by decide
  have hdescent : baseEnd_215667 < baseStart_215667 := by decide
  rcases family_descends (prefixWord ++ tailWord_215667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215680 : List Nat := [2, 1, 1, 2, 1, 7, 1, 3, 2]
def baseStart_215680 : Nat := 118140960795 + 215680 * 2 ^ 59
def prefixEnd_215680 : Nat := 4983230072969 + 3 ^ 40 * 215680 * 2
def baseEnd_215680 : Nat := 98442228943841230851655

theorem tailTrace_215680 : CollatzResearch.WordTrace tailWord_215680 prefixEnd_215680 98442228943841230851655 := by
  unfold tailWord_215680
  simp only [CollatzResearch.WordTrace]
  refine ⟨3933247929317835028254247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5244330572423780037672329 3933247929317835028254247)
  ·
    refine ⟨5899871893976752542381371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3933247929317835028254247 5899871893976752542381371)
    ·
      refine ⟨8849807840965128813572057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5899871893976752542381371 8849807840965128813572057)
      ·
        refine ⟨6637355880723846610179043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8849807840965128813572057 6637355880723846610179043)
        ·
          refine ⟨9956033821085769915268565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6637355880723846610179043 9956033821085769915268565)
          ·
            refine ⟨233344542681697732389107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 9956033821085769915268565 233344542681697732389107)
            ·
              refine ⟨350016814022546598583661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233344542681697732389107 350016814022546598583661)
              ·
                refine ⟨131256305258454974468873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 350016814022546598583661 131256305258454974468873)
                ·
                  refine ⟨98442228943841230851655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131256305258454974468873 98442228943841230851655)
                  ·
                    rfl

theorem cell20_215680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 2].length) (baseStart_215680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215680 prefixEnd_215680 := by exact prefixLift 215680
  have htrace : WordTrace (prefixWord ++ tailWord_215680) baseStart_215680 baseEnd_215680 := by
    simpa [prefixWord, tailWord_215680, baseEnd_215680] using wordTrace_append hprefix tailTrace_215680
  have hstable : (prefixWord ++ tailWord_215680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215680).length < 2 ^ (prefixWord ++ tailWord_215680).sum := by decide
  have hdescent : baseEnd_215680 < baseStart_215680 := by decide
  rcases family_descends (prefixWord ++ tailWord_215680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215708 : List Nat := [2, 2, 3, 2, 2, 2, 2, 5]
def baseStart_215708 : Nat := 118140960795 + 215708 * 2 ^ 59
def prefixEnd_215708 : Nat := 4983230072969 + 3 ^ 40 * 215708 * 2
def baseEnd_215708 : Nat := 32818336302265859306069

theorem tailTrace_215708 : CollatzResearch.WordTrace tailWord_215708 prefixEnd_215708 32818336302265859306069 := by
  unfold tailWord_215708
  simp only [CollatzResearch.WordTrace]
  refine ⟨3933758551267115419263889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5245011401689487225685185 3933758551267115419263889)
  ·
    refine ⟨2950318913450336564447917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3933758551267115419263889 2950318913450336564447917)
    ·
      refine ⟨1106369592543876211667969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2950318913450336564447917 1106369592543876211667969)
      ·
        refine ⟨829777194407907158750977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1106369592543876211667969 829777194407907158750977)
        ·
          refine ⟨622332895805930369063233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 829777194407907158750977 622332895805930369063233)
          ·
            refine ⟨466749671854447776797425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622332895805930369063233 466749671854447776797425)
            ·
              refine ⟨350062253890835832598069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466749671854447776797425 350062253890835832598069)
              ·
                refine ⟨32818336302265859306069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 350062253890835832598069 32818336302265859306069)
                ·
                  rfl

theorem cell20_215708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_215708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215708 prefixEnd_215708 := by exact prefixLift 215708
  have htrace : WordTrace (prefixWord ++ tailWord_215708) baseStart_215708 baseEnd_215708 := by
    simpa [prefixWord, tailWord_215708, baseEnd_215708] using wordTrace_append hprefix tailTrace_215708
  have hstable : (prefixWord ++ tailWord_215708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215708).length < 2 ^ (prefixWord ++ tailWord_215708).sum := by decide
  have hdescent : baseEnd_215708 < baseStart_215708 := by decide
  rcases family_descends (prefixWord ++ tailWord_215708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215746 : List Nat := [3, 5, 1, 11]
def baseStart_215746 : Nat := 118140960795 + 215746 * 2 ^ 59
def prefixEnd_215746 : Nat := 4983230072969 + 3 ^ 40 * 215746 * 2
def baseEnd_215746 : Nat := 405236021161474628195

theorem tailTrace_215746 : CollatzResearch.WordTrace tailWord_215746 prefixEnd_215746 405236021161474628195 := by
  unfold tailWord_215746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1967225769099140832102773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5245935384264375552274061 1967225769099140832102773)
  ·
    refine ⟨184427415853044453009635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1967225769099140832102773 184427415853044453009635)
    ·
      refine ⟨276641123779566679514453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184427415853044453009635 276641123779566679514453)
      ·
        refine ⟨405236021161474628195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 276641123779566679514453 405236021161474628195)
        ·
          rfl

theorem cell20_215746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 11].length) (baseStart_215746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215746 prefixEnd_215746 := by exact prefixLift 215746
  have htrace : WordTrace (prefixWord ++ tailWord_215746) baseStart_215746 baseEnd_215746 := by
    simpa [prefixWord, tailWord_215746, baseEnd_215746] using wordTrace_append hprefix tailTrace_215746
  have hstable : (prefixWord ++ tailWord_215746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215746).length < 2 ^ (prefixWord ++ tailWord_215746).sum := by decide
  have hdescent : baseEnd_215746 < baseStart_215746 := by decide
  rcases family_descends (prefixWord ++ tailWord_215746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215756 : List Nat := [2, 2, 1, 5, 1, 2, 1, 4, 2]
def baseStart_215756 : Nat := 118140960795 + 215756 * 2 ^ 59
def prefixEnd_215756 : Nat := 4983230072969 + 3 ^ 40 * 215756 * 2
def baseEnd_215756 : Nat := 98476917414722744318011

theorem tailTrace_215756 : CollatzResearch.WordTrace tailWord_215756 prefixEnd_215756 98476917414722744318011 := by
  unfold tailWord_215756
  simp only [CollatzResearch.WordTrace]
  refine ⟨3934633903180167518137561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5246178537573556690850081 3934633903180167518137561)
  ·
    refine ⟨2950975427385125638603171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3934633903180167518137561 2950975427385125638603171)
    ·
      refine ⟨4426463141077688457904757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2950975427385125638603171 4426463141077688457904757)
      ·
        refine ⟨414980919476033292928571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4426463141077688457904757 414980919476033292928571)
        ·
          refine ⟨622471379214049939392857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414980919476033292928571 622471379214049939392857)
          ·
            refine ⟨466853534410537454544643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622471379214049939392857 466853534410537454544643)
            ·
              refine ⟨700280301615806181816965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466853534410537454544643 700280301615806181816965)
              ·
                refine ⟨131302556552963659090681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 700280301615806181816965 131302556552963659090681)
                ·
                  refine ⟨98476917414722744318011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131302556552963659090681 98476917414722744318011)
                  ·
                    rfl

theorem cell20_215756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_215756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215756 prefixEnd_215756 := by exact prefixLift 215756
  have htrace : WordTrace (prefixWord ++ tailWord_215756) baseStart_215756 baseEnd_215756 := by
    simpa [prefixWord, tailWord_215756, baseEnd_215756] using wordTrace_append hprefix tailTrace_215756
  have hstable : (prefixWord ++ tailWord_215756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215756).length < 2 ^ (prefixWord ++ tailWord_215756).sum := by decide
  have hdescent : baseEnd_215756 < baseStart_215756 := by decide
  rcases family_descends (prefixWord ++ tailWord_215756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215767 : List Nat := [1, 1, 3, 2, 1, 4, 3, 5]
def baseStart_215767 : Nat := 118140960795 + 215767 * 2 ^ 59
def prefixEnd_215767 : Nat := 4983230072969 + 3 ^ 40 * 215767 * 2
def baseEnd_215767 : Nat := 32827312704818531650433

theorem tailTrace_215767 : CollatzResearch.WordTrace tailWord_215767 prefixEnd_215767 32827312704818531650433 := by
  unfold tailWord_215767
  simp only [CollatzResearch.WordTrace]
  refine ⟨7869669009320483914925555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5246446006213655943283703 7869669009320483914925555)
  ·
    refine ⟨11804503513980725872388333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7869669009320483914925555 11804503513980725872388333)
    ·
      refine ⟨4426688817742772202145625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11804503513980725872388333 4426688817742772202145625)
      ·
        refine ⟨3320016613307079151609219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4426688817742772202145625 3320016613307079151609219)
        ·
          refine ⟨4980024919960618727413829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3320016613307079151609219 4980024919960618727413829)
          ·
            refine ⟨933754672492616011390093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4980024919960618727413829 933754672492616011390093)
            ·
              refine ⟨350158002184731004271285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 933754672492616011390093 350158002184731004271285)
              ·
                refine ⟨32827312704818531650433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 350158002184731004271285 32827312704818531650433)
                ·
                  rfl

theorem cell20_215767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 5].length) (baseStart_215767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215767 prefixEnd_215767 := by exact prefixLift 215767
  have htrace : WordTrace (prefixWord ++ tailWord_215767) baseStart_215767 baseEnd_215767 := by
    simpa [prefixWord, tailWord_215767, baseEnd_215767] using wordTrace_append hprefix tailTrace_215767
  have hstable : (prefixWord ++ tailWord_215767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215767).length < 2 ^ (prefixWord ++ tailWord_215767).sum := by decide
  have hdescent : baseEnd_215767 < baseStart_215767 := by decide
  rcases family_descends (prefixWord ++ tailWord_215767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215794 : List Nat := [3, 2, 1, 3, 1, 3, 2, 3, 2]
def baseStart_215794 : Nat := 118140960795 + 215794 * 2 ^ 59
def prefixEnd_215794 : Nat := 4983230072969 + 3 ^ 40 * 215794 * 2
def baseEnd_215794 : Nat := 98494261650163501051189

theorem tailTrace_215794 : CollatzResearch.WordTrace tailWord_215794 prefixEnd_215794 98494261650163501051189 := by
  unfold tailWord_215794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1967663445055666881539609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5247102520148445017438957 1967663445055666881539609)
  ·
    refine ⟨1475747583791750161154707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1967663445055666881539609 1475747583791750161154707)
    ·
      refine ⟨2213621375687625241732061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1475747583791750161154707 2213621375687625241732061)
      ·
        refine ⟨830108015882859465649523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2213621375687625241732061 830108015882859465649523)
        ·
          refine ⟨1245162023824289198474285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830108015882859465649523 1245162023824289198474285)
          ·
            refine ⟨466935758934108449427857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1245162023824289198474285 466935758934108449427857)
            ·
              refine ⟨350201819200581337070893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466935758934108449427857 350201819200581337070893)
              ·
                refine ⟨131325682200218001401585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 350201819200581337070893 131325682200218001401585)
                ·
                  refine ⟨98494261650163501051189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131325682200218001401585 98494261650163501051189)
                  ·
                    rfl

theorem cell20_215794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_215794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215794 prefixEnd_215794 := by exact prefixLift 215794
  have htrace : WordTrace (prefixWord ++ tailWord_215794) baseStart_215794 baseEnd_215794 := by
    simpa [prefixWord, tailWord_215794, baseEnd_215794] using wordTrace_append hprefix tailTrace_215794
  have hstable : (prefixWord ++ tailWord_215794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215794).length < 2 ^ (prefixWord ++ tailWord_215794).sum := by decide
  have hdescent : baseEnd_215794 < baseStart_215794 := by decide
  rcases family_descends (prefixWord ++ tailWord_215794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215798 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_215798 : Nat := 118140960795 + 215798 * 2 ^ 59
def prefixEnd_215798 : Nat := 4983230072969 + 3 ^ 40 * 215798 * 2
def baseEnd_215798 : Nat := 98496087359157264917839

theorem tailTrace_215798 : CollatzResearch.WordTrace tailWord_215798 prefixEnd_215798 98496087359157264917839 := by
  unfold tailWord_215798
  simp only [CollatzResearch.WordTrace]
  refine ⟨491924979513011013081503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5247199781472117472869365 491924979513011013081503)
  ·
    refine ⟨737887469269516519622255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 491924979513011013081503 737887469269516519622255)
    ·
      refine ⟨1106831203904274779433383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 737887469269516519622255 1106831203904274779433383)
      ·
        refine ⟨1660246805856412169150075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1106831203904274779433383 1660246805856412169150075)
        ·
          refine ⟨2490370208784618253725113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1660246805856412169150075 2490370208784618253725113)
          ·
            refine ⟨1867777656588463690293835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2490370208784618253725113 1867777656588463690293835)
            ·
              refine ⟨2801666484882695535440753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1867777656588463690293835 2801666484882695535440753)
              ·
                refine ⟨2101249863662021651580565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2801666484882695535440753 2101249863662021651580565)
                ·
                  refine ⟨98496087359157264917839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2101249863662021651580565 98496087359157264917839)
                  ·
                    rfl

theorem cell20_215798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_215798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215798 prefixEnd_215798 := by exact prefixLift 215798
  have htrace : WordTrace (prefixWord ++ tailWord_215798) baseStart_215798 baseEnd_215798 := by
    simpa [prefixWord, tailWord_215798, baseEnd_215798] using wordTrace_append hprefix tailTrace_215798
  have hstable : (prefixWord ++ tailWord_215798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215798).length < 2 ^ (prefixWord ++ tailWord_215798).sum := by decide
  have hdescent : baseEnd_215798 < baseStart_215798 := by decide
  rcases family_descends (prefixWord ++ tailWord_215798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215815 : List Nat := [1, 1, 4, 4, 1, 2, 2, 1, 4]
def baseStart_215815 : Nat := 118140960795 + 215815 * 2 ^ 59
def prefixEnd_215815 : Nat := 4983230072969 + 3 ^ 40 * 215815 * 2
def baseEnd_215815 : Nat := 98503846622380761351103

theorem tailTrace_215815 : CollatzResearch.WordTrace tailWord_215815 prefixEnd_215815 98503846622380761351103 := by
  unfold tailWord_215815
  simp only [CollatzResearch.WordTrace]
  refine ⟨7871419713146588112672899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5247613142097725408448599 7871419713146588112672899)
  ·
    refine ⟨11807129569719882169009349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7871419713146588112672899 11807129569719882169009349)
    ·
      refine ⟨2213836794322477906689253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11807129569719882169009349 2213836794322477906689253)
      ·
        refine ⟨415094398935464607504235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2213836794322477906689253 415094398935464607504235)
        ·
          refine ⟨622641598403196911256353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415094398935464607504235 622641598403196911256353)
          ·
            refine ⟨466981198802397683442265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622641598403196911256353 466981198802397683442265)
            ·
              refine ⟨350235899101798262581699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466981198802397683442265 350235899101798262581699)
              ·
                refine ⟨525353848652697393872549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350235899101798262581699 525353848652697393872549)
                ·
                  refine ⟨98503846622380761351103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 525353848652697393872549 98503846622380761351103)
                  ·
                    rfl

theorem cell20_215815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 4].length) (baseStart_215815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215815 prefixEnd_215815 := by exact prefixLift 215815
  have htrace : WordTrace (prefixWord ++ tailWord_215815) baseStart_215815 baseEnd_215815 := by
    simpa [prefixWord, tailWord_215815, baseEnd_215815] using wordTrace_append hprefix tailTrace_215815
  have hstable : (prefixWord ++ tailWord_215815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215815).length < 2 ^ (prefixWord ++ tailWord_215815).sum := by decide
  have hdescent : baseEnd_215815 < baseStart_215815 := by decide
  rcases family_descends (prefixWord ++ tailWord_215815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215836 : List Nat := [2, 2, 3, 1, 1, 3, 2, 2, 4]
def baseStart_215836 : Nat := 118140960795 + 215836 * 2 ^ 59
def prefixEnd_215836 : Nat := 4983230072969 + 3 ^ 40 * 215836 * 2
def baseEnd_215836 : Nat := 98513431594598021651017

theorem tailTrace_215836 : CollatzResearch.WordTrace tailWord_215836 prefixEnd_215836 98513431594598021651017 := by
  unfold tailWord_215836
  simp only [CollatzResearch.WordTrace]
  refine ⟨3936092823035254349593681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5248123764047005799458241 3936092823035254349593681)
  ·
    refine ⟨2952069617276440762195261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3936092823035254349593681 2952069617276440762195261)
    ·
      refine ⟨1107026106478665285823223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2952069617276440762195261 1107026106478665285823223)
      ·
        refine ⟨1660539159717997928734835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1107026106478665285823223 1660539159717997928734835)
        ·
          refine ⟨2490808739576996893102253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1660539159717997928734835 2490808739576996893102253)
          ·
            refine ⟨934053277341373834913345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2490808739576996893102253 934053277341373834913345)
            ·
              refine ⟨700539958006030376185009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 934053277341373834913345 700539958006030376185009)
              ·
                refine ⟨525404968504522782138757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 700539958006030376185009 525404968504522782138757)
                ·
                  refine ⟨98513431594598021651017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 525404968504522782138757 98513431594598021651017)
                  ·
                    rfl

theorem cell20_215836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_215836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215836 prefixEnd_215836 := by exact prefixLift 215836
  have htrace : WordTrace (prefixWord ++ tailWord_215836) baseStart_215836 baseEnd_215836 := by
    simpa [prefixWord, tailWord_215836, baseEnd_215836] using wordTrace_append hprefix tailTrace_215836
  have hstable : (prefixWord ++ tailWord_215836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215836).length < 2 ^ (prefixWord ++ tailWord_215836).sum := by decide
  have hdescent : baseEnd_215836 < baseStart_215836 := by decide
  rcases family_descends (prefixWord ++ tailWord_215836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215870 : List Nat := [4, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_215870 : Nat := 118140960795 + 215870 * 2 ^ 59
def prefixEnd_215870 : Nat := 4983230072969 + 3 ^ 40 * 215870 * 2
def baseEnd_215870 : Nat := 98528950121045014517545

theorem tailTrace_215870 : CollatzResearch.WordTrace tailWord_215870 prefixEnd_215870 98528950121045014517545 := by
  unfold tailWord_215870
  simp only [CollatzResearch.WordTrace]
  refine ⟨984178215993416563240633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5248950485298221670616709 984178215993416563240633)
  ·
    refine ⟨738133661995062422430475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 984178215993416563240633 738133661995062422430475)
    ·
      refine ⟨1107200492992593633645713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 738133661995062422430475 1107200492992593633645713)
      ·
        refine ⟨830400369744445225234285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1107200492992593633645713 830400369744445225234285)
        ·
          refine ⟨311400138654166959462857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 830400369744445225234285 311400138654166959462857)
          ·
            refine ⟨233550103990625219597143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311400138654166959462857 233550103990625219597143)
            ·
              refine ⟨350325155985937829395715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233550103990625219597143 350325155985937829395715)
              ·
                refine ⟨525487733978906744093573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350325155985937829395715 525487733978906744093573)
                ·
                  refine ⟨98528950121045014517545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 525487733978906744093573 98528950121045014517545)
                  ·
                    rfl

theorem cell20_215870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_215870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215870 prefixEnd_215870 := by exact prefixLift 215870
  have htrace : WordTrace (prefixWord ++ tailWord_215870) baseStart_215870 baseEnd_215870 := by
    simpa [prefixWord, tailWord_215870, baseEnd_215870] using wordTrace_append hprefix tailTrace_215870
  have hstable : (prefixWord ++ tailWord_215870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215870).length < 2 ^ (prefixWord ++ tailWord_215870).sum := by decide
  have hdescent : baseEnd_215870 < baseStart_215870 := by decide
  rcases family_descends (prefixWord ++ tailWord_215870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215881 : List Nat := [1, 2, 1, 1, 2, 6, 2, 5]
def baseStart_215881 : Nat := 118140960795 + 215881 * 2 ^ 59
def prefixEnd_215881 : Nat := 4983230072969 + 3 ^ 40 * 215881 * 2
def baseEnd_215881 : Nat := 32844656940259288383611

theorem tailTrace_215881 : CollatzResearch.WordTrace tailWord_215881 prefixEnd_215881 32844656940259288383611 := by
  unfold tailWord_215881
  simp only [CollatzResearch.WordTrace]
  refine ⟨7873826930907481384575497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5249217953938320923050331 7873826930907481384575497)
  ·
    refine ⟨5905370198180611038431623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7873826930907481384575497 5905370198180611038431623)
    ·
      refine ⟨8858055297270916557647435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5905370198180611038431623 8858055297270916557647435)
      ·
        refine ⟨13287082945906374836471153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8858055297270916557647435 13287082945906374836471153)
        ·
          refine ⟨9965312209429781127353365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13287082945906374836471153 9965312209429781127353365)
          ·
            refine ⟨467124009817020990344689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9965312209429781127353365 467124009817020990344689)
            ·
              refine ⟨350343007362765742758517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467124009817020990344689 350343007362765742758517)
              ·
                refine ⟨32844656940259288383611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 350343007362765742758517 32844656940259288383611)
                ·
                  rfl

theorem cell20_215881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 5].length) (baseStart_215881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215881 prefixEnd_215881 := by exact prefixLift 215881
  have htrace : WordTrace (prefixWord ++ tailWord_215881) baseStart_215881 baseEnd_215881 := by
    simpa [prefixWord, tailWord_215881, baseEnd_215881] using wordTrace_append hprefix tailTrace_215881
  have hstable : (prefixWord ++ tailWord_215881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215881).length < 2 ^ (prefixWord ++ tailWord_215881).sum := by decide
  have hdescent : baseEnd_215881 < baseStart_215881 := by decide
  rcases family_descends (prefixWord ++ tailWord_215881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215884 : List Nat := [2, 2, 1, 3, 3, 1, 4, 1, 3]
def baseStart_215884 : Nat := 118140960795 + 215884 * 2 ^ 59
def prefixEnd_215884 : Nat := 4983230072969 + 3 ^ 40 * 215884 * 2
def baseEnd_215884 : Nat := 98535340102523188050821

theorem tailTrace_215884 : CollatzResearch.WordTrace tailWord_215884 prefixEnd_215884 98535340102523188050821 := by
  unfold tailWord_215884
  simp only [CollatzResearch.WordTrace]
  refine ⟨3936968174948306448467353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5249290899931075264623137 3936968174948306448467353)
  ·
    refine ⟨2952726131211229836350515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3936968174948306448467353 2952726131211229836350515)
    ·
      refine ⟨4429089196816844754525773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2952726131211229836350515 4429089196816844754525773)
      ·
        refine ⟨1660908448806316782947165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4429089196816844754525773 1660908448806316782947165)
        ·
          refine ⟨622840668302368793605187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1660908448806316782947165 622840668302368793605187)
          ·
            refine ⟨934261002453553190407781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622840668302368793605187 934261002453553190407781)
            ·
              refine ⟨175173937960041223201459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 934261002453553190407781 175173937960041223201459)
              ·
                refine ⟨262760906940061834802189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175173937960041223201459 262760906940061834802189)
                ·
                  refine ⟨98535340102523188050821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262760906940061834802189 98535340102523188050821)
                  ·
                    rfl

theorem cell20_215884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_215884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215884 prefixEnd_215884 := by exact prefixLift 215884
  have htrace : WordTrace (prefixWord ++ tailWord_215884) baseStart_215884 baseEnd_215884 := by
    simpa [prefixWord, tailWord_215884, baseEnd_215884] using wordTrace_append hprefix tailTrace_215884
  have hstable : (prefixWord ++ tailWord_215884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215884).length < 2 ^ (prefixWord ++ tailWord_215884).sum := by decide
  have hdescent : baseEnd_215884 < baseStart_215884 := by decide
  rcases family_descends (prefixWord ++ tailWord_215884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215925 : List Nat := [1, 3, 4, 1, 1, 4, 2, 2, 2]
def baseStart_215925 : Nat := 118140960795 + 215925 * 2 ^ 59
def prefixEnd_215925 : Nat := 4983230072969 + 3 ^ 40 * 215925 * 2
def baseEnd_215925 : Nat := 98554053619709267683987

theorem tailTrace_215925 : CollatzResearch.WordTrace tailWord_215925 prefixEnd_215925 98554053619709267683987 := by
  unfold tailWord_215925
  simp only [CollatzResearch.WordTrace]
  refine ⟨7875431742748076899177229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5250287828498717932784819 7875431742748076899177229)
  ·
    refine ⟨2953286903530528837191461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7875431742748076899177229 2953286903530528837191461)
    ·
      refine ⟨553741294411974156973399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2953286903530528837191461 553741294411974156973399)
      ·
        refine ⟨830611941617961235460099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553741294411974156973399 830611941617961235460099)
        ·
          refine ⟨1245917912426941853190149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830611941617961235460099 1245917912426941853190149)
          ·
            refine ⟨233609608580051597473153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1245917912426941853190149 233609608580051597473153)
            ·
              refine ⟨175207206435038698104865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233609608580051597473153 175207206435038698104865)
              ·
                refine ⟨131405404826279023578649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175207206435038698104865 131405404826279023578649)
                ·
                  refine ⟨98554053619709267683987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131405404826279023578649 98554053619709267683987)
                  ·
                    rfl

theorem cell20_215925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_215925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215925 prefixEnd_215925 := by exact prefixLift 215925
  have htrace : WordTrace (prefixWord ++ tailWord_215925) baseStart_215925 baseEnd_215925 := by
    simpa [prefixWord, tailWord_215925, baseEnd_215925] using wordTrace_append hprefix tailTrace_215925
  have hstable : (prefixWord ++ tailWord_215925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215925).length < 2 ^ (prefixWord ++ tailWord_215925).sum := by decide
  have hdescent : baseEnd_215925 < baseStart_215925 := by decide
  rcases family_descends (prefixWord ++ tailWord_215925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215929 : List Nat := [1, 2, 1, 3, 2, 4, 1, 4, 2]
def baseStart_215929 : Nat := 118140960795 + 215929 * 2 ^ 59
def prefixEnd_215929 : Nat := 4983230072969 + 3 ^ 40 * 215929 * 2
def baseEnd_215929 : Nat := 98555879328703031550637

theorem tailTrace_215929 : CollatzResearch.WordTrace tailWord_215929 prefixEnd_215929 98555879328703031550637 := by
  unfold tailWord_215929
  simp only [CollatzResearch.WordTrace]
  refine ⟨7875577634733585582322841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5250385089822390388215227 7875577634733585582322841)
  ·
    refine ⟨5906683226050189186742131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7875577634733585582322841 5906683226050189186742131)
    ·
      refine ⟨8860024839075283780113197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5906683226050189186742131 8860024839075283780113197)
      ·
        refine ⟨3322509314653231417542449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8860024839075283780113197 3322509314653231417542449)
        ·
          refine ⟨2491881985989923563156837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3322509314653231417542449 2491881985989923563156837)
          ·
            refine ⟨467227872373110668091907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2491881985989923563156837 467227872373110668091907)
            ·
              refine ⟨700841808559666002137861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467227872373110668091907 700841808559666002137861)
              ·
                refine ⟨131407839104937375400849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 700841808559666002137861 131407839104937375400849)
                ·
                  refine ⟨98555879328703031550637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131407839104937375400849 98555879328703031550637)
                  ·
                    rfl

theorem cell20_215929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 2].length) (baseStart_215929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215929 prefixEnd_215929 := by exact prefixLift 215929
  have htrace : WordTrace (prefixWord ++ tailWord_215929) baseStart_215929 baseEnd_215929 := by
    simpa [prefixWord, tailWord_215929, baseEnd_215929] using wordTrace_append hprefix tailTrace_215929
  have hstable : (prefixWord ++ tailWord_215929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215929).length < 2 ^ (prefixWord ++ tailWord_215929).sum := by decide
  have hdescent : baseEnd_215929 < baseStart_215929 := by decide
  rcases family_descends (prefixWord ++ tailWord_215929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215943 : List Nat := [1, 1, 4, 2, 3, 1, 2, 3, 3]
def baseStart_215943 : Nat := 118140960795 + 215943 * 2 ^ 59
def prefixEnd_215943 : Nat := 4983230072969 + 3 ^ 40 * 215943 * 2
def baseEnd_215943 : Nat := 98562269310181205083913

theorem tailTrace_215943 : CollatzResearch.WordTrace tailWord_215943 prefixEnd_215943 98562269310181205083913 := by
  unfold tailWord_215943
  simp only [CollatzResearch.WordTrace]
  refine ⟨7876088256682865973332483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5250725504455243982221655 7876088256682865973332483)
  ·
    refine ⟨11814132385024298959998725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7876088256682865973332483 11814132385024298959998725)
    ·
      refine ⟨2215149822192056054999761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11814132385024298959998725 2215149822192056054999761)
      ·
        refine ⟨1661362366644042041249821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2215149822192056054999761 1661362366644042041249821)
        ·
          refine ⟨623010887491515765468683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1661362366644042041249821 623010887491515765468683)
          ·
            refine ⟨934516331237273648203025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623010887491515765468683 934516331237273648203025)
            ·
              refine ⟨700887248427955236152269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 934516331237273648203025 700887248427955236152269)
              ·
                refine ⟨262832718160483213557101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 700887248427955236152269 262832718160483213557101)
                ·
                  refine ⟨98562269310181205083913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262832718160483213557101 98562269310181205083913)
                  ·
                    rfl

theorem cell20_215943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 3].length) (baseStart_215943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215943 prefixEnd_215943 := by exact prefixLift 215943
  have htrace : WordTrace (prefixWord ++ tailWord_215943) baseStart_215943 baseEnd_215943 := by
    simpa [prefixWord, tailWord_215943, baseEnd_215943] using wordTrace_append hprefix tailTrace_215943
  have hstable : (prefixWord ++ tailWord_215943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215943).length < 2 ^ (prefixWord ++ tailWord_215943).sum := by decide
  have hdescent : baseEnd_215943 < baseStart_215943 := by decide
  rcases family_descends (prefixWord ++ tailWord_215943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215967 : List Nat := [1, 1, 2, 5, 2, 1, 1, 5, 2]
def baseStart_215967 : Nat := 118140960795 + 215967 * 2 ^ 59
def prefixEnd_215967 : Nat := 4983230072969 + 3 ^ 40 * 215967 * 2
def baseEnd_215967 : Nat := 98573223564143788283815

theorem tailTrace_215967 : CollatzResearch.WordTrace tailWord_215967 prefixEnd_215967 98573223564143788283815 := by
  unfold tailWord_215967
  simp only [CollatzResearch.WordTrace]
  refine ⟨7876963608595918072206155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5251309072397278714804103 7876963608595918072206155)
  ·
    refine ⟨11815445412893877108309233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7876963608595918072206155 11815445412893877108309233)
    ·
      refine ⟨8861584059670407831231925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11815445412893877108309233 8861584059670407831231925)
      ·
        refine ⟨830773505594100734177993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8861584059670407831231925 830773505594100734177993)
        ·
          refine ⟨623080129195575550633495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 830773505594100734177993 623080129195575550633495)
          ·
            refine ⟨934620193793363325950243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623080129195575550633495 934620193793363325950243)
            ·
              refine ⟨1401930290690044988925365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934620193793363325950243 1401930290690044988925365)
              ·
                refine ⟨131430964752191717711753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1401930290690044988925365 131430964752191717711753)
                ·
                  refine ⟨98573223564143788283815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131430964752191717711753 98573223564143788283815)
                  ·
                    rfl

theorem cell20_215967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 2].length) (baseStart_215967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215967 prefixEnd_215967 := by exact prefixLift 215967
  have htrace : WordTrace (prefixWord ++ tailWord_215967) baseStart_215967 baseEnd_215967 := by
    simpa [prefixWord, tailWord_215967, baseEnd_215967] using wordTrace_append hprefix tailTrace_215967
  have hstable : (prefixWord ++ tailWord_215967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215967).length < 2 ^ (prefixWord ++ tailWord_215967).sum := by decide
  have hdescent : baseEnd_215967 < baseStart_215967 := by decide
  rcases family_descends (prefixWord ++ tailWord_215967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215998 : List Nat := [4, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_215998 : Nat := 118140960795 + 215998 * 2 ^ 59
def prefixEnd_215998 : Nat := 4983230072969 + 3 ^ 40 * 215998 * 2
def baseEnd_215998 : Nat := 98587372808845458250355

theorem tailTrace_215998 : CollatzResearch.WordTrace tailWord_215998 prefixEnd_215998 98587372808845458250355 := by
  unfold tailWord_215998
  simp only [CollatzResearch.WordTrace]
  refine ⟨984761783935451295823081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5252062847655740244389765 984761783935451295823081)
  ·
    refine ⟨738571337951588471867311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 984761783935451295823081 738571337951588471867311)
    ·
      refine ⟨1107857006927382707800967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 738571337951588471867311 1107857006927382707800967)
      ·
        refine ⟨1661785510391074061701451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1107857006927382707800967 1661785510391074061701451)
        ·
          refine ⟨2492678265586611092552177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1661785510391074061701451 2492678265586611092552177)
          ·
            refine ⟨1869508699189958319414133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2492678265586611092552177 1869508699189958319414133)
            ·
              refine ⟨175266440549058592445075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1869508699189958319414133 175266440549058592445075)
              ·
                refine ⟨262899660823587888667613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175266440549058592445075 262899660823587888667613)
                ·
                  refine ⟨98587372808845458250355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262899660823587888667613 98587372808845458250355)
                  ·
                    rfl

theorem cell20_215998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_215998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_215998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_215998 prefixEnd_215998 := by exact prefixLift 215998
  have htrace : WordTrace (prefixWord ++ tailWord_215998) baseStart_215998 baseEnd_215998 := by
    simpa [prefixWord, tailWord_215998, baseEnd_215998] using wordTrace_append hprefix tailTrace_215998
  have hstable : (prefixWord ++ tailWord_215998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215998).length < 2 ^ (prefixWord ++ tailWord_215998).sum := by decide
  have hdescent : baseEnd_215998 < baseStart_215998 := by decide
  rcases family_descends (prefixWord ++ tailWord_215998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216040 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 5]
def baseStart_216040 : Nat := 118140960795 + 216040 * 2 ^ 59
def prefixEnd_216040 : Nat := 4983230072969 + 3 ^ 40 * 216040 * 2
def baseEnd_216040 : Nat := 98606542753279978850183

theorem tailTrace_216040 : CollatzResearch.WordTrace tailWord_216040 prefixEnd_216040 98606542753279978850183 := by
  unfold tailWord_216040
  simp only [CollatzResearch.WordTrace]
  refine ⟨3939813068665725769806787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5253084091554301026409049 3939813068665725769806787)
  ·
    refine ⟨5909719602998588654710181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3939813068665725769806787 5909719602998588654710181)
    ·
      refine ⟨1108072425562235372758159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5909719602998588654710181 1108072425562235372758159)
      ·
        refine ⟨1662108638343353059137239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1108072425562235372758159 1662108638343353059137239)
        ·
          refine ⟨2493162957515029588705859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1662108638343353059137239 2493162957515029588705859)
          ·
            refine ⟨3739744436272544383058789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2493162957515029588705859 3739744436272544383058789)
            ·
              refine ⟨701202081801102071823523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3739744436272544383058789 701202081801102071823523)
              ·
                refine ⟨1051803122701653107735285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701202081801102071823523 1051803122701653107735285)
                ·
                  refine ⟨98606542753279978850183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1051803122701653107735285 98606542753279978850183)
                  ·
                    rfl

theorem cell20_216040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_216040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216040 prefixEnd_216040 := by exact prefixLift 216040
  have htrace : WordTrace (prefixWord ++ tailWord_216040) baseStart_216040 baseEnd_216040 := by
    simpa [prefixWord, tailWord_216040, baseEnd_216040] using wordTrace_append hprefix tailTrace_216040
  have hstable : (prefixWord ++ tailWord_216040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216040).length < 2 ^ (prefixWord ++ tailWord_216040).sum := by decide
  have hdescent : baseEnd_216040 < baseStart_216040 := by decide
  rcases family_descends (prefixWord ++ tailWord_216040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216053 : List Nat := [1, 3, 5, 2, 1, 1, 1, 3, 3]
def baseStart_216053 : Nat := 118140960795 + 216053 * 2 ^ 59
def prefixEnd_216053 : Nat := 4983230072969 + 3 ^ 40 * 216053 * 2
def baseEnd_216053 : Nat := 98612476307509711416797

theorem tailTrace_216053 : CollatzResearch.WordTrace tailWord_216053 prefixEnd_216053 98612476307509711416797 := by
  unfold tailWord_216053
  simp only [CollatzResearch.WordTrace]
  refine ⟨7880100286284354759836813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5253400190856236506557875 7880100286284354759836813)
  ·
    refine ⟨2955037607356633034938805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7880100286284354759836813 2955037607356633034938805)
    ·
      refine ⟨277034775689684347025513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2955037607356633034938805 277034775689684347025513)
      ·
        refine ⟨207776081767263260269135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277034775689684347025513 207776081767263260269135)
        ·
          refine ⟨311664122650894890403703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207776081767263260269135 311664122650894890403703)
          ·
            refine ⟨467496183976342335605555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311664122650894890403703 467496183976342335605555)
            ·
              refine ⟨701244275964513503408333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467496183976342335605555 701244275964513503408333)
              ·
                refine ⟨262966603486692563778125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 701244275964513503408333 262966603486692563778125)
                ·
                  refine ⟨98612476307509711416797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262966603486692563778125 98612476307509711416797)
                  ·
                    rfl

theorem cell20_216053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_216053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216053 prefixEnd_216053 := by exact prefixLift 216053
  have htrace : WordTrace (prefixWord ++ tailWord_216053) baseStart_216053 baseEnd_216053 := by
    simpa [prefixWord, tailWord_216053, baseEnd_216053] using wordTrace_append hprefix tailTrace_216053
  have hstable : (prefixWord ++ tailWord_216053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216053).length < 2 ^ (prefixWord ++ tailWord_216053).sum := by decide
  have hdescent : baseEnd_216053 < baseStart_216053 := by decide
  rcases family_descends (prefixWord ++ tailWord_216053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216092 : List Nat := [2, 2, 3, 1, 12]
def baseStart_216092 : Nat := 118140960795 + 216092 * 2 ^ 59
def prefixEnd_216092 : Nat := 4983230072969 + 3 ^ 40 * 216092 * 2
def baseEnd_216092 : Nat := 1217657740372826038477

theorem tailTrace_216092 : CollatzResearch.WordTrace tailWord_216092 prefixEnd_216092 1217657740372826038477 := by
  unfold tailWord_216092
  simp only [CollatzResearch.WordTrace]
  refine ⟨3940761366571532210253265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5254348488762042947004353 3940761366571532210253265)
  ·
    refine ⟨2955571024928649157689949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3940761366571532210253265 2955571024928649157689949)
    ·
      refine ⟨1108339134348243434133731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2955571024928649157689949 1108339134348243434133731)
      ·
        refine ⟨1662508701522365151200597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1108339134348243434133731 1662508701522365151200597)
        ·
          refine ⟨1217657740372826038477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1662508701522365151200597 1217657740372826038477)
          ·
            rfl

theorem cell20_216092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 12].length) (baseStart_216092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216092 prefixEnd_216092 := by exact prefixLift 216092
  have htrace : WordTrace (prefixWord ++ tailWord_216092) baseStart_216092 baseEnd_216092 := by
    simpa [prefixWord, tailWord_216092, baseEnd_216092] using wordTrace_append hprefix tailTrace_216092
  have hstable : (prefixWord ++ tailWord_216092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216092).length < 2 ^ (prefixWord ++ tailWord_216092).sum := by decide
  have hdescent : baseEnd_216092 < baseStart_216092 := by decide
  rcases family_descends (prefixWord ++ tailWord_216092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216095 : List Nat := [1, 1, 2, 4, 1, 4, 2, 2, 3]
def baseStart_216095 : Nat := 118140960795 + 216095 * 2 ^ 59
def prefixEnd_216095 : Nat := 4983230072969 + 3 ^ 40 * 216095 * 2
def baseEnd_216095 : Nat := 98631646251944232016625

theorem tailTrace_216095 : CollatzResearch.WordTrace tailWord_216095 prefixEnd_216095 98631646251944232016625 := by
  unfold tailWord_216095
  simp only [CollatzResearch.WordTrace]
  refine ⟨7881632152132195932865739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5254421434754797288577159 7881632152132195932865739)
  ·
    refine ⟨11822448228198293899298609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7881632152132195932865739 11822448228198293899298609)
    ·
      refine ⟨8866836171148720424473957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11822448228198293899298609 8866836171148720424473957)
      ·
        refine ⟨1662531782090385079588867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8866836171148720424473957 1662531782090385079588867)
        ·
          refine ⟨2493797673135577619383301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1662531782090385079588867 2493797673135577619383301)
          ·
            refine ⟨467587063712920803634369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2493797673135577619383301 467587063712920803634369)
            ·
              refine ⟨350690297784690602725777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467587063712920803634369 350690297784690602725777)
              ·
                refine ⟨263017723338517952044333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350690297784690602725777 263017723338517952044333)
                ·
                  refine ⟨98631646251944232016625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263017723338517952044333 98631646251944232016625)
                  ·
                    rfl

theorem cell20_216095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 3].length) (baseStart_216095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216095 prefixEnd_216095 := by exact prefixLift 216095
  have htrace : WordTrace (prefixWord ++ tailWord_216095) baseStart_216095 baseEnd_216095 := by
    simpa [prefixWord, tailWord_216095, baseEnd_216095] using wordTrace_append hprefix tailTrace_216095
  have hstable : (prefixWord ++ tailWord_216095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216095).length < 2 ^ (prefixWord ++ tailWord_216095).sum := by decide
  have hdescent : baseEnd_216095 < baseStart_216095 := by decide
  rcases family_descends (prefixWord ++ tailWord_216095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216098 : List Nat := [3, 3, 1, 1, 1, 3, 4, 2, 2]
def baseStart_216098 : Nat := 118140960795 + 216098 * 2 ^ 59
def prefixEnd_216098 : Nat := 4983230072969 + 3 ^ 40 * 216098 * 2
def baseEnd_216098 : Nat := 98633015533689554916613

theorem tailTrace_216098 : CollatzResearch.WordTrace tailWord_216098 prefixEnd_216098 98633015533689554916613 := by
  unfold tailWord_216098
  simp only [CollatzResearch.WordTrace]
  refine ⟨1970435392780331861306237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5254494380747551630149965 1970435392780331861306237)
  ·
    refine ⟨738913272292624447989839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1970435392780331861306237 738913272292624447989839)
    ·
      refine ⟨1108369908438936671984759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 738913272292624447989839 1108369908438936671984759)
      ·
        refine ⟨1662554862658405007977139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1108369908438936671984759 1662554862658405007977139)
        ·
          refine ⟨2493832293987607511965709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1662554862658405007977139 2493832293987607511965709)
          ·
            refine ⟨935187110245352816987141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2493832293987607511965709 935187110245352816987141)
            ·
              refine ⟨175347583171003653185089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 935187110245352816987141 175347583171003653185089)
              ·
                refine ⟨131510687378252739888817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175347583171003653185089 131510687378252739888817)
                ·
                  refine ⟨98633015533689554916613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131510687378252739888817 98633015533689554916613)
                  ·
                    rfl

theorem cell20_216098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_216098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216098 prefixEnd_216098 := by exact prefixLift 216098
  have htrace : WordTrace (prefixWord ++ tailWord_216098) baseStart_216098 baseEnd_216098 := by
    simpa [prefixWord, tailWord_216098, baseEnd_216098] using wordTrace_append hprefix tailTrace_216098
  have hstable : (prefixWord ++ tailWord_216098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216098).length < 2 ^ (prefixWord ++ tailWord_216098).sum := by decide
  have hdescent : baseEnd_216098 < baseStart_216098 := by decide
  rcases family_descends (prefixWord ++ tailWord_216098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216154 : List Nat := [3, 1, 1, 2, 1, 1, 2, 6, 3]
def baseStart_216154 : Nat := 118140960795 + 216154 * 2 ^ 59
def prefixEnd_216154 : Nat := 4983230072969 + 3 ^ 40 * 216154 * 2
def baseEnd_216154 : Nat := 98658575459602249049717

theorem tailTrace_216154 : CollatzResearch.WordTrace tailWord_216154 prefixEnd_216154 98658575459602249049717 := by
  unfold tailWord_216154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1970946014729612252315879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5255856039278966006175677 1970946014729612252315879)
  ·
    refine ⟨2956419022094418378473819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1970946014729612252315879 2956419022094418378473819)
    ·
      refine ⟨4434628533141627567710729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2956419022094418378473819 4434628533141627567710729)
      ·
        refine ⟨3325971399856220675783047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4434628533141627567710729 3325971399856220675783047)
        ·
          refine ⟨4988957099784331013674571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3325971399856220675783047 4988957099784331013674571)
          ·
            refine ⟨7483435649676496520511857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4988957099784331013674571 7483435649676496520511857)
            ·
              refine ⟨5612576737257372390383893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7483435649676496520511857 5612576737257372390383893)
              ·
                refine ⟨263089534558939330799245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5612576737257372390383893 263089534558939330799245)
                ·
                  refine ⟨98658575459602249049717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263089534558939330799245 98658575459602249049717)
                  ·
                    rfl

theorem cell20_216154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_216154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216154 prefixEnd_216154 := by exact prefixLift 216154
  have htrace : WordTrace (prefixWord ++ tailWord_216154) baseStart_216154 baseEnd_216154 := by
    simpa [prefixWord, tailWord_216154, baseEnd_216154] using wordTrace_append hprefix tailTrace_216154
  have hstable : (prefixWord ++ tailWord_216154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216154).length < 2 ^ (prefixWord ++ tailWord_216154).sum := by decide
  have hdescent : baseEnd_216154 < baseStart_216154 := by decide
  rcases family_descends (prefixWord ++ tailWord_216154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216161 : List Nat := [1, 2, 3, 1, 1, 2, 3, 3, 4]
def baseStart_216161 : Nat := 118140960795 + 216161 * 2 ^ 59
def prefixEnd_216161 : Nat := 4983230072969 + 3 ^ 40 * 216161 * 2
def baseEnd_216161 : Nat := 98661770450341335816355

theorem tailTrace_216161 : CollatzResearch.WordTrace tailWord_216161 prefixEnd_216161 98661770450341335816355 := by
  unfold tailWord_216161
  simp only [CollatzResearch.WordTrace]
  refine ⟨7884039369893089204768337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5256026246595392803178891 7884039369893089204768337)
  ·
    refine ⟨5913029527419816903576253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7884039369893089204768337 5913029527419816903576253)
    ·
      refine ⟨2217386072782431338841095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5913029527419816903576253 2217386072782431338841095)
      ·
        refine ⟨3326079109173647008261643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2217386072782431338841095 3326079109173647008261643)
        ·
          refine ⟨4989118663760470512392465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3326079109173647008261643 4989118663760470512392465)
          ·
            refine ⟨3741838997820352884294349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4989118663760470512392465 3741838997820352884294349)
            ·
              refine ⟨1403189624182632331610381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3741838997820352884294349 1403189624182632331610381)
              ·
                refine ⟨526196109068487124353893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1403189624182632331610381 526196109068487124353893)
                ·
                  refine ⟨98661770450341335816355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 526196109068487124353893 98661770450341335816355)
                  ·
                    rfl

theorem cell20_216161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_216161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216161 prefixEnd_216161 := by exact prefixLift 216161
  have htrace : WordTrace (prefixWord ++ tailWord_216161) baseStart_216161 baseEnd_216161 := by
    simpa [prefixWord, tailWord_216161, baseEnd_216161] using wordTrace_append hprefix tailTrace_216161
  have hstable : (prefixWord ++ tailWord_216161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216161).length < 2 ^ (prefixWord ++ tailWord_216161).sum := by decide
  have hdescent : baseEnd_216161 < baseStart_216161 := by decide
  rcases family_descends (prefixWord ++ tailWord_216161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216185 : List Nat := [1, 2, 1, 3, 5, 1, 1, 6]
def baseStart_216185 : Nat := 118140960795 + 216185 * 2 ^ 59
def prefixEnd_216185 : Nat := 4983230072969 + 3 ^ 40 * 216185 * 2
def baseEnd_216185 : Nat := 32890908234767973005419

theorem tailTrace_216185 : CollatzResearch.WordTrace tailWord_216185 prefixEnd_216185 32890908234767973005419 := by
  unfold tailWord_216185
  simp only [CollatzResearch.WordTrace]
  refine ⟨7884914721806141303642009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5256609814537427535761339 7884914721806141303642009)
  ·
    refine ⟨5913686041354605977731507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7884914721806141303642009 5913686041354605977731507)
    ·
      refine ⟨8870529062031908966597261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5913686041354605977731507 8870529062031908966597261)
      ·
        refine ⟨3326448398261965862473973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8870529062031908966597261 3326448398261965862473973)
        ·
          refine ⟨311854537337059299606935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3326448398261965862473973 311854537337059299606935)
          ·
            refine ⟨467781806005588949410403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311854537337059299606935 467781806005588949410403)
            ·
              refine ⟨701672709008383424115605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467781806005588949410403 701672709008383424115605)
              ·
                refine ⟨32890908234767973005419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 701672709008383424115605 32890908234767973005419)
                ·
                  rfl

theorem cell20_216185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 6].length) (baseStart_216185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216185 prefixEnd_216185 := by exact prefixLift 216185
  have htrace : WordTrace (prefixWord ++ tailWord_216185) baseStart_216185 baseEnd_216185 := by
    simpa [prefixWord, tailWord_216185, baseEnd_216185] using wordTrace_append hprefix tailTrace_216185
  have hstable : (prefixWord ++ tailWord_216185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216185).length < 2 ^ (prefixWord ++ tailWord_216185).sum := by decide
  have hdescent : baseEnd_216185 < baseStart_216185 := by decide
  rcases family_descends (prefixWord ++ tailWord_216185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216216 : List Nat := [2, 1, 2, 4, 2, 1, 3, 1, 4]
def baseStart_216216 : Nat := 118140960795 + 216216 * 2 ^ 59
def prefixEnd_216216 : Nat := 4983230072969 + 3 ^ 40 * 216216 * 2
def baseEnd_216216 : Nat := 98686873949005588982797

theorem tailTrace_216216 : CollatzResearch.WordTrace tailWord_216216 prefixEnd_216216 98686873949005588982797 := by
  unfold tailWord_216216
  simp only [CollatzResearch.WordTrace]
  refine ⟨3943022692346916799010251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5257363589795889065347001 3943022692346916799010251)
  ·
    refine ⟨5914534038520375198515377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3943022692346916799010251 5914534038520375198515377)
    ·
      refine ⟨4435900528890281398886533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5914534038520375198515377 4435900528890281398886533)
      ·
        refine ⟨831731349166927762291225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4435900528890281398886533 831731349166927762291225)
        ·
          refine ⟨623798511875195821718419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 831731349166927762291225 623798511875195821718419)
          ·
            refine ⟨935697767812793732577629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623798511875195821718419 935697767812793732577629)
            ·
              refine ⟨350886662929797649716611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 935697767812793732577629 350886662929797649716611)
              ·
                refine ⟨526329994394696474574917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350886662929797649716611 526329994394696474574917)
                ·
                  refine ⟨98686873949005588982797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 526329994394696474574917 98686873949005588982797)
                  ·
                    rfl

theorem cell20_216216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_216216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216216 prefixEnd_216216 := by exact prefixLift 216216
  have htrace : WordTrace (prefixWord ++ tailWord_216216) baseStart_216216 baseEnd_216216 := by
    simpa [prefixWord, tailWord_216216, baseEnd_216216] using wordTrace_append hprefix tailTrace_216216
  have hstable : (prefixWord ++ tailWord_216216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216216).length < 2 ^ (prefixWord ++ tailWord_216216).sum := by decide
  have hdescent : baseEnd_216216 < baseStart_216216 := by decide
  rcases family_descends (prefixWord ++ tailWord_216216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216226 : List Nat := [3, 3, 1, 3, 2, 1, 1, 3, 3]
def baseStart_216226 : Nat := 118140960795 + 216226 * 2 ^ 59
def prefixEnd_216226 : Nat := 4983230072969 + 3 ^ 40 * 216226 * 2
def baseEnd_216226 : Nat := 98691438221489998649423

theorem tailTrace_216226 : CollatzResearch.WordTrace tailWord_216226 prefixEnd_216226 98691438221489998649423 := by
  unfold tailWord_216226
  simp only [CollatzResearch.WordTrace]
  refine ⟨1971602528664401326471133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5257606743105070203923021 1971602528664401326471133)
  ·
    refine ⟨739350948249150497426675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1971602528664401326471133 739350948249150497426675)
    ·
      refine ⟨1109026422373725746140013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 739350948249150497426675 1109026422373725746140013)
      ·
        refine ⟨415884908390147154802505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1109026422373725746140013 415884908390147154802505)
        ·
          refine ⟨311913681292610366101879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415884908390147154802505 311913681292610366101879)
          ·
            refine ⟨467870521938915549152819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311913681292610366101879 467870521938915549152819)
            ·
              refine ⟨701805782908373323729229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467870521938915549152819 701805782908373323729229)
              ·
                refine ⟨263177168590639996398461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 701805782908373323729229 263177168590639996398461)
                ·
                  refine ⟨98691438221489998649423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263177168590639996398461 98691438221489998649423)
                  ·
                    rfl

theorem cell20_216226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_216226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216226 prefixEnd_216226 := by exact prefixLift 216226
  have htrace : WordTrace (prefixWord ++ tailWord_216226) baseStart_216226 baseEnd_216226 := by
    simpa [prefixWord, tailWord_216226, baseEnd_216226] using wordTrace_append hprefix tailTrace_216226
  have hstable : (prefixWord ++ tailWord_216226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216226).length < 2 ^ (prefixWord ++ tailWord_216226).sum := by decide
  have hdescent : baseEnd_216226 < baseStart_216226 := by decide
  rcases family_descends (prefixWord ++ tailWord_216226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216251 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 5]
def baseStart_216251 : Nat := 118140960795 + 216251 * 2 ^ 59
def prefixEnd_216251 : Nat := 4983230072969 + 3 ^ 40 * 216251 * 2
def baseEnd_216251 : Nat := 98702848902701022815987

theorem tailTrace_216251 : CollatzResearch.WordTrace tailWord_216251 prefixEnd_216251 98702848902701022815987 := by
  unfold tailWord_216251
  simp only [CollatzResearch.WordTrace]
  refine ⟨7887321939567034575544607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5258214626378023050363071 7887321939567034575544607)
  ·
    refine ⟨11830982909350551863316911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7887321939567034575544607 11830982909350551863316911)
    ·
      refine ⟨17746474364025827794975367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11830982909350551863316911 17746474364025827794975367)
      ·
        refine ⟨26619711546038741692463051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17746474364025827794975367 26619711546038741692463051)
        ·
          refine ⟨39929567319058112538694577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26619711546038741692463051 39929567319058112538694577)
          ·
            refine ⟨29947175489293584404020933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39929567319058112538694577 29947175489293584404020933)
            ·
              refine ⟨5615095404242547075753925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29947175489293584404020933 5615095404242547075753925)
              ·
                refine ⟨1052830388295477576703861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5615095404242547075753925 1052830388295477576703861)
                ·
                  refine ⟨98702848902701022815987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1052830388295477576703861 98702848902701022815987)
                  ·
                    rfl

theorem cell20_216251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_216251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216251 prefixEnd_216251 := by exact prefixLift 216251
  have htrace : WordTrace (prefixWord ++ tailWord_216251) baseStart_216251 baseEnd_216251 := by
    simpa [prefixWord, tailWord_216251, baseEnd_216251] using wordTrace_append hprefix tailTrace_216251
  have hstable : (prefixWord ++ tailWord_216251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216251).length < 2 ^ (prefixWord ++ tailWord_216251).sum := by decide
  have hdescent : baseEnd_216251 < baseStart_216251 := by decide
  rcases family_descends (prefixWord ++ tailWord_216251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216299 : List Nat := [1, 1, 1, 1, 2, 7, 3, 4]
def baseStart_216299 : Nat := 118140960795 + 216299 * 2 ^ 59
def prefixEnd_216299 : Nat := 4983230072969 + 3 ^ 40 * 216299 * 2
def baseEnd_216299 : Nat := 32908252470208729738597

theorem tailTrace_216299 : CollatzResearch.WordTrace tailWord_216299 prefixEnd_216299 32908252470208729738597 := by
  unfold tailWord_216299
  simp only [CollatzResearch.WordTrace]
  refine ⟨7889072643393138773291951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5259381762262092515527967 7889072643393138773291951)
  ·
    refine ⟨11833608965089708159937927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7889072643393138773291951 11833608965089708159937927)
    ·
      refine ⟨17750413447634562239906891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11833608965089708159937927 17750413447634562239906891)
      ·
        refine ⟨26625620171451843359860337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17750413447634562239906891 26625620171451843359860337)
        ·
          refine ⟨19969215128588882519895253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26625620171451843359860337 19969215128588882519895253)
          ·
            refine ⟨468028479576301934060045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 19969215128588882519895253 468028479576301934060045)
            ·
              refine ⟨175510679841113225272517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 468028479576301934060045 175510679841113225272517)
              ·
                refine ⟨32908252470208729738597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175510679841113225272517 32908252470208729738597)
                ·
                  rfl

theorem cell20_216299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 4].length) (baseStart_216299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216299 prefixEnd_216299 := by exact prefixLift 216299
  have htrace : WordTrace (prefixWord ++ tailWord_216299) baseStart_216299 baseEnd_216299 := by
    simpa [prefixWord, tailWord_216299, baseEnd_216299] using wordTrace_append hprefix tailTrace_216299
  have hstable : (prefixWord ++ tailWord_216299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216299).length < 2 ^ (prefixWord ++ tailWord_216299).sum := by decide
  have hdescent : baseEnd_216299 < baseStart_216299 := by decide
  rcases family_descends (prefixWord ++ tailWord_216299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216323 : List Nat := [1, 1, 1, 3, 2, 6, 1, 2, 3]
def baseStart_216323 : Nat := 118140960795 + 216323 * 2 ^ 59
def prefixEnd_216323 : Nat := 4983230072969 + 3 ^ 40 * 216323 * 2
def baseEnd_216323 : Nat := 98735711664588772415693

theorem tailTrace_216323 : CollatzResearch.WordTrace tailWord_216323 prefixEnd_216323 98735711664588772415693 := by
  unfold tailWord_216323
  simp only [CollatzResearch.WordTrace]
  refine ⟨7889947995306190872165623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5259965330204127248110415 7889947995306190872165623)
  ·
    refine ⟨11834921992959286308248435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7889947995306190872165623 11834921992959286308248435)
    ·
      refine ⟨17752382989438929462372653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11834921992959286308248435 17752382989438929462372653)
      ·
        refine ⟨6657143621039598548389745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17752382989438929462372653 6657143621039598548389745)
        ·
          refine ⟨4992857715779698911292309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6657143621039598548389745 4992857715779698911292309)
          ·
            refine ⟨234040205427173386466827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4992857715779698911292309 234040205427173386466827)
            ·
              refine ⟨351060308140760079700241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234040205427173386466827 351060308140760079700241)
              ·
                refine ⟨263295231105570059775181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351060308140760079700241 263295231105570059775181)
                ·
                  refine ⟨98735711664588772415693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263295231105570059775181 98735711664588772415693)
                  ·
                    rfl

theorem cell20_216323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 3].length) (baseStart_216323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216323 prefixEnd_216323 := by exact prefixLift 216323
  have htrace : WordTrace (prefixWord ++ tailWord_216323) baseStart_216323 baseEnd_216323 := by
    simpa [prefixWord, tailWord_216323, baseEnd_216323] using wordTrace_append hprefix tailTrace_216323
  have hstable : (prefixWord ++ tailWord_216323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216323).length < 2 ^ (prefixWord ++ tailWord_216323).sum := by decide
  have hdescent : baseEnd_216323 < baseStart_216323 := by decide
  rcases family_descends (prefixWord ++ tailWord_216323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216350 : List Nat := [4, 3, 2, 1, 2, 2, 2, 4]
def baseStart_216350 : Nat := 118140960795 + 216350 * 2 ^ 59
def prefixEnd_216350 : Nat := 4983230072969 + 3 ^ 40 * 216350 * 2
def baseEnd_216350 : Nat := 32916011733432226171861

theorem tailTrace_216350 : CollatzResearch.WordTrace tailWord_216350 prefixEnd_216350 32916011733432226171861 := by
  unfold tailWord_216350
  simp only [CollatzResearch.WordTrace]
  refine ⟨986366595776046810424813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5260621844138916322265669 986366595776046810424813)
  ·
    refine ⟨369887473416017553909305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 986366595776046810424813 369887473416017553909305)
    ·
      refine ⟨277415605062013165431979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369887473416017553909305 277415605062013165431979)
      ·
        refine ⟨416123407593019748147969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277415605062013165431979 416123407593019748147969)
        ·
          refine ⟨312092555694764811110977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416123407593019748147969 312092555694764811110977)
          ·
            refine ⟨234069416771073608333233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312092555694764811110977 234069416771073608333233)
            ·
              refine ⟨175552062578305206249925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234069416771073608333233 175552062578305206249925)
              ·
                refine ⟨32916011733432226171861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175552062578305206249925 32916011733432226171861)
                ·
                  rfl

theorem cell20_216350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_216350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216350 prefixEnd_216350 := by exact prefixLift 216350
  have htrace : WordTrace (prefixWord ++ tailWord_216350) baseStart_216350 baseEnd_216350 := by
    simpa [prefixWord, tailWord_216350, baseEnd_216350] using wordTrace_append hprefix tailTrace_216350
  have hstable : (prefixWord ++ tailWord_216350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216350).length < 2 ^ (prefixWord ++ tailWord_216350).sum := by decide
  have hdescent : baseEnd_216350 < baseStart_216350 := by decide
  rcases family_descends (prefixWord ++ tailWord_216350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216381 : List Nat := [1, 4, 1, 5, 1, 1, 3, 2, 2]
def baseStart_216381 : Nat := 118140960795 + 216381 * 2 ^ 59
def prefixEnd_216381 : Nat := 4983230072969 + 3 ^ 40 * 216381 * 2
def baseEnd_216381 : Nat := 98762184444998348482123

theorem tailTrace_216381 : CollatzResearch.WordTrace tailWord_216381 prefixEnd_216381 98762184444998348482123 := by
  unfold tailWord_216381
  simp only [CollatzResearch.WordTrace]
  refine ⟨7892063429096066777776997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5261375619397377851851331 7892063429096066777776997)
  ·
    refine ⟨1479761892955512520833187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7892063429096066777776997 1479761892955512520833187)
    ·
      refine ⟨2219642839433268781249781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1479761892955512520833187 2219642839433268781249781)
      ·
        refine ⟨208091516196868948242167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2219642839433268781249781 208091516196868948242167)
        ·
          refine ⟨312137274295303422363251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208091516196868948242167 312137274295303422363251)
          ·
            refine ⟨468205911442955133544877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312137274295303422363251 468205911442955133544877)
            ·
              refine ⟨175577216791108175079329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 468205911442955133544877 175577216791108175079329)
              ·
                refine ⟨131682912593331131309497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175577216791108175079329 131682912593331131309497)
                ·
                  refine ⟨98762184444998348482123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131682912593331131309497 98762184444998348482123)
                  ·
                    rfl

theorem cell20_216381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_216381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216381 prefixEnd_216381 := by exact prefixLift 216381
  have htrace : WordTrace (prefixWord ++ tailWord_216381) baseStart_216381 baseEnd_216381 := by
    simpa [prefixWord, tailWord_216381, baseEnd_216381] using wordTrace_append hprefix tailTrace_216381
  have hstable : (prefixWord ++ tailWord_216381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216381).length < 2 ^ (prefixWord ++ tailWord_216381).sum := by decide
  have hdescent : baseEnd_216381 < baseStart_216381 := by decide
  rcases family_descends (prefixWord ++ tailWord_216381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216382 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_216382 : Nat := 118140960795 + 216382 * 2 ^ 59
def prefixEnd_216382 : Nat := 4983230072969 + 3 ^ 40 * 216382 * 2
def baseEnd_216382 : Nat := 98762640872246789448785

theorem tailTrace_216382 : CollatzResearch.WordTrace tailWord_216382 prefixEnd_216382 98762640872246789448785 := by
  unfold tailWord_216382
  simp only [CollatzResearch.WordTrace]
  refine ⟨986512487761555493570425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5261399934728295965708933 986512487761555493570425)
  ·
    refine ⟨739884365821166620177819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 986512487761555493570425 739884365821166620177819)
    ·
      refine ⟨1109826548731749930266729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 739884365821166620177819 1109826548731749930266729)
      ·
        refine ⟨832369911548812447700047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1109826548731749930266729 832369911548812447700047)
        ·
          refine ⟨1248554867323218671550071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832369911548812447700047 1248554867323218671550071)
          ·
            refine ⟨1872832300984828007325107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248554867323218671550071 1872832300984828007325107)
            ·
              refine ⟨2809248451477242010987661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1872832300984828007325107 2809248451477242010987661)
              ·
                refine ⟨1053468169303965754120373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2809248451477242010987661 1053468169303965754120373)
                ·
                  refine ⟨98762640872246789448785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1053468169303965754120373 98762640872246789448785)
                  ·
                    rfl

theorem cell20_216382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_216382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216382 prefixEnd_216382 := by exact prefixLift 216382
  have htrace : WordTrace (prefixWord ++ tailWord_216382) baseStart_216382 baseEnd_216382 := by
    simpa [prefixWord, tailWord_216382, baseEnd_216382] using wordTrace_append hprefix tailTrace_216382
  have hstable : (prefixWord ++ tailWord_216382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216382).length < 2 ^ (prefixWord ++ tailWord_216382).sum := by decide
  have hdescent : baseEnd_216382 < baseStart_216382 := by decide
  rcases family_descends (prefixWord ++ tailWord_216382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216385 : List Nat := [1, 2, 5, 2, 1, 3, 1, 1, 4]
def baseStart_216385 : Nat := 118140960795 + 216385 * 2 ^ 59
def prefixEnd_216385 : Nat := 4983230072969 + 3 ^ 40 * 216385 * 2
def baseEnd_216385 : Nat := 98764010153992112348773

theorem tailTrace_216385 : CollatzResearch.WordTrace tailWord_216385 prefixEnd_216385 98764010153992112348773 := by
  unfold tailWord_216385
  simp only [CollatzResearch.WordTrace]
  refine ⟨7892209321081575460922609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5261472880721050307281739 7892209321081575460922609)
  ·
    refine ⟨5919156990811181595691957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7892209321081575460922609 5919156990811181595691957)
    ·
      refine ⟨554920967888548274596121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5919156990811181595691957 554920967888548274596121)
      ·
        refine ⟨416190725916411205947091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554920967888548274596121 416190725916411205947091)
        ·
          refine ⟨624286088874616808920637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416190725916411205947091 624286088874616808920637)
          ·
            refine ⟨234107283327981303345239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 624286088874616808920637 234107283327981303345239)
            ·
              refine ⟨351160924991971955017859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234107283327981303345239 351160924991971955017859)
              ·
                refine ⟨526741387487957932526789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351160924991971955017859 526741387487957932526789)
                ·
                  refine ⟨98764010153992112348773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 526741387487957932526789 98764010153992112348773)
                  ·
                    rfl

theorem cell20_216385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 4].length) (baseStart_216385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216385 prefixEnd_216385 := by exact prefixLift 216385
  have htrace : WordTrace (prefixWord ++ tailWord_216385) baseStart_216385 baseEnd_216385 := by
    simpa [prefixWord, tailWord_216385, baseEnd_216385] using wordTrace_append hprefix tailTrace_216385
  have hstable : (prefixWord ++ tailWord_216385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216385).length < 2 ^ (prefixWord ++ tailWord_216385).sum := by decide
  have hdescent : baseEnd_216385 < baseStart_216385 := by decide
  rcases family_descends (prefixWord ++ tailWord_216385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216396 : List Nat := [2, 2, 1, 3, 2, 2, 1, 7]
def baseStart_216396 : Nat := 118140960795 + 216396 * 2 ^ 59
def prefixEnd_216396 : Nat := 4983230072969 + 3 ^ 40 * 216396 * 2
def baseEnd_216396 : Nat := 32923010284574987660687

theorem tailTrace_216396 : CollatzResearch.WordTrace tailWord_216396 prefixEnd_216396 32923010284574987660687 := by
  unfold tailWord_216396
  simp only [CollatzResearch.WordTrace]
  refine ⟨3946305262020862169786521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5261740349361149559715361 3946305262020862169786521)
  ·
    refine ⟨2959728946515646627339891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3946305262020862169786521 2959728946515646627339891)
    ·
      refine ⟨4439593419773469941009837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2959728946515646627339891 4439593419773469941009837)
      ·
        refine ⟨1664847532415051227878689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4439593419773469941009837 1664847532415051227878689)
        ·
          refine ⟨1248635649311288420909017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1664847532415051227878689 1248635649311288420909017)
          ·
            refine ⟨936476736983466315681763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1248635649311288420909017 936476736983466315681763)
            ·
              refine ⟨1404715105475199473522645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936476736983466315681763 1404715105475199473522645)
              ·
                refine ⟨32923010284574987660687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1404715105475199473522645 32923010284574987660687)
                ·
                  rfl

theorem cell20_216396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_216396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216396 prefixEnd_216396 := by exact prefixLift 216396
  have htrace : WordTrace (prefixWord ++ tailWord_216396) baseStart_216396 baseEnd_216396 := by
    simpa [prefixWord, tailWord_216396, baseEnd_216396] using wordTrace_append hprefix tailTrace_216396
  have hstable : (prefixWord ++ tailWord_216396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216396).length < 2 ^ (prefixWord ++ tailWord_216396).sum := by decide
  have hdescent : baseEnd_216396 < baseStart_216396 := by decide
  rcases family_descends (prefixWord ++ tailWord_216396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216430 : List Nat := [4, 1, 2, 4, 2, 7]
def baseStart_216430 : Nat := 118140960795 + 216430 * 2 ^ 59
def prefixEnd_216430 : Nat := 4983230072969 + 3 ^ 40 * 216430 * 2
def baseEnd_216430 : Nat := 3658687014080442809207

theorem tailTrace_216430 : CollatzResearch.WordTrace tailWord_216430 prefixEnd_216430 3658687014080442809207 := by
  unfold tailWord_216430
  simp only [CollatzResearch.WordTrace]
  refine ⟨986731325739818518288843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5262567070612365430873829 986731325739818518288843)
  ·
    refine ⟨1480096988609727777433265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 986731325739818518288843 1480096988609727777433265)
    ·
      refine ⟨1110072741457295833074949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1480096988609727777433265 1110072741457295833074949)
      ·
        refine ⟨208138639023242968701553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1110072741457295833074949 208138639023242968701553)
        ·
          refine ⟨156103979267432226526165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208138639023242968701553 156103979267432226526165)
          ·
            refine ⟨3658687014080442809207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 156103979267432226526165 3658687014080442809207)
            ·
              rfl

theorem cell20_216430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 7].length) (baseStart_216430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216430 prefixEnd_216430 := by exact prefixLift 216430
  have htrace : WordTrace (prefixWord ++ tailWord_216430) baseStart_216430 baseEnd_216430 := by
    simpa [prefixWord, tailWord_216430, baseEnd_216430] using wordTrace_append hprefix tailTrace_216430
  have hstable : (prefixWord ++ tailWord_216430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216430).length < 2 ^ (prefixWord ++ tailWord_216430).sum := by decide
  have hdescent : baseEnd_216430 < baseStart_216430 := by decide
  rcases family_descends (prefixWord ++ tailWord_216430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216441 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 5]
def baseStart_216441 : Nat := 118140960795 + 216441 * 2 ^ 59
def prefixEnd_216441 : Nat := 4983230072969 + 3 ^ 40 * 216441 * 2
def baseEnd_216441 : Nat := 98789570079904806481877

theorem tailTrace_216441 : CollatzResearch.WordTrace tailWord_216441 prefixEnd_216441 98789570079904806481877 := by
  unfold tailWord_216441
  simp only [CollatzResearch.WordTrace]
  refine ⟨7894251808878697024961177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5262834539252464683307451 7894251808878697024961177)
  ·
    refine ⟨5920688856659022768720883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7894251808878697024961177 5920688856659022768720883)
    ·
      refine ⟨8881033284988534153081325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5920688856659022768720883 8881033284988534153081325)
      ·
        refine ⟨3330387481870700307405497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8881033284988534153081325 3330387481870700307405497)
        ·
          refine ⟨2497790611403025230554123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3330387481870700307405497 2497790611403025230554123)
          ·
            refine ⟨3746685917104537845831185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497790611403025230554123 3746685917104537845831185)
            ·
              refine ⟨2810014437828403384373389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3746685917104537845831185 2810014437828403384373389)
              ·
                refine ⟨1053755414185651269140021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2810014437828403384373389 1053755414185651269140021)
                ·
                  refine ⟨98789570079904806481877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1053755414185651269140021 98789570079904806481877)
                  ·
                    rfl

theorem cell20_216441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_216441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216441 prefixEnd_216441 := by exact prefixLift 216441
  have htrace : WordTrace (prefixWord ++ tailWord_216441) baseStart_216441 baseEnd_216441 := by
    simpa [prefixWord, tailWord_216441, baseEnd_216441] using wordTrace_append hprefix tailTrace_216441
  have hstable : (prefixWord ++ tailWord_216441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216441).length < 2 ^ (prefixWord ++ tailWord_216441).sum := by decide
  have hdescent : baseEnd_216441 < baseStart_216441 := by decide
  rcases family_descends (prefixWord ++ tailWord_216441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216444 : List Nat := [2, 2, 2, 1, 1, 1, 5, 4, 2]
def baseStart_216444 : Nat := 118140960795 + 216444 * 2 ^ 59
def prefixEnd_216444 : Nat := 4983230072969 + 3 ^ 40 * 216444 * 2
def baseEnd_216444 : Nat := 98790939361650129381865

theorem tailTrace_216444 : CollatzResearch.WordTrace tailWord_216444 prefixEnd_216444 98790939361650129381865 := by
  unfold tailWord_216444
  simp only [CollatzResearch.WordTrace]
  refine ⟨3947180613933914268660193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5262907485245219024880257 3947180613933914268660193)
  ·
    refine ⟨2960385460450435701495145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3947180613933914268660193 2960385460450435701495145)
    ·
      refine ⟨2220289095337826776121359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2960385460450435701495145 2220289095337826776121359)
      ·
        refine ⟨3330433643006740164182039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2220289095337826776121359 3330433643006740164182039)
        ·
          refine ⟨4995650464510110246273059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3330433643006740164182039 4995650464510110246273059)
          ·
            refine ⟨7493475696765165369409589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4995650464510110246273059 7493475696765165369409589)
            ·
              refine ⟨702513346571734253382149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7493475696765165369409589 702513346571734253382149)
              ·
                refine ⟨131721252482200172509153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 702513346571734253382149 131721252482200172509153)
                ·
                  refine ⟨98790939361650129381865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131721252482200172509153 98790939361650129381865)
                  ·
                    rfl

theorem cell20_216444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_216444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216444 prefixEnd_216444 := by exact prefixLift 216444
  have htrace : WordTrace (prefixWord ++ tailWord_216444) baseStart_216444 baseEnd_216444 := by
    simpa [prefixWord, tailWord_216444, baseEnd_216444] using wordTrace_append hprefix tailTrace_216444
  have hstable : (prefixWord ++ tailWord_216444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216444).length < 2 ^ (prefixWord ++ tailWord_216444).sum := by decide
  have hdescent : baseEnd_216444 < baseStart_216444 := by decide
  rcases family_descends (prefixWord ++ tailWord_216444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216448 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 8]
def baseStart_216448 : Nat := 118140960795 + 216448 * 2 ^ 59
def prefixEnd_216448 : Nat := 4983230072969 + 3 ^ 40 * 216448 * 2
def baseEnd_216448 : Nat := 98792765070643893248515

theorem tailTrace_216448 : CollatzResearch.WordTrace tailWord_216448 prefixEnd_216448 98792765070643893248515 := by
  unfold tailWord_216448
  simp only [CollatzResearch.WordTrace]
  refine ⟨3947253559926668610232999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5263004746568891480310665 3947253559926668610232999)
  ·
    refine ⟨5920880339890002915349499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3947253559926668610232999 5920880339890002915349499)
    ·
      refine ⟨8881320509835004373024249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5920880339890002915349499 8881320509835004373024249)
      ·
        refine ⟨6660990382376253279768187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8881320509835004373024249 6660990382376253279768187)
        ·
          refine ⟨9991485573564379919652281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6660990382376253279768187 9991485573564379919652281)
          ·
            refine ⟨7493614180173284939739211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9991485573564379919652281 7493614180173284939739211)
            ·
              refine ⟨11240421270259927409608817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7493614180173284939739211 11240421270259927409608817)
              ·
                refine ⟨8430315952694945557206613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11240421270259927409608817 8430315952694945557206613)
                ·
                  refine ⟨98792765070643893248515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8430315952694945557206613 98792765070643893248515)
                  ·
                    rfl

theorem cell20_216448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_216448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216448 prefixEnd_216448 := by exact prefixLift 216448
  have htrace : WordTrace (prefixWord ++ tailWord_216448) baseStart_216448 baseEnd_216448 := by
    simpa [prefixWord, tailWord_216448, baseEnd_216448] using wordTrace_append hprefix tailTrace_216448
  have hstable : (prefixWord ++ tailWord_216448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216448).length < 2 ^ (prefixWord ++ tailWord_216448).sum := by decide
  have hdescent : baseEnd_216448 < baseStart_216448 := by decide
  rcases family_descends (prefixWord ++ tailWord_216448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216451 : List Nat := [1, 1, 1, 3, 5, 3, 1, 5]
def baseStart_216451 : Nat := 118140960795 + 216451 * 2 ^ 59
def prefixEnd_216451 : Nat := 4983230072969 + 3 ^ 40 * 216451 * 2
def baseEnd_216451 : Nat := 32931378117463072049501

theorem tailTrace_216451 : CollatzResearch.WordTrace tailWord_216451 prefixEnd_216451 32931378117463072049501 := by
  unfold tailWord_216451
  simp only [CollatzResearch.WordTrace]
  refine ⟨7894616538842468732825207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5263077692561645821883471 7894616538842468732825207)
  ·
    refine ⟨11841924808263703099237811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7894616538842468732825207 11841924808263703099237811)
    ·
      refine ⟨17762887212395554648856717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11841924808263703099237811 17762887212395554648856717)
      ·
        refine ⟨6661082704648332993321269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17762887212395554648856717 6661082704648332993321269)
        ·
          refine ⟨624476503560781218123869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6661082704648332993321269 624476503560781218123869)
          ·
            refine ⟨234178688835292956796451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 624476503560781218123869 234178688835292956796451)
            ·
              refine ⟨351268033252939435194677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234178688835292956796451 351268033252939435194677)
              ·
                refine ⟨32931378117463072049501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 351268033252939435194677 32931378117463072049501)
                ·
                  rfl

theorem cell20_216451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 5].length) (baseStart_216451 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216451 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216451 prefixEnd_216451 := by exact prefixLift 216451
  have htrace : WordTrace (prefixWord ++ tailWord_216451) baseStart_216451 baseEnd_216451 := by
    simpa [prefixWord, tailWord_216451, baseEnd_216451] using wordTrace_append hprefix tailTrace_216451
  have hstable : (prefixWord ++ tailWord_216451).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216451).length < 2 ^ (prefixWord ++ tailWord_216451).sum := by decide
  have hdescent : baseEnd_216451 < baseStart_216451 := by decide
  rcases family_descends (prefixWord ++ tailWord_216451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216468 : List Nat := [2, 4, 2, 1, 2, 2, 3, 4]
def baseStart_216468 : Nat := 118140960795 + 216468 * 2 ^ 59
def prefixEnd_216468 : Nat := 4983230072969 + 3 ^ 40 * 216468 * 2
def baseEnd_216468 : Nat := 32933964538537570860589

theorem tailTrace_216468 : CollatzResearch.WordTrace tailWord_216468 prefixEnd_216468 32933964538537570860589 := by
  unfold tailWord_216468
  simp only [CollatzResearch.WordTrace]
  refine ⟨3947618289890440318097029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5263491053187253757462705 3947618289890440318097029)
  ·
    refine ⟨740178429354457559643193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3947618289890440318097029 740178429354457559643193)
    ·
      refine ⟨555133822015843169732395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 740178429354457559643193 555133822015843169732395)
      ·
        refine ⟨832700733023764754598593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555133822015843169732395 832700733023764754598593)
        ·
          refine ⟨624525549767823565948945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 832700733023764754598593 624525549767823565948945)
          ·
            refine ⟨468394162325867674461709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 624525549767823565948945 468394162325867674461709)
            ·
              refine ⟨175647810872200377923141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 468394162325867674461709 175647810872200377923141)
              ·
                refine ⟨32933964538537570860589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175647810872200377923141 32933964538537570860589)
                ·
                  rfl

theorem cell20_216468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_216468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216468 prefixEnd_216468 := by exact prefixLift 216468
  have htrace : WordTrace (prefixWord ++ tailWord_216468) baseStart_216468 baseEnd_216468 := by
    simpa [prefixWord, tailWord_216468, baseEnd_216468] using wordTrace_append hprefix tailTrace_216468
  have hstable : (prefixWord ++ tailWord_216468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216468).length < 2 ^ (prefixWord ++ tailWord_216468).sum := by decide
  have hdescent : baseEnd_216468 < baseStart_216468 := by decide
  rcases family_descends (prefixWord ++ tailWord_216468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216503 : List Nat := [1, 1, 3, 1, 3, 2, 4, 1, 4]
def baseStart_216503 : Nat := 118140960795 + 216503 * 2 ^ 59
def prefixEnd_216503 : Nat := 4983230072969 + 3 ^ 40 * 216503 * 2
def baseEnd_216503 : Nat := 98817868569308146414957

theorem tailTrace_216503 : CollatzResearch.WordTrace tailWord_216503 prefixEnd_216503 98817868569308146414957 := by
  unfold tailWord_216503
  simp only [CollatzResearch.WordTrace]
  refine ⟨7896513134654081613718163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5264342089769387742478775 7896513134654081613718163)
  ·
    refine ⟨11844769701981122420577245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7896513134654081613718163 11844769701981122420577245)
    ·
      refine ⟨4441788638242920907716467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11844769701981122420577245 4441788638242920907716467)
      ·
        refine ⟨6662682957364381361574701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4441788638242920907716467 6662682957364381361574701)
        ·
          refine ⟨2498506109011643010590513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6662682957364381361574701 2498506109011643010590513)
          ·
            refine ⟨1873879581758732257942885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2498506109011643010590513 1873879581758732257942885)
            ·
              refine ⟨351352421579762298364291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1873879581758732257942885 351352421579762298364291)
              ·
                refine ⟨527028632369643447546437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351352421579762298364291 527028632369643447546437)
                ·
                  refine ⟨98817868569308146414957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 527028632369643447546437 98817868569308146414957)
                  ·
                    rfl

theorem cell20_216503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 4].length) (baseStart_216503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216503 prefixEnd_216503 := by exact prefixLift 216503
  have htrace : WordTrace (prefixWord ++ tailWord_216503) baseStart_216503 baseEnd_216503 := by
    simpa [prefixWord, tailWord_216503, baseEnd_216503] using wordTrace_append hprefix tailTrace_216503
  have hstable : (prefixWord ++ tailWord_216503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216503).length < 2 ^ (prefixWord ++ tailWord_216503).sum := by decide
  have hdescent : baseEnd_216503 < baseStart_216503 := by decide
  rcases family_descends (prefixWord ++ tailWord_216503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216510 : List Nat := [4, 2, 1, 1, 1, 1, 1, 9]
def baseStart_216510 : Nat := 118140960795 + 216510 * 2 ^ 59
def prefixEnd_216510 : Nat := 4983230072969 + 3 ^ 40 * 216510 * 2
def baseEnd_216510 : Nat := 32940354520015744393865

theorem tailTrace_216510 : CollatzResearch.WordTrace tailWord_216510 prefixEnd_216510 32940354520015744393865 := by
  unfold tailWord_216510
  simp only [CollatzResearch.WordTrace]
  refine ⟨987096055703590226152873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5264512297085814539481989 987096055703590226152873)
  ·
    refine ⟨740322041777692669614655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 987096055703590226152873 740322041777692669614655)
    ·
      refine ⟨1110483062666539004421983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 740322041777692669614655 1110483062666539004421983)
      ·
        refine ⟨1665724593999808506632975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1110483062666539004421983 1665724593999808506632975)
        ·
          refine ⟨2498586890999712759949463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1665724593999808506632975 2498586890999712759949463)
          ·
            refine ⟨3747880336499569139924195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498586890999712759949463 3747880336499569139924195)
            ·
              refine ⟨5621820504749353709886293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3747880336499569139924195 5621820504749353709886293)
              ·
                refine ⟨32940354520015744393865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5621820504749353709886293 32940354520015744393865)
                ·
                  rfl

theorem cell20_216510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_216510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216510 prefixEnd_216510 := by exact prefixLift 216510
  have htrace : WordTrace (prefixWord ++ tailWord_216510) baseStart_216510 baseEnd_216510 := by
    simpa [prefixWord, tailWord_216510, baseEnd_216510] using wordTrace_append hprefix tailTrace_216510
  have hstable : (prefixWord ++ tailWord_216510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216510).length < 2 ^ (prefixWord ++ tailWord_216510).sum := by decide
  have hdescent : baseEnd_216510 < baseStart_216510 := by decide
  rcases family_descends (prefixWord ++ tailWord_216510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216537 : List Nat := [1, 2, 1, 2, 4, 4, 1, 3, 2]
def baseStart_216537 : Nat := 118140960795 + 216537 * 2 ^ 59
def prefixEnd_216537 : Nat := 4983230072969 + 3 ^ 40 * 216537 * 2
def baseEnd_216537 : Nat := 98833387095755139281485

theorem tailTrace_216537 : CollatzResearch.WordTrace tailWord_216537 prefixEnd_216537 98833387095755139281485 := by
  unfold tailWord_216537
  simp only [CollatzResearch.WordTrace]
  refine ⟨7897753216530905420455865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5265168811020603613637243 7897753216530905420455865)
  ·
    refine ⟨5923314912398179065341899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7897753216530905420455865 5923314912398179065341899)
    ·
      refine ⟨8884972368597268598012849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5923314912398179065341899 8884972368597268598012849)
      ·
        refine ⟨6663729276447951448509637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8884972368597268598012849 6663729276447951448509637)
        ·
          refine ⟨1249449239333990896595557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6663729276447951448509637 1249449239333990896595557)
          ·
            refine ⟨234271732375123293111667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1249449239333990896595557 234271732375123293111667)
            ·
              refine ⟨351407598562684939667501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234271732375123293111667 351407598562684939667501)
              ·
                refine ⟨131777849461006852375313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351407598562684939667501 131777849461006852375313)
                ·
                  refine ⟨98833387095755139281485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131777849461006852375313 98833387095755139281485)
                  ·
                    rfl

theorem cell20_216537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 2].length) (baseStart_216537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216537 prefixEnd_216537 := by exact prefixLift 216537
  have htrace : WordTrace (prefixWord ++ tailWord_216537) baseStart_216537 baseEnd_216537 := by
    simpa [prefixWord, tailWord_216537, baseEnd_216537] using wordTrace_append hprefix tailTrace_216537
  have hstable : (prefixWord ++ tailWord_216537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216537).length < 2 ^ (prefixWord ++ tailWord_216537).sum := by decide
  have hdescent : baseEnd_216537 < baseStart_216537 := by decide
  rcases family_descends (prefixWord ++ tailWord_216537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216554 : List Nat := [3, 1, 3, 1, 4, 1, 3, 2, 2]
def baseStart_216554 : Nat := 118140960795 + 216554 * 2 ^ 59
def prefixEnd_216554 : Nat := 4983230072969 + 3 ^ 40 * 216554 * 2
def baseEnd_216554 : Nat := 98841146358978635714749

theorem tailTrace_216554 : CollatzResearch.WordTrace tailWord_216554 prefixEnd_216554 98841146358978635714749 := by
  unfold tailWord_216554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1974593314367329330956179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5265582171646211549216477 1974593314367329330956179)
  ·
    refine ⟨2961889971550993996434269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1974593314367329330956179 2961889971550993996434269)
    ·
      refine ⟨1110708739331622748662851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2961889971550993996434269 1110708739331622748662851)
      ·
        refine ⟨1666063108997434122994277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1110708739331622748662851 1666063108997434122994277)
        ·
          refine ⟨312386832937018898061427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1666063108997434122994277 312386832937018898061427)
          ·
            refine ⟨468580249405528347092141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312386832937018898061427 468580249405528347092141)
            ·
              refine ⟨175717593527073130159553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 468580249405528347092141 175717593527073130159553)
              ·
                refine ⟨131788195145304847619665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175717593527073130159553 131788195145304847619665)
                ·
                  refine ⟨98841146358978635714749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131788195145304847619665 98841146358978635714749)
                  ·
                    rfl

theorem cell20_216554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_216554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216554 prefixEnd_216554 := by exact prefixLift 216554
  have htrace : WordTrace (prefixWord ++ tailWord_216554) baseStart_216554 baseEnd_216554 := by
    simpa [prefixWord, tailWord_216554, baseEnd_216554] using wordTrace_append hprefix tailTrace_216554
  have hstable : (prefixWord ++ tailWord_216554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216554).length < 2 ^ (prefixWord ++ tailWord_216554).sum := by decide
  have hdescent : baseEnd_216554 < baseStart_216554 := by decide
  rcases family_descends (prefixWord ++ tailWord_216554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216565 : List Nat := [1, 3, 5, 1, 1, 1, 1, 7]
def baseStart_216565 : Nat := 118140960795 + 216565 * 2 ^ 59
def prefixEnd_216565 : Nat := 4983230072969 + 3 ^ 40 * 216565 * 2
def baseEnd_216565 : Nat := 32948722352903828782679

theorem tailTrace_216565 : CollatzResearch.WordTrace tailWord_216565 prefixEnd_216565 32948722352903828782679 := by
  unfold tailWord_216565
  simp only [CollatzResearch.WordTrace]
  refine ⟨7898774460429466202475149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5265849640286310801650099 7898774460429466202475149)
  ·
    refine ⟨2962040422661049825928181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7898774460429466202475149 2962040422661049825928181)
    ·
      refine ⟨277691289624473421180767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2962040422661049825928181 277691289624473421180767)
      ·
        refine ⟨416536934436710131771151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277691289624473421180767 416536934436710131771151)
        ·
          refine ⟨624805401655065197656727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416536934436710131771151 624805401655065197656727)
          ·
            refine ⟨937208102482597796485091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624805401655065197656727 937208102482597796485091)
            ·
              refine ⟨1405812153723896694727637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937208102482597796485091 1405812153723896694727637)
              ·
                refine ⟨32948722352903828782679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1405812153723896694727637 32948722352903828782679)
                ·
                  rfl

theorem cell20_216565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 7].length) (baseStart_216565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216565 prefixEnd_216565 := by exact prefixLift 216565
  have htrace : WordTrace (prefixWord ++ tailWord_216565) baseStart_216565 baseEnd_216565 := by
    simpa [prefixWord, tailWord_216565, baseEnd_216565] using wordTrace_append hprefix tailTrace_216565
  have hstable : (prefixWord ++ tailWord_216565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216565).length < 2 ^ (prefixWord ++ tailWord_216565).sum := by decide
  have hdescent : baseEnd_216565 < baseStart_216565 := by decide
  rcases family_descends (prefixWord ++ tailWord_216565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216586 : List Nat := [3, 1, 2, 2, 2, 2, 2, 6]
def baseStart_216586 : Nat := 118140960795 + 216586 * 2 ^ 59
def prefixEnd_216586 : Nat := 4983230072969 + 3 ^ 40 * 216586 * 2
def baseEnd_216586 : Nat := 32951917343642915549317

theorem tailTrace_216586 : CollatzResearch.WordTrace tailWord_216586 prefixEnd_216586 32951917343642915549317 := by
  unfold tailWord_216586
  simp only [CollatzResearch.WordTrace]
  refine ⟨1974885098338346697247403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5266360262235591192659741 1974885098338346697247403)
  ·
    refine ⟨2962327647507520045871105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1974885098338346697247403 2962327647507520045871105)
    ·
      refine ⟨2221745735630640034403329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2962327647507520045871105 2221745735630640034403329)
      ·
        refine ⟨1666309301722980025802497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2221745735630640034403329 1666309301722980025802497)
        ·
          refine ⟨1249731976292235019351873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1666309301722980025802497 1249731976292235019351873)
          ·
            refine ⟨937298982219176264513905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1249731976292235019351873 937298982219176264513905)
            ·
              refine ⟨702974236664382198385429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937298982219176264513905 702974236664382198385429)
              ·
                refine ⟨32951917343642915549317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 702974236664382198385429 32951917343642915549317)
                ·
                  rfl

theorem cell20_216586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_216586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216586 prefixEnd_216586 := by exact prefixLift 216586
  have htrace : WordTrace (prefixWord ++ tailWord_216586) baseStart_216586 baseEnd_216586 := by
    simpa [prefixWord, tailWord_216586, baseEnd_216586] using wordTrace_append hprefix tailTrace_216586
  have hstable : (prefixWord ++ tailWord_216586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216586).length < 2 ^ (prefixWord ++ tailWord_216586).sum := by decide
  have hdescent : baseEnd_216586 < baseStart_216586 := by decide
  rcases family_descends (prefixWord ++ tailWord_216586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216610 : List Nat := [3, 3, 1, 1, 1, 1, 3, 4, 3]
def baseStart_216610 : Nat := 118140960795 + 216610 * 2 ^ 59
def prefixEnd_216610 : Nat := 4983230072969 + 3 ^ 40 * 216610 * 2
def baseEnd_216610 : Nat := 98866706284891329847853

theorem tailTrace_216610 : CollatzResearch.WordTrace tailWord_216610 prefixEnd_216610 98866706284891329847853 := by
  unfold tailWord_216610
  simp only [CollatzResearch.WordTrace]
  refine ⟨1975103936316609721965821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5266943830177625925242189 1975103936316609721965821)
  ·
    refine ⟨740663976118728645737183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1975103936316609721965821 740663976118728645737183)
    ·
      refine ⟨1110995964178092968605775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 740663976118728645737183 1110995964178092968605775)
      ·
        refine ⟨1666493946267139452908663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1110995964178092968605775 1666493946267139452908663)
        ·
          refine ⟨2499740919400709179362995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1666493946267139452908663 2499740919400709179362995)
          ·
            refine ⟨3749611379101063769044493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2499740919400709179362995 3749611379101063769044493)
            ·
              refine ⟨1406104267162898913391685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3749611379101063769044493 1406104267162898913391685)
              ·
                refine ⟨263644550093043546260941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1406104267162898913391685 263644550093043546260941)
                ·
                  refine ⟨98866706284891329847853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263644550093043546260941 98866706284891329847853)
                  ·
                    rfl

theorem cell20_216610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_216610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216610 prefixEnd_216610 := by exact prefixLift 216610
  have htrace : WordTrace (prefixWord ++ tailWord_216610) baseStart_216610 baseEnd_216610 := by
    simpa [prefixWord, tailWord_216610, baseEnd_216610] using wordTrace_append hprefix tailTrace_216610
  have hstable : (prefixWord ++ tailWord_216610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216610).length < 2 ^ (prefixWord ++ tailWord_216610).sum := by decide
  have hdescent : baseEnd_216610 < baseStart_216610 := by decide
  rcases family_descends (prefixWord ++ tailWord_216610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216641 : List Nat := [1, 2, 5, 1, 1, 1, 5, 4]
def baseStart_216641 : Nat := 118140960795 + 216641 * 2 ^ 59
def prefixEnd_216641 : Nat := 4983230072969 + 3 ^ 40 * 216641 * 2
def baseEnd_216641 : Nat := 32960285176530999938131

theorem tailTrace_216641 : CollatzResearch.WordTrace tailWord_216641 prefixEnd_216641 32960285176530999938131 := by
  unfold tailWord_216641
  simp only [CollatzResearch.WordTrace]
  refine ⟨7901546408154131182241777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5267697605436087454827851 7901546408154131182241777)
  ·
    refine ⟨5926159806115598386681333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7901546408154131182241777 5926159806115598386681333)
    ·
      refine ⟨555577481823337348751375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5926159806115598386681333 555577481823337348751375)
      ·
        refine ⟨833366222735006023127063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555577481823337348751375 833366222735006023127063)
        ·
          refine ⟨1250049334102509034690595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833366222735006023127063 1250049334102509034690595)
          ·
            refine ⟨1875074001153763552035893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1250049334102509034690595 1875074001153763552035893)
            ·
              refine ⟨175788187608165333003365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1875074001153763552035893 175788187608165333003365)
              ·
                refine ⟨32960285176530999938131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175788187608165333003365 32960285176530999938131)
                ·
                  rfl

theorem cell20_216641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 4].length) (baseStart_216641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216641 prefixEnd_216641 := by exact prefixLift 216641
  have htrace : WordTrace (prefixWord ++ tailWord_216641) baseStart_216641 baseEnd_216641 := by
    simpa [prefixWord, tailWord_216641, baseEnd_216641] using wordTrace_append hprefix tailTrace_216641
  have hstable : (prefixWord ++ tailWord_216641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216641).length < 2 ^ (prefixWord ++ tailWord_216641).sum := by decide
  have hdescent : baseEnd_216641 < baseStart_216641 := by decide
  rcases family_descends (prefixWord ++ tailWord_216641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216727 : List Nat := [1, 1, 3, 3, 2, 3, 3, 2, 2]
def baseStart_216727 : Nat := 118140960795 + 216727 * 2 ^ 59
def prefixEnd_216727 : Nat := 4983230072969 + 3 ^ 40 * 216727 * 2
def baseEnd_216727 : Nat := 98920108272958922947375

theorem tailTrace_216727 : CollatzResearch.WordTrace tailWord_216727 prefixEnd_216727 98920108272958922947375 := by
  unfold tailWord_216727
  simp only [CollatzResearch.WordTrace]
  refine ⟨7904683085842567869872435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5269788723895045246581623 7904683085842567869872435)
  ·
    refine ⟨11857024628763851804808653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7904683085842567869872435 11857024628763851804808653)
    ·
      refine ⟨4446384235786444426803245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11857024628763851804808653 4446384235786444426803245)
      ·
        refine ⟨1667394088419916660051217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4446384235786444426803245 1667394088419916660051217)
        ·
          refine ⟨1250545566314937495038413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1667394088419916660051217 1250545566314937495038413)
          ·
            refine ⟨468954587368101560639405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1250545566314937495038413 468954587368101560639405)
            ·
              refine ⟨175857970263038085239777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 468954587368101560639405 175857970263038085239777)
              ·
                refine ⟨131893477697278563929833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175857970263038085239777 131893477697278563929833)
                ·
                  refine ⟨98920108272958922947375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131893477697278563929833 98920108272958922947375)
                  ·
                    rfl

theorem cell20_216727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 2].length) (baseStart_216727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216727 prefixEnd_216727 := by exact prefixLift 216727
  have htrace : WordTrace (prefixWord ++ tailWord_216727) baseStart_216727 baseEnd_216727 := by
    simpa [prefixWord, tailWord_216727, baseEnd_216727] using wordTrace_append hprefix tailTrace_216727
  have hstable : (prefixWord ++ tailWord_216727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216727).length < 2 ^ (prefixWord ++ tailWord_216727).sum := by decide
  have hdescent : baseEnd_216727 < baseStart_216727 := by decide
  rcases family_descends (prefixWord ++ tailWord_216727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216752 : List Nat := [2, 1, 1, 1, 2, 1, 4, 4, 4]
def baseStart_216752 : Nat := 118140960795 + 216752 * 2 ^ 59
def prefixEnd_216752 : Nat := 4983230072969 + 3 ^ 40 * 216752 * 2
def baseEnd_216752 : Nat := 98931518954169947113939

theorem tailTrace_216752 : CollatzResearch.WordTrace tailWord_216752 prefixEnd_216752 98931518954169947113939 := by
  unfold tailWord_216752
  simp only [CollatzResearch.WordTrace]
  refine ⟨3952797455375998569766255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5270396607167998093021673 3952797455375998569766255)
  ·
    refine ⟨5929196183063997854649383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3952797455375998569766255 5929196183063997854649383)
    ·
      refine ⟨8893794274595996781974075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5929196183063997854649383 8893794274595996781974075)
      ·
        refine ⟨13340691411893995172961113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8893794274595996781974075 13340691411893995172961113)
        ·
          refine ⟨10005518558920496379720835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13340691411893995172961113 10005518558920496379720835)
          ·
            refine ⟨15008277838380744569581253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10005518558920496379720835 15008277838380744569581253)
            ·
              refine ⟨2814052094696389606796485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15008277838380744569581253 2814052094696389606796485)
              ·
                refine ⟨527634767755573051274341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2814052094696389606796485 527634767755573051274341)
                ·
                  refine ⟨98931518954169947113939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 527634767755573051274341 98931518954169947113939)
                  ·
                    rfl

theorem cell20_216752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_216752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216752 prefixEnd_216752 := by exact prefixLift 216752
  have htrace : WordTrace (prefixWord ++ tailWord_216752) baseStart_216752 baseEnd_216752 := by
    simpa [prefixWord, tailWord_216752, baseEnd_216752] using wordTrace_append hprefix tailTrace_216752
  have hstable : (prefixWord ++ tailWord_216752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216752).length < 2 ^ (prefixWord ++ tailWord_216752).sum := by decide
  have hdescent : baseEnd_216752 < baseStart_216752 := by decide
  rcases family_descends (prefixWord ++ tailWord_216752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216820 : List Nat := [2, 6, 1, 1, 1, 1, 1, 5, 2]
def baseStart_216820 : Nat := 118140960795 + 216820 * 2 ^ 59
def prefixEnd_216820 : Nat := 4983230072969 + 3 ^ 40 * 216820 * 2
def baseEnd_216820 : Nat := 98962556007063932846995

theorem tailTrace_216820 : CollatzResearch.WordTrace tailWord_216820 prefixEnd_216820 98962556007063932846995 := by
  unfold tailWord_216820
  simp only [CollatzResearch.WordTrace]
  refine ⟨3954037537252822376503957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5272050049670429835338609 3954037537252822376503957)
  ·
    refine ⟨185345509558726048898623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3954037537252822376503957 185345509558726048898623)
    ·
      refine ⟨278018264338089073347935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185345509558726048898623 278018264338089073347935)
      ·
        refine ⟨417027396507133610021903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278018264338089073347935 417027396507133610021903)
        ·
          refine ⟨625541094760700415032855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417027396507133610021903 625541094760700415032855)
          ·
            refine ⟨938311642141050622549283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625541094760700415032855 938311642141050622549283)
            ·
              refine ⟨1407467463211575933823925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938311642141050622549283 1407467463211575933823925)
              ·
                refine ⟨131950074676085243795993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1407467463211575933823925 131950074676085243795993)
                ·
                  refine ⟨98962556007063932846995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131950074676085243795993 98962556007063932846995)
                  ·
                    rfl

theorem cell20_216820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_216820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216820 prefixEnd_216820 := by exact prefixLift 216820
  have htrace : WordTrace (prefixWord ++ tailWord_216820) baseStart_216820 baseEnd_216820 := by
    simpa [prefixWord, tailWord_216820, baseEnd_216820] using wordTrace_append hprefix tailTrace_216820
  have hstable : (prefixWord ++ tailWord_216820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216820).length < 2 ^ (prefixWord ++ tailWord_216820).sum := by decide
  have hdescent : baseEnd_216820 < baseStart_216820 := by decide
  rcases family_descends (prefixWord ++ tailWord_216820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216828 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 6]
def baseStart_216828 : Nat := 118140960795 + 216828 * 2 ^ 59
def prefixEnd_216828 : Nat := 4983230072969 + 3 ^ 40 * 216828 * 2
def baseEnd_216828 : Nat := 98966207425051460580295

theorem tailTrace_216828 : CollatzResearch.WordTrace tailWord_216828 prefixEnd_216828 98966207425051460580295 := by
  unfold tailWord_216828
  simp only [CollatzResearch.WordTrace]
  refine ⟨3954183429238331059649569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5272244572317774746199425 3954183429238331059649569)
  ·
    refine ⟨2965637571928748294737177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3954183429238331059649569 2965637571928748294737177)
    ·
      refine ⟨2224228178946561221052883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2965637571928748294737177 2224228178946561221052883)
      ·
        refine ⟨3336342268419841831579325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2224228178946561221052883 3336342268419841831579325)
        ·
          refine ⟨1251128350657440686842247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3336342268419841831579325 1251128350657440686842247)
          ·
            refine ⟨1876692525986161030263371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251128350657440686842247 1876692525986161030263371)
            ·
              refine ⟨2815038788979241545395057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876692525986161030263371 2815038788979241545395057)
              ·
                refine ⟨2111279091734431159046293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2815038788979241545395057 2111279091734431159046293)
                ·
                  refine ⟨98966207425051460580295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2111279091734431159046293 98966207425051460580295)
                  ·
                    rfl

theorem cell20_216828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_216828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216828 prefixEnd_216828 := by exact prefixLift 216828
  have htrace : WordTrace (prefixWord ++ tailWord_216828) baseStart_216828 baseEnd_216828 := by
    simpa [prefixWord, tailWord_216828, baseEnd_216828] using wordTrace_append hprefix tailTrace_216828
  have hstable : (prefixWord ++ tailWord_216828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216828).length < 2 ^ (prefixWord ++ tailWord_216828).sum := by decide
  have hdescent : baseEnd_216828 < baseStart_216828 := by decide
  rcases family_descends (prefixWord ++ tailWord_216828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216855 : List Nat := [1, 1, 3, 4, 2, 2, 3, 1, 3]
def baseStart_216855 : Nat := 118140960795 + 216855 * 2 ^ 59
def prefixEnd_216855 : Nat := 4983230072969 + 3 ^ 40 * 216855 * 2
def baseEnd_216855 : Nat := 98978530960759366680185

theorem tailTrace_216855 : CollatzResearch.WordTrace tailWord_216855 prefixEnd_216855 98978530960759366680185 := by
  unfold tailWord_216855
  simp only [CollatzResearch.WordTrace]
  refine ⟨7909351629378845730532019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5272901086252563820354679 7909351629378845730532019)
  ·
    refine ⟨11864027444068268595798029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7909351629378845730532019 11864027444068268595798029)
    ·
      refine ⟨4449010291525600723424261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11864027444068268595798029 4449010291525600723424261)
      ·
        refine ⟨834189429661050135642049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4449010291525600723424261 834189429661050135642049)
        ·
          refine ⟨625642072245787601731537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 834189429661050135642049 625642072245787601731537)
          ·
            refine ⟨469231554184340701298653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 625642072245787601731537 469231554184340701298653)
            ·
              refine ⟨175961832819127762986995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 469231554184340701298653 175961832819127762986995)
              ·
                refine ⟨263942749228691644480493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175961832819127762986995 263942749228691644480493)
                ·
                  refine ⟨98978530960759366680185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263942749228691644480493 98978530960759366680185)
                  ·
                    rfl

theorem cell20_216855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 3].length) (baseStart_216855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216855 prefixEnd_216855 := by exact prefixLift 216855
  have htrace : WordTrace (prefixWord ++ tailWord_216855) baseStart_216855 baseEnd_216855 := by
    simpa [prefixWord, tailWord_216855, baseEnd_216855] using wordTrace_append hprefix tailTrace_216855
  have hstable : (prefixWord ++ tailWord_216855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216855).length < 2 ^ (prefixWord ++ tailWord_216855).sum := by decide
  have hdescent : baseEnd_216855 < baseStart_216855 := by decide
  rcases family_descends (prefixWord ++ tailWord_216855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216869 : List Nat := [1, 3, 1, 2, 3, 4, 2, 4]
def baseStart_216869 : Nat := 118140960795 + 216869 * 2 ^ 59
def prefixEnd_216869 : Nat := 4983230072969 + 3 ^ 40 * 216869 * 2
def baseEnd_216869 : Nat := 32994973647412513404487

theorem tailTrace_216869 : CollatzResearch.WordTrace tailWord_216869 prefixEnd_216869 32994973647412513404487 := by
  unfold tailWord_216869
  simp only [CollatzResearch.WordTrace]
  refine ⟨7909862251328126121541661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5273241500885417414361107 7909862251328126121541661)
  ·
    refine ⟨2966198344248047295578123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7909862251328126121541661 2966198344248047295578123)
    ·
      refine ⟨4449297516372070943367185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2966198344248047295578123 4449297516372070943367185)
      ·
        refine ⟨3336973137279053207525389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4449297516372070943367185 3336973137279053207525389)
        ·
          refine ⟨1251364926479644952822021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3336973137279053207525389 1251364926479644952822021)
          ·
            refine ⟨234630923714933428654129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1251364926479644952822021 234630923714933428654129)
            ·
              refine ⟨175973192786200071490597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234630923714933428654129 175973192786200071490597)
              ·
                refine ⟨32994973647412513404487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175973192786200071490597 32994973647412513404487)
                ·
                  rfl

theorem cell20_216869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 4].length) (baseStart_216869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216869 prefixEnd_216869 := by exact prefixLift 216869
  have htrace : WordTrace (prefixWord ++ tailWord_216869) baseStart_216869 baseEnd_216869 := by
    simpa [prefixWord, tailWord_216869, baseEnd_216869] using wordTrace_append hprefix tailTrace_216869
  have hstable : (prefixWord ++ tailWord_216869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216869).length < 2 ^ (prefixWord ++ tailWord_216869).sum := by decide
  have hdescent : baseEnd_216869 < baseStart_216869 := by decide
  rcases family_descends (prefixWord ++ tailWord_216869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216890 : List Nat := [3, 1, 1, 1, 5, 3, 6]
def baseStart_216890 : Nat := 118140960795 + 216890 * 2 ^ 59
def prefixEnd_216890 : Nat := 4983230072969 + 3 ^ 40 * 216890 * 2
def baseEnd_216890 : Nat := 10999389546050533390375

theorem tailTrace_216890 : CollatzResearch.WordTrace tailWord_216890 prefixEnd_216890 10999389546050533390375 := by
  unfold tailWord_216890
  simp only [CollatzResearch.WordTrace]
  refine ⟨1977657046063011677014031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5273752122834697805370749 1977657046063011677014031)
  ·
    refine ⟨2966485569094517515521047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1977657046063011677014031 2966485569094517515521047)
    ·
      refine ⟨4449728353641776273281571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2966485569094517515521047 4449728353641776273281571)
      ·
        refine ⟨6674592530462664409922357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4449728353641776273281571 6674592530462664409922357)
        ·
          refine ⟨625743049730874788430221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6674592530462664409922357 625743049730874788430221)
          ·
            refine ⟨234653643649078045661333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 625743049730874788430221 234653643649078045661333)
            ·
              refine ⟨10999389546050533390375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 234653643649078045661333 10999389546050533390375)
              ·
                rfl

theorem cell20_216890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 6].length) (baseStart_216890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216890 prefixEnd_216890 := by exact prefixLift 216890
  have htrace : WordTrace (prefixWord ++ tailWord_216890) baseStart_216890 baseEnd_216890 := by
    simpa [prefixWord, tailWord_216890, baseEnd_216890] using wordTrace_append hprefix tailTrace_216890
  have hstable : (prefixWord ++ tailWord_216890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216890).length < 2 ^ (prefixWord ++ tailWord_216890).sum := by decide
  have hdescent : baseEnd_216890 < baseStart_216890 := by decide
  rcases family_descends (prefixWord ++ tailWord_216890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216914 : List Nat := [3, 2, 2, 1, 1, 4, 1, 3, 3]
def baseStart_216914 : Nat := 118140960795 + 216914 * 2 ^ 59
def prefixEnd_216914 : Nat := 4983230072969 + 3 ^ 40 * 216914 * 2
def baseEnd_216914 : Nat := 99005460168417383713277

theorem tailTrace_216914 : CollatzResearch.WordTrace tailWord_216914 prefixEnd_216914 99005460168417383713277 := by
  unfold tailWord_216914
  simp only [CollatzResearch.WordTrace]
  refine ⟨1977875884041274701732449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5274335690776732537953197 1977875884041274701732449)
  ·
    refine ⟨1483406913030956026299337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1977875884041274701732449 1483406913030956026299337)
    ·
      refine ⟨1112555184773217019724503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1483406913030956026299337 1112555184773217019724503)
      ·
        refine ⟨1668832777159825529586755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1112555184773217019724503 1668832777159825529586755)
        ·
          refine ⟨2503249165739738294380133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1668832777159825529586755 2503249165739738294380133)
          ·
            refine ⟨469359218576200930196275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2503249165739738294380133 469359218576200930196275)
            ·
              refine ⟨704038827864301395294413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469359218576200930196275 704038827864301395294413)
              ·
                refine ⟨264014560449113023235405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 704038827864301395294413 264014560449113023235405)
                ·
                  refine ⟨99005460168417383713277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264014560449113023235405 99005460168417383713277)
                  ·
                    rfl

theorem cell20_216914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_216914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216914 prefixEnd_216914 := by exact prefixLift 216914
  have htrace : WordTrace (prefixWord ++ tailWord_216914) baseStart_216914 baseEnd_216914 := by
    simpa [prefixWord, tailWord_216914, baseEnd_216914] using wordTrace_append hprefix tailTrace_216914
  have hstable : (prefixWord ++ tailWord_216914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216914).length < 2 ^ (prefixWord ++ tailWord_216914).sum := by decide
  have hdescent : baseEnd_216914 < baseStart_216914 := by decide
  rcases family_descends (prefixWord ++ tailWord_216914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216993 : List Nat := [1, 2, 3, 4, 2, 1, 2, 3, 2]
def baseStart_216993 : Nat := 118140960795 + 216993 * 2 ^ 59
def prefixEnd_216993 : Nat := 4983230072969 + 3 ^ 40 * 216993 * 2
def baseEnd_216993 : Nat := 99041517921044220079621

theorem tailTrace_216993 : CollatzResearch.WordTrace tailWord_216993 prefixEnd_216993 99041517921044220079621 := by
  unfold tailWord_216993
  simp only [CollatzResearch.WordTrace]
  refine ⟨7914384902878895299055633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5276256601919263532703755 7914384902878895299055633)
  ·
    refine ⟨5935788677159171474291725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7914384902878895299055633 5935788677159171474291725)
    ·
      refine ⟨2225920753934689302859397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5935788677159171474291725 2225920753934689302859397)
      ·
        refine ⟨417360141362754244286137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2225920753934689302859397 417360141362754244286137)
        ·
          refine ⟨313020106022065683214603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417360141362754244286137 313020106022065683214603)
          ·
            refine ⟨469530159033098524821905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313020106022065683214603 469530159033098524821905)
            ·
              refine ⟨352147619274823893616429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469530159033098524821905 352147619274823893616429)
              ·
                refine ⟨132055357228058960106161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352147619274823893616429 132055357228058960106161)
                ·
                  refine ⟨99041517921044220079621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132055357228058960106161 99041517921044220079621)
                  ·
                    rfl

theorem cell20_216993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 2].length) (baseStart_216993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_216993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_216993 prefixEnd_216993 := by exact prefixLift 216993
  have htrace : WordTrace (prefixWord ++ tailWord_216993) baseStart_216993 baseEnd_216993 := by
    simpa [prefixWord, tailWord_216993, baseEnd_216993] using wordTrace_append hprefix tailTrace_216993
  have hstable : (prefixWord ++ tailWord_216993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216993).length < 2 ^ (prefixWord ++ tailWord_216993).sum := by decide
  have hdescent : baseEnd_216993 < baseStart_216993 := by decide
  rcases family_descends (prefixWord ++ tailWord_216993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217069 : List Nat := [1, 5, 1, 4, 1, 2, 1, 1, 4]
def baseStart_217069 : Nat := 118140960795 + 217069 * 2 ^ 59
def prefixEnd_217069 : Nat := 4983230072969 + 3 ^ 40 * 217069 * 2
def baseEnd_217069 : Nat := 99076206391925733545977

theorem tailTrace_217069 : CollatzResearch.WordTrace tailWord_217069 prefixEnd_217069 99076206391925733545977 := by
  unfold tailWord_217069
  simp only [CollatzResearch.WordTrace]
  refine ⟨7917156850603560278822261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5278104567069040185881507 7917156850603560278822261)
  ·
    refine ⟨742233454744083776139587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7917156850603560278822261 742233454744083776139587)
    ·
      refine ⟨1113350182116125664209381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 742233454744083776139587 1113350182116125664209381)
      ·
        refine ⟨208753159146773562039259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1113350182116125664209381 208753159146773562039259)
        ·
          refine ⟨313129738720160343058889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208753159146773562039259 313129738720160343058889)
          ·
            refine ⟨234847304040120257294167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313129738720160343058889 234847304040120257294167)
            ·
              refine ⟨352270956060180385941251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234847304040120257294167 352270956060180385941251)
              ·
                refine ⟨528406434090270578911877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352270956060180385941251 528406434090270578911877)
                ·
                  refine ⟨99076206391925733545977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 528406434090270578911877 99076206391925733545977)
                  ·
                    rfl

theorem cell20_217069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_217069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217069 prefixEnd_217069 := by exact prefixLift 217069
  have htrace : WordTrace (prefixWord ++ tailWord_217069) baseStart_217069 baseEnd_217069 := by
    simpa [prefixWord, tailWord_217069, baseEnd_217069] using wordTrace_append hprefix tailTrace_217069
  have hstable : (prefixWord ++ tailWord_217069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217069).length < 2 ^ (prefixWord ++ tailWord_217069).sum := by decide
  have hdescent : baseEnd_217069 < baseStart_217069 := by decide
  rcases family_descends (prefixWord ++ tailWord_217069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217115 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 8]
def baseStart_217115 : Nat := 118140960795 + 217115 * 2 ^ 59
def prefixEnd_217115 : Nat := 4983230072969 + 3 ^ 40 * 217115 * 2
def baseEnd_217115 : Nat := 99097202045354018012455

theorem tailTrace_217115 : CollatzResearch.WordTrace tailWord_217115 prefixEnd_217115 99097202045354018012455 := by
  unfold tailWord_217115
  simp only [CollatzResearch.WordTrace]
  refine ⟨7918834608436910134996799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5279223072291273423331199 7918834608436910134996799)
  ·
    refine ⟨11878251912655365202495199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7918834608436910134996799 11878251912655365202495199)
    ·
      refine ⟨17817377868983047803742799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11878251912655365202495199 17817377868983047803742799)
      ·
        refine ⟨26726066803474571705614199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17817377868983047803742799 26726066803474571705614199)
        ·
          refine ⟨40089100205211857558421299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26726066803474571705614199 40089100205211857558421299)
          ·
            refine ⟨60133650307817786337631949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40089100205211857558421299 60133650307817786337631949)
            ·
              refine ⟨22550118865431669876611981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60133650307817786337631949 22550118865431669876611981)
              ·
                refine ⟨8456294574536876203729493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22550118865431669876611981 8456294574536876203729493)
                ·
                  refine ⟨99097202045354018012455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8456294574536876203729493 99097202045354018012455)
                  ·
                    rfl

theorem cell20_217115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_217115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217115 prefixEnd_217115 := by exact prefixLift 217115
  have htrace : WordTrace (prefixWord ++ tailWord_217115) baseStart_217115 baseEnd_217115 := by
    simpa [prefixWord, tailWord_217115, baseEnd_217115] using wordTrace_append hprefix tailTrace_217115
  have hstable : (prefixWord ++ tailWord_217115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217115).length < 2 ^ (prefixWord ++ tailWord_217115).sum := by decide
  have hdescent : baseEnd_217115 < baseStart_217115 := by decide
  rcases family_descends (prefixWord ++ tailWord_217115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217124 : List Nat := [2, 3, 1, 4, 2, 2, 2, 2, 2]
def baseStart_217124 : Nat := 118140960795 + 217124 * 2 ^ 59
def prefixEnd_217124 : Nat := 4983230072969 + 3 ^ 40 * 217124 * 2
def baseEnd_217124 : Nat := 99101309890589986712419

theorem tailTrace_217124 : CollatzResearch.WordTrace tailWord_217124 prefixEnd_217124 99101309890589986712419 := by
  unfold tailWord_217124
  simp only [CollatzResearch.WordTrace]
  refine ⟨3959581432702152336037213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5279441910269536448049617 3959581432702152336037213)
  ·
    refine ⟨1484843037263307126013955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3959581432702152336037213 1484843037263307126013955)
    ·
      refine ⟨2227264555894960689020933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1484843037263307126013955 2227264555894960689020933)
      ·
        refine ⟨417612104230305129191425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2227264555894960689020933 417612104230305129191425)
        ·
          refine ⟨313209078172728846893569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417612104230305129191425 313209078172728846893569)
          ·
            refine ⟨234906808629546635170177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313209078172728846893569 234906808629546635170177)
            ·
              refine ⟨176180106472159976377633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234906808629546635170177 176180106472159976377633)
              ·
                refine ⟨132135079854119982283225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176180106472159976377633 132135079854119982283225)
                ·
                  refine ⟨99101309890589986712419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132135079854119982283225 99101309890589986712419)
                  ·
                    rfl

theorem cell20_217124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_217124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217124 prefixEnd_217124 := by exact prefixLift 217124
  have htrace : WordTrace (prefixWord ++ tailWord_217124) baseStart_217124 baseEnd_217124 := by
    simpa [prefixWord, tailWord_217124, baseEnd_217124] using wordTrace_append hprefix tailTrace_217124
  have hstable : (prefixWord ++ tailWord_217124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217124).length < 2 ^ (prefixWord ++ tailWord_217124).sum := by decide
  have hdescent : baseEnd_217124 < baseStart_217124 := by decide
  rcases family_descends (prefixWord ++ tailWord_217124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217125 : List Nat := [1, 3, 1, 2, 2, 3, 1, 4, 3]
def baseStart_217125 : Nat := 118140960795 + 217125 * 2 ^ 59
def prefixEnd_217125 : Nat := 4983230072969 + 3 ^ 40 * 217125 * 2
def baseEnd_217125 : Nat := 99101766317838427679081

theorem tailTrace_217125 : CollatzResearch.WordTrace tailWord_217125 prefixEnd_217125 99101766317838427679081 := by
  unfold tailWord_217125
  simp only [CollatzResearch.WordTrace]
  refine ⟨7919199338400681842860829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5279466225600454561907219 7919199338400681842860829)
  ·
    refine ⟨2969699751900255691072811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7919199338400681842860829 2969699751900255691072811)
    ·
      refine ⟨4454549627850383536609217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2969699751900255691072811 4454549627850383536609217)
      ·
        refine ⟨3340912220887787652456913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4454549627850383536609217 3340912220887787652456913)
        ·
          refine ⟨2505684165665840739342685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3340912220887787652456913 2505684165665840739342685)
          ·
            refine ⟨939631562124690277253507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2505684165665840739342685 939631562124690277253507)
            ·
              refine ⟨1409447343187035415880261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939631562124690277253507 1409447343187035415880261)
              ·
                refine ⟨264271376847569140477549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1409447343187035415880261 264271376847569140477549)
                ·
                  refine ⟨99101766317838427679081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264271376847569140477549 99101766317838427679081)
                  ·
                    rfl

theorem cell20_217125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_217125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217125 prefixEnd_217125 := by exact prefixLift 217125
  have htrace : WordTrace (prefixWord ++ tailWord_217125) baseStart_217125 baseEnd_217125 := by
    simpa [prefixWord, tailWord_217125, baseEnd_217125] using wordTrace_append hprefix tailTrace_217125
  have hstable : (prefixWord ++ tailWord_217125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217125).length < 2 ^ (prefixWord ++ tailWord_217125).sum := by decide
  have hdescent : baseEnd_217125 < baseStart_217125 := by decide
  rcases family_descends (prefixWord ++ tailWord_217125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217139 : List Nat := [1, 1, 1, 2, 4, 1, 5, 5]
def baseStart_217139 : Nat := 118140960795 + 217139 * 2 ^ 59
def prefixEnd_217139 : Nat := 4983230072969 + 3 ^ 40 * 217139 * 2
def baseEnd_217139 : Nat := 33036052099772200404119

theorem tailTrace_217139 : CollatzResearch.WordTrace tailWord_217139 prefixEnd_217139 33036052099772200404119 := by
  unfold tailWord_217139
  simp only [CollatzResearch.WordTrace]
  refine ⟨7919709960349962233870471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5279806640233308155913647 7919709960349962233870471)
  ·
    refine ⟨11879564940524943350805707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7919709960349962233870471 11879564940524943350805707)
    ·
      refine ⟨17819347410787415026208561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11879564940524943350805707 17819347410787415026208561)
      ·
        refine ⟨13364510558090561269656421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17819347410787415026208561 13364510558090561269656421)
        ·
          refine ⟨2505845729641980238060579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13364510558090561269656421 2505845729641980238060579)
          ·
            refine ⟨3758768594462970357090869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505845729641980238060579 3758768594462970357090869)
            ·
              refine ⟨352384555730903470977269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3758768594462970357090869 352384555730903470977269)
              ·
                refine ⟨33036052099772200404119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 352384555730903470977269 33036052099772200404119)
                ·
                  rfl

theorem cell20_217139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 5].length) (baseStart_217139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217139 prefixEnd_217139 := by exact prefixLift 217139
  have htrace : WordTrace (prefixWord ++ tailWord_217139) baseStart_217139 baseEnd_217139 := by
    simpa [prefixWord, tailWord_217139, baseEnd_217139] using wordTrace_append hprefix tailTrace_217139
  have hstable : (prefixWord ++ tailWord_217139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217139).length < 2 ^ (prefixWord ++ tailWord_217139).sum := by decide
  have hdescent : baseEnd_217139 < baseStart_217139 := by decide
  rcases family_descends (prefixWord ++ tailWord_217139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217142 : List Nat := [5, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_217142 : Nat := 118140960795 + 217142 * 2 ^ 59
def prefixEnd_217142 : Nat := 4983230072969 + 3 ^ 40 * 217142 * 2
def baseEnd_217142 : Nat := 99109525581061924112345

theorem tailTrace_217142 : CollatzResearch.WordTrace tailWord_217142 prefixEnd_217142 99109525581061924112345 := by
  unfold tailWord_217142
  simp only [CollatzResearch.WordTrace]
  refine ⟨494988711208693359139355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5279879586226062497486453 494988711208693359139355)
  ·
    refine ⟨742483066813040038709033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 494988711208693359139355 742483066813040038709033)
    ·
      refine ⟨556862300109780029031775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 742483066813040038709033 556862300109780029031775)
      ·
        refine ⟨835293450164670043547663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556862300109780029031775 835293450164670043547663)
        ·
          refine ⟨1252940175247005065321495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835293450164670043547663 1252940175247005065321495)
          ·
            refine ⟨1879410262870507597982243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252940175247005065321495 1879410262870507597982243)
            ·
              refine ⟨2819115394305761396973365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1879410262870507597982243 2819115394305761396973365)
              ·
                refine ⟨264292068216165130966253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2819115394305761396973365 264292068216165130966253)
                ·
                  refine ⟨99109525581061924112345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264292068216165130966253 99109525581061924112345)
                  ·
                    rfl

theorem cell20_217142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_217142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217142 prefixEnd_217142 := by exact prefixLift 217142
  have htrace : WordTrace (prefixWord ++ tailWord_217142) baseStart_217142 baseEnd_217142 := by
    simpa [prefixWord, tailWord_217142, baseEnd_217142] using wordTrace_append hprefix tailTrace_217142
  have hstable : (prefixWord ++ tailWord_217142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217142).length < 2 ^ (prefixWord ++ tailWord_217142).sum := by decide
  have hdescent : baseEnd_217142 < baseStart_217142 := by decide
  rcases family_descends (prefixWord ++ tailWord_217142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217146 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_217146 : Nat := 118140960795 + 217146 * 2 ^ 59
def prefixEnd_217146 : Nat := 4983230072969 + 3 ^ 40 * 217146 * 2
def baseEnd_217146 : Nat := 99111351290055687978995

theorem tailTrace_217146 : CollatzResearch.WordTrace tailWord_217146 prefixEnd_217146 99111351290055687978995 := by
  unfold tailWord_217146
  simp only [CollatzResearch.WordTrace]
  refine ⟨1979991317831150607343823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5279976847549734952916861 1979991317831150607343823)
  ·
    refine ⟨2969986976746725911015735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1979991317831150607343823 2969986976746725911015735)
    ·
      refine ⟨4454980465120088866523603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2969986976746725911015735 4454980465120088866523603)
      ·
        refine ⟨6682470697680133299785405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4454980465120088866523603 6682470697680133299785405)
        ·
          refine ⟨2505926511630049987419527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6682470697680133299785405 2505926511630049987419527)
          ·
            refine ⟨3758889767445074981129291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505926511630049987419527 3758889767445074981129291)
            ·
              refine ⟨5638334651167612471693937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3758889767445074981129291 5638334651167612471693937)
              ·
                refine ⟨4228750988375709353770453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5638334651167612471693937 4228750988375709353770453)
                ·
                  refine ⟨99111351290055687978995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4228750988375709353770453 99111351290055687978995)
                  ·
                    rfl

theorem cell20_217146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_217146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217146 prefixEnd_217146 := by exact prefixLift 217146
  have htrace : WordTrace (prefixWord ++ tailWord_217146) baseStart_217146 baseEnd_217146 := by
    simpa [prefixWord, tailWord_217146, baseEnd_217146] using wordTrace_append hprefix tailTrace_217146
  have hstable : (prefixWord ++ tailWord_217146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217146).length < 2 ^ (prefixWord ++ tailWord_217146).sum := by decide
  have hdescent : baseEnd_217146 < baseStart_217146 := by decide
  rcases family_descends (prefixWord ++ tailWord_217146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217166 : List Nat := [4, 1, 1, 1, 1, 5, 2, 3, 2]
def baseStart_217166 : Nat := 118140960795 + 217166 * 2 ^ 59
def prefixEnd_217166 : Nat := 4983230072969 + 3 ^ 40 * 217166 * 2
def baseEnd_217166 : Nat := 99120479835024507312247

theorem tailTrace_217166 : CollatzResearch.WordTrace tailWord_217166 prefixEnd_217166 99120479835024507312247 := by
  unfold tailWord_217166
  simp only [CollatzResearch.WordTrace]
  refine ⟨990086841406518230637919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5280463154168097230068901 990086841406518230637919)
  ·
    refine ⟨1485130262109777345956879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 990086841406518230637919 1485130262109777345956879)
    ·
      refine ⟨2227695393164666018935319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1485130262109777345956879 2227695393164666018935319)
      ·
        refine ⟨3341543089746999028402979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2227695393164666018935319 3341543089746999028402979)
        ·
          refine ⟨5012314634620498542604469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3341543089746999028402979 5012314634620498542604469)
          ·
            refine ⟨469904496995671738369169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5012314634620498542604469 469904496995671738369169)
            ·
              refine ⟨352428372746753803776877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469904496995671738369169 352428372746753803776877)
              ·
                refine ⟨132160639780032676416329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352428372746753803776877 132160639780032676416329)
                ·
                  refine ⟨99120479835024507312247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132160639780032676416329 99120479835024507312247)
                  ·
                    rfl

theorem cell20_217166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_217166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217166 prefixEnd_217166 := by exact prefixLift 217166
  have htrace : WordTrace (prefixWord ++ tailWord_217166) baseStart_217166 baseEnd_217166 := by
    simpa [prefixWord, tailWord_217166, baseEnd_217166] using wordTrace_append hprefix tailTrace_217166
  have hstable : (prefixWord ++ tailWord_217166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217166).length < 2 ^ (prefixWord ++ tailWord_217166).sum := by decide
  have hdescent : baseEnd_217166 < baseStart_217166 := by decide
  rcases family_descends (prefixWord ++ tailWord_217166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217180 : List Nat := [2, 2, 4, 1, 1, 2, 3, 2, 3]
def baseStart_217180 : Nat := 118140960795 + 217180 * 2 ^ 59
def prefixEnd_217180 : Nat := 4983230072969 + 3 ^ 40 * 217180 * 2
def baseEnd_217180 : Nat := 99126869816502680845523

theorem tailTrace_217180 : CollatzResearch.WordTrace tailWord_217180 prefixEnd_217180 99126869816502680845523 := by
  unfold tailWord_217180
  simp only [CollatzResearch.WordTrace]
  refine ⟨3960602676600713118056497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5280803568800950824075329 3960602676600713118056497)
  ·
    refine ⟨2970452007450534838542373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3960602676600713118056497 2970452007450534838542373)
    ·
      refine ⟨556959751396975282226695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2970452007450534838542373 556959751396975282226695)
      ·
        refine ⟨835439627095462923340043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556959751396975282226695 835439627095462923340043)
        ·
          refine ⟨1253159440643194385010065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835439627095462923340043 1253159440643194385010065)
          ·
            refine ⟨939869580482395788757549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1253159440643194385010065 939869580482395788757549)
            ·
              refine ⟨352451092680898420784081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 939869580482395788757549 352451092680898420784081)
              ·
                refine ⟨264338319510673815588061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352451092680898420784081 264338319510673815588061)
                ·
                  refine ⟨99126869816502680845523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264338319510673815588061 99126869816502680845523)
                  ·
                    rfl

theorem cell20_217180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_217180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217180 prefixEnd_217180 := by exact prefixLift 217180
  have htrace : WordTrace (prefixWord ++ tailWord_217180) baseStart_217180 baseEnd_217180 := by
    simpa [prefixWord, tailWord_217180, baseEnd_217180] using wordTrace_append hprefix tailTrace_217180
  have hstable : (prefixWord ++ tailWord_217180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217180).length < 2 ^ (prefixWord ++ tailWord_217180).sum := by decide
  have hdescent : baseEnd_217180 < baseStart_217180 := by decide
  rcases family_descends (prefixWord ++ tailWord_217180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217187 : List Nat := [1, 1, 1, 5, 1, 1, 4, 4, 2]
def baseStart_217187 : Nat := 118140960795 + 217187 * 2 ^ 59
def prefixEnd_217187 : Nat := 4983230072969 + 3 ^ 40 * 217187 * 2
def baseEnd_217187 : Nat := 99130064807241767612161

theorem tailTrace_217187 : CollatzResearch.WordTrace tailWord_217187 prefixEnd_217187 99130064807241767612161 := by
  unfold tailWord_217187
  simp only [CollatzResearch.WordTrace]
  refine ⟨7921460664176066431617815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5280973776117377621078543 7921460664176066431617815)
  ·
    refine ⟨11882190996264099647426723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7921460664176066431617815 11882190996264099647426723)
    ·
      refine ⟨17823286494396149471140085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11882190996264099647426723 17823286494396149471140085)
      ·
        refine ⟨1670933108849639012919383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17823286494396149471140085 1670933108849639012919383)
        ·
          refine ⟨2506399663274458519379075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1670933108849639012919383 2506399663274458519379075)
          ·
            refine ⟨3759599494911687779068613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2506399663274458519379075 3759599494911687779068613)
            ·
              refine ⟨704924905295941458575365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3759599494911687779068613 704924905295941458575365)
              ·
                refine ⟨132173419742989023482881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 704924905295941458575365 132173419742989023482881)
                ·
                  refine ⟨99130064807241767612161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132173419742989023482881 99130064807241767612161)
                  ·
                    rfl

theorem cell20_217187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 4, 2].length) (baseStart_217187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217187 prefixEnd_217187 := by exact prefixLift 217187
  have htrace : WordTrace (prefixWord ++ tailWord_217187) baseStart_217187 baseEnd_217187 := by
    simpa [prefixWord, tailWord_217187, baseEnd_217187] using wordTrace_append hprefix tailTrace_217187
  have hstable : (prefixWord ++ tailWord_217187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217187).length < 2 ^ (prefixWord ++ tailWord_217187).sum := by decide
  have hdescent : baseEnd_217187 < baseStart_217187 := by decide
  rcases family_descends (prefixWord ++ tailWord_217187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217242 : List Nat := [3, 1, 1, 5, 2, 2, 1, 1, 4]
def baseStart_217242 : Nat := 118140960795 + 217242 * 2 ^ 59
def prefixEnd_217242 : Nat := 4983230072969 + 3 ^ 40 * 217242 * 2
def baseEnd_217242 : Nat := 99155168305906020778603

theorem tailTrace_217242 : CollatzResearch.WordTrace tailWord_217242 prefixEnd_217242 99155168305906020778603 := by
  unfold tailWord_217242
  simp only [CollatzResearch.WordTrace]
  refine ⟨1980866669744202706217495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5282311119317873883246653 1980866669744202706217495)
  ·
    refine ⟨2971300004616304059326243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1980866669744202706217495 2971300004616304059326243)
    ·
      refine ⟨4456950006924456088989365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2971300004616304059326243 4456950006924456088989365)
      ·
        refine ⟨417839063149167758342753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4456950006924456088989365 417839063149167758342753)
        ·
          refine ⟨313379297361875818757065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417839063149167758342753 313379297361875818757065)
          ·
            refine ⟨235034473021406864067799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313379297361875818757065 235034473021406864067799)
            ·
              refine ⟨352551709532110296101699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235034473021406864067799 352551709532110296101699)
              ·
                refine ⟨528827564298165444152549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352551709532110296101699 528827564298165444152549)
                ·
                  refine ⟨99155168305906020778603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 528827564298165444152549 99155168305906020778603)
                  ·
                    rfl

theorem cell20_217242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_217242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217242 prefixEnd_217242 := by exact prefixLift 217242
  have htrace : WordTrace (prefixWord ++ tailWord_217242) baseStart_217242 baseEnd_217242 := by
    simpa [prefixWord, tailWord_217242, baseEnd_217242] using wordTrace_append hprefix tailTrace_217242
  have hstable : (prefixWord ++ tailWord_217242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217242).length < 2 ^ (prefixWord ++ tailWord_217242).sum := by decide
  have hdescent : baseEnd_217242 < baseStart_217242 := by decide
  rcases family_descends (prefixWord ++ tailWord_217242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217252 : List Nat := [2, 3, 1, 2, 5, 1, 2, 1, 3]
def baseStart_217252 : Nat := 118140960795 + 217252 * 2 ^ 59
def prefixEnd_217252 : Nat := 4983230072969 + 3 ^ 40 * 217252 * 2
def baseEnd_217252 : Nat := 99159732578390430445229

theorem tailTrace_217252 : CollatzResearch.WordTrace tailWord_217252 prefixEnd_217252 99159732578390430445229 := by
  unfold tailWord_217252
  simp only [CollatzResearch.WordTrace]
  refine ⟨3961915704470291266367005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5282554272627055021822673 3961915704470291266367005)
  ·
    refine ⟨1485718389176359224887627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3961915704470291266367005 1485718389176359224887627)
    ·
      refine ⟨2228577583764538837331441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1485718389176359224887627 2228577583764538837331441)
      ·
        refine ⟨1671433187823404127998581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2228577583764538837331441 1671433187823404127998581)
        ·
          refine ⟨156696861358444136999867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1671433187823404127998581 156696861358444136999867)
          ·
            refine ⟨235045292037666205499801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156696861358444136999867 235045292037666205499801)
            ·
              refine ⟨176283969028249654124851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235045292037666205499801 176283969028249654124851)
              ·
                refine ⟨264425953542374481187277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176283969028249654124851 264425953542374481187277)
                ·
                  refine ⟨99159732578390430445229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264425953542374481187277 99159732578390430445229)
                  ·
                    rfl

theorem cell20_217252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_217252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217252 prefixEnd_217252 := by exact prefixLift 217252
  have htrace : WordTrace (prefixWord ++ tailWord_217252) baseStart_217252 baseEnd_217252 := by
    simpa [prefixWord, tailWord_217252, baseEnd_217252] using wordTrace_append hprefix tailTrace_217252
  have hstable : (prefixWord ++ tailWord_217252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217252).length < 2 ^ (prefixWord ++ tailWord_217252).sum := by decide
  have hdescent : baseEnd_217252 < baseStart_217252 := by decide
  rcases family_descends (prefixWord ++ tailWord_217252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217253 : List Nat := [1, 3, 1, 2, 1, 3, 4, 5]
def baseStart_217253 : Nat := 118140960795 + 217253 * 2 ^ 59
def prefixEnd_217253 : Nat := 4983230072969 + 3 ^ 40 * 217253 * 2
def baseEnd_217253 : Nat := 33053396335212957137297

theorem tailTrace_217253 : CollatzResearch.WordTrace tailWord_217253 prefixEnd_217253 33053396335212957137297 := by
  unfold tailWord_217253
  simp only [CollatzResearch.WordTrace]
  refine ⟨7923867881936959703520413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5282578587957973135680275 7923867881936959703520413)
  ·
    refine ⟨2971450455726359888820155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7923867881936959703520413 2971450455726359888820155)
    ·
      refine ⟨4457175683589539833230233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2971450455726359888820155 4457175683589539833230233)
      ·
        refine ⟨3342881762692154874922675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4457175683589539833230233 3342881762692154874922675)
        ·
          refine ⟨5014322644038232312384013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3342881762692154874922675 5014322644038232312384013)
          ·
            refine ⟨1880370991514337117144005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5014322644038232312384013 1880370991514337117144005)
            ·
              refine ⟨352569560908938209464501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1880370991514337117144005 352569560908938209464501)
              ·
                refine ⟨33053396335212957137297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 352569560908938209464501 33053396335212957137297)
                ·
                  rfl

theorem cell20_217253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 5].length) (baseStart_217253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217253 prefixEnd_217253 := by exact prefixLift 217253
  have htrace : WordTrace (prefixWord ++ tailWord_217253) baseStart_217253 baseEnd_217253 := by
    simpa [prefixWord, tailWord_217253, baseEnd_217253] using wordTrace_append hprefix tailTrace_217253
  have hstable : (prefixWord ++ tailWord_217253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217253).length < 2 ^ (prefixWord ++ tailWord_217253).sum := by decide
  have hdescent : baseEnd_217253 < baseStart_217253 := by decide
  rcases family_descends (prefixWord ++ tailWord_217253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217267 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 6]
def baseStart_217267 : Nat := 118140960795 + 217267 * 2 ^ 59
def prefixEnd_217267 : Nat := 4983230072969 + 3 ^ 40 * 217267 * 2
def baseEnd_217267 : Nat := 99166578987117044945167

theorem tailTrace_217267 : CollatzResearch.WordTrace tailWord_217267 prefixEnd_217267 99166578987117044945167 := by
  unfold tailWord_217267
  simp only [CollatzResearch.WordTrace]
  refine ⟨7924378503886240094530055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5282919002590826729686703 7924378503886240094530055)
  ·
    refine ⟨11886567755829360141795083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7924378503886240094530055 11886567755829360141795083)
    ·
      refine ⟨17829851633744040212692625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11886567755829360141795083 17829851633744040212692625)
      ·
        refine ⟨13372388725308030159519469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17829851633744040212692625 13372388725308030159519469)
        ·
          refine ⟨5014645771990511309819801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13372388725308030159519469 5014645771990511309819801)
          ·
            refine ⟨3760984328992883482364851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5014645771990511309819801 3760984328992883482364851)
            ·
              refine ⟨5641476493489325223547277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3760984328992883482364851 5641476493489325223547277)
              ·
                refine ⟨2115553685058496958830229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5641476493489325223547277 2115553685058496958830229)
                ·
                  refine ⟨99166578987117044945167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2115553685058496958830229 99166578987117044945167)
                  ·
                    rfl

theorem cell20_217267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_217267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217267 prefixEnd_217267 := by exact prefixLift 217267
  have htrace : WordTrace (prefixWord ++ tailWord_217267) baseStart_217267 baseEnd_217267 := by
    simpa [prefixWord, tailWord_217267, baseEnd_217267] using wordTrace_append hprefix tailTrace_217267
  have hstable : (prefixWord ++ tailWord_217267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217267).length < 2 ^ (prefixWord ++ tailWord_217267).sum := by decide
  have hdescent : baseEnd_217267 < baseStart_217267 := by decide
  rcases family_descends (prefixWord ++ tailWord_217267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217294 : List Nat := [4, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_217294 : Nat := 118140960795 + 217294 * 2 ^ 59
def prefixEnd_217294 : Nat := 4983230072969 + 3 ^ 40 * 217294 * 2
def baseEnd_217294 : Nat := 99178902522824951045057

theorem tailTrace_217294 : CollatzResearch.WordTrace tailWord_217294 prefixEnd_217294 99178902522824951045057 := by
  unfold tailWord_217294
  simp only [CollatzResearch.WordTrace]
  refine ⟨990670409348552963220367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5283575516525615803841957 990670409348552963220367)
  ·
    refine ⟨1486005614022829444830551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 990670409348552963220367 1486005614022829444830551)
    ·
      refine ⟨2229008421034244167245827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1486005614022829444830551 2229008421034244167245827)
      ·
        refine ⟨3343512631551366250868741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2229008421034244167245827 3343512631551366250868741)
        ·
          refine ⟨626908618415881172037889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3343512631551366250868741 626908618415881172037889)
          ·
            refine ⟨470181463811910879028417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 626908618415881172037889 470181463811910879028417)
            ·
              refine ⟨352636097858933159271313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470181463811910879028417 352636097858933159271313)
              ·
                refine ⟨264477073394199869453485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352636097858933159271313 264477073394199869453485)
                ·
                  refine ⟨99178902522824951045057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264477073394199869453485 99178902522824951045057)
                  ·
                    rfl

theorem cell20_217294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_217294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217294 prefixEnd_217294 := by exact prefixLift 217294
  have htrace : WordTrace (prefixWord ++ tailWord_217294) baseStart_217294 baseEnd_217294 := by
    simpa [prefixWord, tailWord_217294, baseEnd_217294] using wordTrace_append hprefix tailTrace_217294
  have hstable : (prefixWord ++ tailWord_217294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217294).length < 2 ^ (prefixWord ++ tailWord_217294).sum := by decide
  have hdescent : baseEnd_217294 < baseStart_217294 := by decide
  rcases family_descends (prefixWord ++ tailWord_217294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217322 : List Nat := [3, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_217322 : Nat := 118140960795 + 217322 * 2 ^ 59
def prefixEnd_217322 : Nat := 4983230072969 + 3 ^ 40 * 217322 * 2
def baseEnd_217322 : Nat := 99191682485781298111609

theorem tailTrace_217322 : CollatzResearch.WordTrace tailWord_217322 prefixEnd_217322 99191682485781298111609 := by
  unfold tailWord_217322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1981596129671746121945555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5284256345791322991854813 1981596129671746121945555)
  ·
    refine ⟨2972394194507619182918333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1981596129671746121945555 2972394194507619182918333)
    ·
      refine ⟨1114647822940357193594375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2972394194507619182918333 1114647822940357193594375)
      ·
        refine ⟨1671971734410535790391563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1114647822940357193594375 1671971734410535790391563)
        ·
          refine ⟨2507957601615803685587345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671971734410535790391563 2507957601615803685587345)
          ·
            refine ⟨1880968201211852764190509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2507957601615803685587345 1880968201211852764190509)
            ·
              refine ⟨705363075454444786571441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1880968201211852764190509 705363075454444786571441)
              ·
                refine ⟨529022306590833589928581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705363075454444786571441 529022306590833589928581)
                ·
                  refine ⟨99191682485781298111609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 529022306590833589928581 99191682485781298111609)
                  ·
                    rfl

theorem cell20_217322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_217322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217322 prefixEnd_217322 := by exact prefixLift 217322
  have htrace : WordTrace (prefixWord ++ tailWord_217322) baseStart_217322 baseEnd_217322 := by
    simpa [prefixWord, tailWord_217322, baseEnd_217322] using wordTrace_append hprefix tailTrace_217322
  have hstable : (prefixWord ++ tailWord_217322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217322).length < 2 ^ (prefixWord ++ tailWord_217322).sum := by decide
  have hdescent : baseEnd_217322 < baseStart_217322 := by decide
  rcases family_descends (prefixWord ++ tailWord_217322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217325 : List Nat := [1, 5, 1, 2, 3, 1, 3, 4]
def baseStart_217325 : Nat := 118140960795 + 217325 * 2 ^ 59
def prefixEnd_217325 : Nat := 4983230072969 + 3 ^ 40 * 217325 * 2
def baseEnd_217325 : Nat := 33064350589175540337199

theorem tailTrace_217325 : CollatzResearch.WordTrace tailWord_217325 prefixEnd_217325 33064350589175540337199 := by
  unfold tailWord_217325
  simp only [CollatzResearch.WordTrace]
  refine ⟨7926493937676116000141429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5284329291784077333427619 7926493937676116000141429)
  ·
    refine ⟨743108806657135875013259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7926493937676116000141429 743108806657135875013259)
    ·
      refine ⟨1114663209985703812519889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 743108806657135875013259 1114663209985703812519889)
      ·
        refine ⟨835997407489277859389917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1114663209985703812519889 835997407489277859389917)
        ·
          refine ⟨313499027808479197271219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 835997407489277859389917 313499027808479197271219)
          ·
            refine ⟨470248541712718795906829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313499027808479197271219 470248541712718795906829)
            ·
              refine ⟨176343203142269548465061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 470248541712718795906829 176343203142269548465061)
              ·
                refine ⟨33064350589175540337199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176343203142269548465061 33064350589175540337199)
                ·
                  rfl

theorem cell20_217325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 4].length) (baseStart_217325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217325 prefixEnd_217325 := by exact prefixLift 217325
  have htrace : WordTrace (prefixWord ++ tailWord_217325) baseStart_217325 baseEnd_217325 := by
    simpa [prefixWord, tailWord_217325, baseEnd_217325] using wordTrace_append hprefix tailTrace_217325
  have hstable : (prefixWord ++ tailWord_217325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217325).length < 2 ^ (prefixWord ++ tailWord_217325).sum := by decide
  have hdescent : baseEnd_217325 < baseStart_217325 := by decide
  rcases family_descends (prefixWord ++ tailWord_217325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217343 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 6]
def baseStart_217343 : Nat := 118140960795 + 217343 * 2 ^ 59
def prefixEnd_217343 : Nat := 4983230072969 + 3 ^ 40 * 217343 * 2
def baseEnd_217343 : Nat := 99201267457998558411523

theorem tailTrace_217343 : CollatzResearch.WordTrace tailWord_217343 prefixEnd_217343 99201267457998558411523 := by
  unfold tailWord_217343
  simp only [CollatzResearch.WordTrace]
  refine ⟨7927150451610905074296683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5284766967740603382864455 7927150451610905074296683)
  ·
    refine ⟨11890725677416357611445025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7927150451610905074296683 11890725677416357611445025)
    ·
      refine ⟨8918044258062268208583769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11890725677416357611445025 8918044258062268208583769)
      ·
        refine ⟨6688533193546701156437827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8918044258062268208583769 6688533193546701156437827)
        ·
          refine ⟨10032799790320051734656741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6688533193546701156437827 10032799790320051734656741)
          ·
            refine ⟨1881149960685009700248139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10032799790320051734656741 1881149960685009700248139)
            ·
              refine ⟨2821724941027514550372209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881149960685009700248139 2821724941027514550372209)
              ·
                refine ⟨2116293705770635912779157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2821724941027514550372209 2116293705770635912779157)
                ·
                  refine ⟨99201267457998558411523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2116293705770635912779157 99201267457998558411523)
                  ·
                    rfl

theorem cell20_217343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_217343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217343 prefixEnd_217343 := by exact prefixLift 217343
  have htrace : WordTrace (prefixWord ++ tailWord_217343) baseStart_217343 baseEnd_217343 := by
    simpa [prefixWord, tailWord_217343, baseEnd_217343] using wordTrace_append hprefix tailTrace_217343
  have hstable : (prefixWord ++ tailWord_217343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217343).length < 2 ^ (prefixWord ++ tailWord_217343).sum := by decide
  have hdescent : baseEnd_217343 < baseStart_217343 := by decide
  rcases family_descends (prefixWord ++ tailWord_217343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217346 : List Nat := [3, 4, 1, 1, 2, 2, 7]
def baseStart_217346 : Nat := 118140960795 + 217346 * 2 ^ 59
def prefixEnd_217346 : Nat := 4983230072969 + 3 ^ 40 * 217346 * 2
def baseEnd_217346 : Nat := 11022515193304875701279

theorem tailTrace_217346 : CollatzResearch.WordTrace tailWord_217346 prefixEnd_217346 11022515193304875701279 := by
  unfold tailWord_217346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1981814967650009146663973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5284839913733357724437261 1981814967650009146663973)
  ·
    refine ⟨371590306434376714999495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1981814967650009146663973 371590306434376714999495)
    ·
      refine ⟨557385459651565072499243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371590306434376714999495 557385459651565072499243)
      ·
        refine ⟨836078189477347608748865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557385459651565072499243 836078189477347608748865)
        ·
          refine ⟨627058642108010706561649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 836078189477347608748865 627058642108010706561649)
          ·
            refine ⟨470293981581008029921237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 627058642108010706561649 470293981581008029921237)
            ·
              refine ⟨11022515193304875701279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 470293981581008029921237 11022515193304875701279)
              ·
                rfl

theorem cell20_217346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 7].length) (baseStart_217346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217346 prefixEnd_217346 := by exact prefixLift 217346
  have htrace : WordTrace (prefixWord ++ tailWord_217346) baseStart_217346 baseEnd_217346 := by
    simpa [prefixWord, tailWord_217346, baseEnd_217346] using wordTrace_append hprefix tailTrace_217346
  have hstable : (prefixWord ++ tailWord_217346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217346).length < 2 ^ (prefixWord ++ tailWord_217346).sum := by decide
  have hdescent : baseEnd_217346 < baseStart_217346 := by decide
  rcases family_descends (prefixWord ++ tailWord_217346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217353 : List Nat := [1, 2, 1, 1, 3, 4, 3, 2, 3]
def baseStart_217353 : Nat := 118140960795 + 217353 * 2 ^ 59
def prefixEnd_217353 : Nat := 4983230072969 + 3 ^ 40 * 217353 * 2
def baseEnd_217353 : Nat := 99205831730482968078149

theorem tailTrace_217353 : CollatzResearch.WordTrace tailWord_217353 prefixEnd_217353 99205831730482968078149 := by
  unfold tailWord_217353
  simp only [CollatzResearch.WordTrace]
  refine ⟨7927515181574676782160713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5285010121049784521440475 7927515181574676782160713)
  ·
    refine ⟨5945636386181007586620535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7927515181574676782160713 5945636386181007586620535)
    ·
      refine ⟨8918454579271511379930803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5945636386181007586620535 8918454579271511379930803)
      ·
        refine ⟨13377681868907267069896205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8918454579271511379930803 13377681868907267069896205)
        ·
          refine ⟨5016630700840225151211077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13377681868907267069896205 5016630700840225151211077)
          ·
            refine ⟨940618256407542215852077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5016630700840225151211077 940618256407542215852077)
            ·
              refine ⟨352731846152828330944529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 940618256407542215852077 352731846152828330944529)
              ·
                refine ⟨264548884614621248208397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352731846152828330944529 264548884614621248208397)
                ·
                  refine ⟨99205831730482968078149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264548884614621248208397 99205831730482968078149)
                  ·
                    rfl

theorem cell20_217353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_217353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217353 prefixEnd_217353 := by exact prefixLift 217353
  have htrace : WordTrace (prefixWord ++ tailWord_217353) baseStart_217353 baseEnd_217353 := by
    simpa [prefixWord, tailWord_217353, baseEnd_217353] using wordTrace_append hprefix tailTrace_217353
  have hstable : (prefixWord ++ tailWord_217353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217353).length < 2 ^ (prefixWord ++ tailWord_217353).sum := by decide
  have hdescent : baseEnd_217353 < baseStart_217353 := by decide
  rcases family_descends (prefixWord ++ tailWord_217353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217384 : List Nat := [2, 1, 5, 1, 3, 1, 1, 6]
def baseStart_217384 : Nat := 118140960795 + 217384 * 2 ^ 59
def prefixEnd_217384 : Nat := 4983230072969 + 3 ^ 40 * 217384 * 2
def baseEnd_217384 : Nat := 33073326991728212681563

theorem tailTrace_217384 : CollatzResearch.WordTrace tailWord_217384 prefixEnd_217384 33073326991728212681563 := by
  unfold tailWord_217384
  simp only [CollatzResearch.WordTrace]
  refine ⟨3964322922231184538269603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5285763896308246051026137 3964322922231184538269603)
  ·
    refine ⟨5946484383346776807404405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3964322922231184538269603 5946484383346776807404405)
    ·
      refine ⟨557482910938760325694163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5946484383346776807404405 557482910938760325694163)
      ·
        refine ⟨836224366408140488541245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557482910938760325694163 836224366408140488541245)
        ·
          refine ⟨313584137403052683202967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 836224366408140488541245 313584137403052683202967)
          ·
            refine ⟨470376206104579024804451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313584137403052683202967 470376206104579024804451)
            ·
              refine ⟨705564309156868537206677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470376206104579024804451 705564309156868537206677)
              ·
                refine ⟨33073326991728212681563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 705564309156868537206677 33073326991728212681563)
                ·
                  rfl

theorem cell20_217384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_217384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217384 prefixEnd_217384 := by exact prefixLift 217384
  have htrace : WordTrace (prefixWord ++ tailWord_217384) baseStart_217384 baseEnd_217384 := by
    simpa [prefixWord, tailWord_217384, baseEnd_217384] using wordTrace_append hprefix tailTrace_217384
  have hstable : (prefixWord ++ tailWord_217384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217384).length < 2 ^ (prefixWord ++ tailWord_217384).sum := by decide
  have hdescent : baseEnd_217384 < baseStart_217384 := by decide
  rcases family_descends (prefixWord ++ tailWord_217384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217390 : List Nat := [4, 1, 3, 3, 1, 2, 1, 3, 2]
def baseStart_217390 : Nat := 118140960795 + 217390 * 2 ^ 59
def prefixEnd_217390 : Nat := 4983230072969 + 3 ^ 40 * 217390 * 2
def baseEnd_217390 : Nat := 99222719538675283844665

theorem tailTrace_217390 : CollatzResearch.WordTrace tailWord_217390 prefixEnd_217390 99222719538675283844665 := by
  unfold tailWord_217390
  simp only [CollatzResearch.WordTrace]
  refine ⟨991108085305079012657203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5285909788293754734171749 991108085305079012657203)
  ·
    refine ⟨1486662127957618518985805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 991108085305079012657203 1486662127957618518985805)
    ·
      refine ⟨557498297984106944619677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1486662127957618518985805 557498297984106944619677)
      ·
        refine ⟨209061861744040104232379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 557498297984106944619677 209061861744040104232379)
        ·
          refine ⟨313592792616060156348569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209061861744040104232379 313592792616060156348569)
          ·
            refine ⟨235194594462045117261427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313592792616060156348569 235194594462045117261427)
            ·
              refine ⟨352791891693067675892141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235194594462045117261427 352791891693067675892141)
              ·
                refine ⟨132296959384900378459553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352791891693067675892141 132296959384900378459553)
                ·
                  refine ⟨99222719538675283844665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132296959384900378459553 99222719538675283844665)
                  ·
                    rfl

theorem cell20_217390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_217390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217390 prefixEnd_217390 := by exact prefixLift 217390
  have htrace : WordTrace (prefixWord ++ tailWord_217390) baseStart_217390 baseEnd_217390 := by
    simpa [prefixWord, tailWord_217390, baseEnd_217390] using wordTrace_append hprefix tailTrace_217390
  have hstable : (prefixWord ++ tailWord_217390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217390).length < 2 ^ (prefixWord ++ tailWord_217390).sum := by decide
  have hdescent : baseEnd_217390 < baseStart_217390 := by decide
  rcases family_descends (prefixWord ++ tailWord_217390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217419 : List Nat := [1, 1, 1, 1, 3, 1, 1, 7, 4]
def baseStart_217419 : Nat := 118140960795 + 217419 * 2 ^ 59
def prefixEnd_217419 : Nat := 4983230072969 + 3 ^ 40 * 217419 * 2
def baseEnd_217419 : Nat := 99235955928880071877879

theorem tailTrace_217419 : CollatzResearch.WordTrace tailWord_217419 prefixEnd_217419 99235955928880071877879 := by
  unfold tailWord_217419
  simp only [CollatzResearch.WordTrace]
  refine ⟨7929922399335570054063311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5286614932890380036042207 7929922399335570054063311)
  ·
    refine ⟨11894883599003355081094967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7929922399335570054063311 11894883599003355081094967)
    ·
      refine ⟨17842325398505032621642451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11894883599003355081094967 17842325398505032621642451)
      ·
        refine ⟨26763488097757548932463677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17842325398505032621642451 26763488097757548932463677)
        ·
          refine ⟨10036308036659080849673879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26763488097757548932463677 10036308036659080849673879)
          ·
            refine ⟨15054462054988621274510819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10036308036659080849673879 15054462054988621274510819)
            ·
              refine ⟨22581693082482931911766229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15054462054988621274510819 22581693082482931911766229)
              ·
                refine ⟨529258431620693716682021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22581693082482931911766229 529258431620693716682021)
                ·
                  refine ⟨99235955928880071877879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 529258431620693716682021 99235955928880071877879)
                  ·
                    rfl

theorem cell20_217419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_217419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217419 prefixEnd_217419 := by exact prefixLift 217419
  have htrace : WordTrace (prefixWord ++ tailWord_217419) baseStart_217419 baseEnd_217419 := by
    simpa [prefixWord, tailWord_217419, baseEnd_217419] using wordTrace_append hprefix tailTrace_217419
  have hstable : (prefixWord ++ tailWord_217419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217419).length < 2 ^ (prefixWord ++ tailWord_217419).sum := by decide
  have hdescent : baseEnd_217419 < baseStart_217419 := by decide
  rcases family_descends (prefixWord ++ tailWord_217419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217453 : List Nat := [1, 5, 1, 1, 1, 2, 2, 5, 2]
def baseStart_217453 : Nat := 118140960795 + 217453 * 2 ^ 59
def prefixEnd_217453 : Nat := 4983230072969 + 3 ^ 40 * 217453 * 2
def baseEnd_217453 : Nat := 99251474455327064744407

theorem tailTrace_217453 : CollatzResearch.WordTrace tailWord_217453 prefixEnd_217453 99251474455327064744407 := by
  unfold tailWord_217453
  simp only [CollatzResearch.WordTrace]
  refine ⟨7931162481212393860801013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5287441654141595907200675 7931162481212393860801013)
  ·
    refine ⟨743546482613661924450095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7931162481212393860801013 743546482613661924450095)
    ·
      refine ⟨1115319723920492886675143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 743546482613661924450095 1115319723920492886675143)
      ·
        refine ⟨1672979585880739330012715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1115319723920492886675143 1672979585880739330012715)
        ·
          refine ⟨2509469378821108995019073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1672979585880739330012715 2509469378821108995019073)
          ·
            refine ⟨1882102034115831746264305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2509469378821108995019073 1882102034115831746264305)
            ·
              refine ⟨1411576525586873809698229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1882102034115831746264305 1411576525586873809698229)
              ·
                refine ⟨132335299273769419659209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1411576525586873809698229 132335299273769419659209)
                ·
                  refine ⟨99251474455327064744407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132335299273769419659209 99251474455327064744407)
                  ·
                    rfl

theorem cell20_217453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_217453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217453 prefixEnd_217453 := by exact prefixLift 217453
  have htrace : WordTrace (prefixWord ++ tailWord_217453) baseStart_217453 baseEnd_217453 := by
    simpa [prefixWord, tailWord_217453, baseEnd_217453] using wordTrace_append hprefix tailTrace_217453
  have hstable : (prefixWord ++ tailWord_217453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217453).length < 2 ^ (prefixWord ++ tailWord_217453).sum := by decide
  have hdescent : baseEnd_217453 < baseStart_217453 := by decide
  rcases family_descends (prefixWord ++ tailWord_217453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217467 : List Nat := [1, 1, 1, 1, 1, 8, 2, 2, 3]
def baseStart_217467 : Nat := 118140960795 + 217467 * 2 ^ 59
def prefixEnd_217467 : Nat := 4983230072969 + 3 ^ 40 * 217467 * 2
def baseEnd_217467 : Nat := 99257864436805238277683

theorem tailTrace_217467 : CollatzResearch.WordTrace tailWord_217467 prefixEnd_217467 99257864436805238277683 := by
  unfold tailWord_217467
  simp only [CollatzResearch.WordTrace]
  refine ⟨7931673103161674251810655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5287782068774449501207103 7931673103161674251810655)
  ·
    refine ⟨11897509654742511377715983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7931673103161674251810655 11897509654742511377715983)
    ·
      refine ⟨17846264482113767066573975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11897509654742511377715983 17846264482113767066573975)
      ·
        refine ⟨26769396723170650599860963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17846264482113767066573975 26769396723170650599860963)
        ·
          refine ⟨40154095084755975899791445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26769396723170650599860963 40154095084755975899791445)
          ·
            refine ⟨470555801774484092575681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 40154095084755975899791445 470555801774484092575681)
            ·
              refine ⟨352916851330863069431761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470555801774484092575681 352916851330863069431761)
              ·
                refine ⟨264687638498147302073821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352916851330863069431761 264687638498147302073821)
                ·
                  refine ⟨99257864436805238277683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264687638498147302073821 99257864436805238277683)
                  ·
                    rfl

theorem cell20_217467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 3].length) (baseStart_217467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217467 prefixEnd_217467 := by exact prefixLift 217467
  have htrace : WordTrace (prefixWord ++ tailWord_217467) baseStart_217467 baseEnd_217467 := by
    simpa [prefixWord, tailWord_217467, baseEnd_217467] using wordTrace_append hprefix tailTrace_217467
  have hstable : (prefixWord ++ tailWord_217467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217467).length < 2 ^ (prefixWord ++ tailWord_217467).sum := by decide
  have hdescent : baseEnd_217467 < baseStart_217467 := by decide
  rcases family_descends (prefixWord ++ tailWord_217467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217481 : List Nat := [1, 2, 1, 1, 6, 1, 3, 5]
def baseStart_217481 : Nat := 118140960795 + 217481 * 2 ^ 59
def prefixEnd_217481 : Nat := 4983230072969 + 3 ^ 40 * 217481 * 2
def baseEnd_217481 : Nat := 33088084806094470603653

theorem tailTrace_217481 : CollatzResearch.WordTrace tailWord_217481 prefixEnd_217481 33088084806094470603653 := by
  unfold tailWord_217481
  simp only [CollatzResearch.WordTrace]
  refine ⟨7932183725110954642820297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5288122483407303095213531 7932183725110954642820297)
  ·
    refine ⟨5949137793833215982115223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7932183725110954642820297 5949137793833215982115223)
    ·
      refine ⟨8923706690749823973172835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5949137793833215982115223 8923706690749823973172835)
      ·
        refine ⟨13385560036124735959759253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8923706690749823973172835 13385560036124735959759253)
        ·
          refine ⟨627448126693346998113715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13385560036124735959759253 627448126693346998113715)
          ·
            refine ⟨941172190040020497170573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627448126693346998113715 941172190040020497170573)
            ·
              refine ⟨352939571265007686438965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 941172190040020497170573 352939571265007686438965)
              ·
                refine ⟨33088084806094470603653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 352939571265007686438965 33088084806094470603653)
                ·
                  rfl

theorem cell20_217481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 5].length) (baseStart_217481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217481 prefixEnd_217481 := by exact prefixLift 217481
  have htrace : WordTrace (prefixWord ++ tailWord_217481) baseStart_217481 baseEnd_217481 := by
    simpa [prefixWord, tailWord_217481, baseEnd_217481] using wordTrace_append hprefix tailTrace_217481
  have hstable : (prefixWord ++ tailWord_217481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217481).length < 2 ^ (prefixWord ++ tailWord_217481).sum := by decide
  have hdescent : baseEnd_217481 < baseStart_217481 := by decide
  rcases family_descends (prefixWord ++ tailWord_217481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217495 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 6]
def baseStart_217495 : Nat := 118140960795 + 217495 * 2 ^ 59
def prefixEnd_217495 : Nat := 4983230072969 + 3 ^ 40 * 217495 * 2
def baseEnd_217495 : Nat := 99270644399761585344235

theorem tailTrace_217495 : CollatzResearch.WordTrace tailWord_217495 prefixEnd_217495 99270644399761585344235 := by
  unfold tailWord_217495
  simp only [CollatzResearch.WordTrace]
  refine ⟨7932694347060235033829939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5288462898040156689219959 7932694347060235033829939)
  ·
    refine ⟨11899041520590352550744909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7932694347060235033829939 11899041520590352550744909)
    ·
      refine ⟨4462140570221382206529341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11899041520590352550744909 4462140570221382206529341)
      ·
        refine ⟨1673302713833018327448503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4462140570221382206529341 1673302713833018327448503)
        ·
          refine ⟨2509954070749527491172755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1673302713833018327448503 2509954070749527491172755)
          ·
            refine ⟨3764931106124291236759133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2509954070749527491172755 3764931106124291236759133)
            ·
              refine ⟨1411849164796609213784675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3764931106124291236759133 1411849164796609213784675)
              ·
                refine ⟨2117773747194913820677013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411849164796609213784675 2117773747194913820677013)
                ·
                  refine ⟨99270644399761585344235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2117773747194913820677013 99270644399761585344235)
                  ·
                    rfl

theorem cell20_217495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_217495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217495 prefixEnd_217495 := by exact prefixLift 217495
  have htrace : WordTrace (prefixWord ++ tailWord_217495) baseStart_217495 baseEnd_217495 := by
    simpa [prefixWord, tailWord_217495, baseEnd_217495] using wordTrace_append hprefix tailTrace_217495
  have hstable : (prefixWord ++ tailWord_217495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217495).length < 2 ^ (prefixWord ++ tailWord_217495).sum := by decide
  have hdescent : baseEnd_217495 < baseStart_217495 := by decide
  rcases family_descends (prefixWord ++ tailWord_217495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217498 : List Nat := [3, 1, 1, 4, 1, 3, 3, 4]
def baseStart_217498 : Nat := 118140960795 + 217498 * 2 ^ 59
def prefixEnd_217498 : Nat := 4983230072969 + 3 ^ 40 * 217498 * 2
def baseEnd_217498 : Nat := 33090671227168969414741

theorem tailTrace_217498 : CollatzResearch.WordTrace tailWord_217498 prefixEnd_217498 33090671227168969414741 := by
  unfold tailWord_217498
  simp only [CollatzResearch.WordTrace]
  refine ⟨1983200941512341636547287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5288535844032911030792765 1983200941512341636547287)
  ·
    refine ⟨2974801412268512454820931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1983200941512341636547287 2974801412268512454820931)
    ·
      refine ⟨4462202118402768682231397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2974801412268512454820931 4462202118402768682231397)
      ·
        refine ⟨836662897200519127918387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4462202118402768682231397 836662897200519127918387)
        ·
          refine ⟨1254994345800778691877581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836662897200519127918387 1254994345800778691877581)
          ·
            refine ⟨470622879675292009454093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1254994345800778691877581 470622879675292009454093)
            ·
              refine ⟨176483579878234503545285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 470622879675292009454093 176483579878234503545285)
              ·
                refine ⟨33090671227168969414741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176483579878234503545285 33090671227168969414741)
                ·
                  rfl

theorem cell20_217498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_217498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217498 prefixEnd_217498 := by exact prefixLift 217498
  have htrace : WordTrace (prefixWord ++ tailWord_217498) baseStart_217498 baseEnd_217498 := by
    simpa [prefixWord, tailWord_217498, baseEnd_217498] using wordTrace_append hprefix tailTrace_217498
  have hstable : (prefixWord ++ tailWord_217498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217498).length < 2 ^ (prefixWord ++ tailWord_217498).sum := by decide
  have hdescent : baseEnd_217498 < baseStart_217498 := by decide
  rcases family_descends (prefixWord ++ tailWord_217498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217529 : List Nat := [1, 2, 1, 4, 3, 1, 2, 4, 2]
def baseStart_217529 : Nat := 118140960795 + 217529 * 2 ^ 59
def prefixEnd_217529 : Nat := 4983230072969 + 3 ^ 40 * 217529 * 2
def baseEnd_217529 : Nat := 99286162926208578210763

theorem tailTrace_217529 : CollatzResearch.WordTrace tailWord_217529 prefixEnd_217529 99286162926208578210763 := by
  unfold tailWord_217529
  simp only [CollatzResearch.WordTrace]
  refine ⟨7933934428937058840567641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5289289619291372560378427 7933934428937058840567641)
  ·
    refine ⟨5950450821702794130425731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7933934428937058840567641 5950450821702794130425731)
    ·
      refine ⟨8925676232554191195638597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5950450821702794130425731 8925676232554191195638597)
      ·
        refine ⟨1673564293603910849182237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8925676232554191195638597 1673564293603910849182237)
        ·
          refine ⟨627586610101466568443339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1673564293603910849182237 627586610101466568443339)
          ·
            refine ⟨941379915152199852665009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627586610101466568443339 941379915152199852665009)
            ·
              refine ⟨706034936364149889498757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 941379915152199852665009 706034936364149889498757)
              ·
                refine ⟨132381550568278104281017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 706034936364149889498757 132381550568278104281017)
                ·
                  refine ⟨99286162926208578210763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132381550568278104281017 99286162926208578210763)
                  ·
                    rfl

theorem cell20_217529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 2].length) (baseStart_217529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217529 prefixEnd_217529 := by exact prefixLift 217529
  have htrace : WordTrace (prefixWord ++ tailWord_217529) baseStart_217529 baseEnd_217529 := by
    simpa [prefixWord, tailWord_217529, baseEnd_217529] using wordTrace_append hprefix tailTrace_217529
  have hstable : (prefixWord ++ tailWord_217529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217529).length < 2 ^ (prefixWord ++ tailWord_217529).sum := by decide
  have hdescent : baseEnd_217529 < baseStart_217529 := by decide
  rcases family_descends (prefixWord ++ tailWord_217529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217557 : List Nat := [1, 3, 2, 3, 1, 3, 1, 6]
def baseStart_217557 : Nat := 118140960795 + 217557 * 2 ^ 59
def prefixEnd_217557 : Nat := 4983230072969 + 3 ^ 40 * 217557 * 2
def baseEnd_217557 : Nat := 33099647629721641759105

theorem tailTrace_217557 : CollatzResearch.WordTrace tailWord_217557 prefixEnd_217557 33099647629721641759105 := by
  unfold tailWord_217557
  simp only [CollatzResearch.WordTrace]
  refine ⟨7934955672835619622586925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5289970448557079748391283 7934955672835619622586925)
  ·
    refine ⟨2975608377313357358470097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7934955672835619622586925 2975608377313357358470097)
    ·
      refine ⟨2231706282985018018852573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2975608377313357358470097 2231706282985018018852573)
      ·
        refine ⟨836889856119381757069715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2231706282985018018852573 836889856119381757069715)
        ·
          refine ⟨1255334784179072635604573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836889856119381757069715 1255334784179072635604573)
          ·
            refine ⟨470750544067152238351715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1255334784179072635604573 470750544067152238351715)
            ·
              refine ⟨706125816100728357527573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470750544067152238351715 706125816100728357527573)
              ·
                refine ⟨33099647629721641759105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 706125816100728357527573 33099647629721641759105)
                ·
                  rfl

theorem cell20_217557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 6].length) (baseStart_217557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217557 prefixEnd_217557 := by exact prefixLift 217557
  have htrace : WordTrace (prefixWord ++ tailWord_217557) baseStart_217557 baseEnd_217557 := by
    simpa [prefixWord, tailWord_217557, baseEnd_217557] using wordTrace_append hprefix tailTrace_217557
  have hstable : (prefixWord ++ tailWord_217557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217557).length < 2 ^ (prefixWord ++ tailWord_217557).sum := by decide
  have hdescent : baseEnd_217557 < baseStart_217557 := by decide
  rcases family_descends (prefixWord ++ tailWord_217557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217567 : List Nat := [1, 1, 2, 3, 3, 2, 3, 3, 2]
def baseStart_217567 : Nat := 118140960795 + 217567 * 2 ^ 59
def prefixEnd_217567 : Nat := 4983230072969 + 3 ^ 40 * 217567 * 2
def baseEnd_217567 : Nat := 99303507161649334943941

theorem tailTrace_217567 : CollatzResearch.WordTrace tailWord_217567 prefixEnd_217567 99303507161649334943941 := by
  unfold tailWord_217567
  simp only [CollatzResearch.WordTrace]
  refine ⟨7935320402799391330450955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5290213601866260886967303 7935320402799391330450955)
  ·
    refine ⟨11902980604199086995676433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7935320402799391330450955 11902980604199086995676433)
    ·
      refine ⟨8927235453149315246757325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11902980604199086995676433 8927235453149315246757325)
      ·
        refine ⟨3347713294930993217533997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8927235453149315246757325 3347713294930993217533997)
        ·
          refine ⟨1255392485599122456575249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3347713294930993217533997 1255392485599122456575249)
          ·
            refine ⟨941544364199341842431437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1255392485599122456575249 941544364199341842431437)
            ·
              refine ⟨353079136574753190911789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 941544364199341842431437 353079136574753190911789)
              ·
                refine ⟨132404676215532446591921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353079136574753190911789 132404676215532446591921)
                ·
                  refine ⟨99303507161649334943941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132404676215532446591921 99303507161649334943941)
                  ·
                    rfl

theorem cell20_217567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 2].length) (baseStart_217567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217567 prefixEnd_217567 := by exact prefixLift 217567
  have htrace : WordTrace (prefixWord ++ tailWord_217567) baseStart_217567 baseEnd_217567 := by
    simpa [prefixWord, tailWord_217567, baseEnd_217567] using wordTrace_append hprefix tailTrace_217567
  have hstable : (prefixWord ++ tailWord_217567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217567).length < 2 ^ (prefixWord ++ tailWord_217567).sum := by decide
  have hdescent : baseEnd_217567 < baseStart_217567 := by decide
  rcases family_descends (prefixWord ++ tailWord_217567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217570 : List Nat := [3, 3, 3, 2, 2, 1, 6]
def baseStart_217570 : Nat := 118140960795 + 217570 * 2 ^ 59
def prefixEnd_217570 : Nat := 4983230072969 + 3 ^ 40 * 217570 * 2
def baseEnd_217570 : Nat := 11033875160377184204881

theorem tailTrace_217570 : CollatzResearch.WordTrace tailWord_217570 prefixEnd_217570 11033875160377184204881 := by
  unfold tailWord_217570
  simp only [CollatzResearch.WordTrace]
  refine ⟨1983857455447130710702541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5290286547859015228540109 1983857455447130710702541)
  ·
    refine ⟨743946545792674016513453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1983857455447130710702541 743946545792674016513453)
    ·
      refine ⟨278979954672252756192545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 743946545792674016513453 278979954672252756192545)
      ·
        refine ⟨209234966004189567144409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278979954672252756192545 209234966004189567144409)
        ·
          refine ⟨156926224503142175358307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209234966004189567144409 156926224503142175358307)
          ·
            refine ⟨235389336754713263037461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156926224503142175358307 235389336754713263037461)
            ·
              refine ⟨11033875160377184204881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 235389336754713263037461 11033875160377184204881)
              ·
                rfl

theorem cell20_217570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 6].length) (baseStart_217570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217570 prefixEnd_217570 := by exact prefixLift 217570
  have htrace : WordTrace (prefixWord ++ tailWord_217570) baseStart_217570 baseEnd_217570 := by
    simpa [prefixWord, tailWord_217570, baseEnd_217570] using wordTrace_append hprefix tailTrace_217570
  have hstable : (prefixWord ++ tailWord_217570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217570).length < 2 ^ (prefixWord ++ tailWord_217570).sum := by decide
  have hdescent : baseEnd_217570 < baseStart_217570 := by decide
  rcases family_descends (prefixWord ++ tailWord_217570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217581 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 5]
def baseStart_217581 : Nat := 118140960795 + 217581 * 2 ^ 59
def prefixEnd_217581 : Nat := 4983230072969 + 3 ^ 40 * 217581 * 2
def baseEnd_217581 : Nat := 99309897143127508477217

theorem tailTrace_217581 : CollatzResearch.WordTrace tailWord_217581 prefixEnd_217581 99309897143127508477217 := by
  unfold tailWord_217581
  simp only [CollatzResearch.WordTrace]
  refine ⟨7935831024748671721460597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5290554016499114480973731 7935831024748671721460597)
  ·
    refine ⟨743984158570187973886931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7935831024748671721460597 743984158570187973886931)
    ·
      refine ⟨1115976237855281960830397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 743984158570187973886931 1115976237855281960830397)
      ·
        refine ⟨418491089195730735311399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1115976237855281960830397 418491089195730735311399)
        ·
          refine ⟨627736633793596102967099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418491089195730735311399 627736633793596102967099)
          ·
            refine ⟨941604950690394154450649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627736633793596102967099 941604950690394154450649)
            ·
              refine ⟨706203713017795615837987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 941604950690394154450649 706203713017795615837987)
              ·
                refine ⟨1059305569526693423756981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706203713017795615837987 1059305569526693423756981)
                ·
                  refine ⟨99309897143127508477217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1059305569526693423756981 99309897143127508477217)
                  ·
                    rfl

theorem cell20_217581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_217581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217581 prefixEnd_217581 := by exact prefixLift 217581
  have htrace : WordTrace (prefixWord ++ tailWord_217581) baseStart_217581 baseEnd_217581 := by
    simpa [prefixWord, tailWord_217581, baseEnd_217581] using wordTrace_append hprefix tailTrace_217581
  have hstable : (prefixWord ++ tailWord_217581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217581).length < 2 ^ (prefixWord ++ tailWord_217581).sum := by decide
  have hdescent : baseEnd_217581 < baseStart_217581 := by decide
  rcases family_descends (prefixWord ++ tailWord_217581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217639 : List Nat := [1, 1, 7, 2, 1, 1, 1, 4, 2]
def baseStart_217639 : Nat := 118140960795 + 217639 * 2 ^ 59
def prefixEnd_217639 : Nat := 4983230072969 + 3 ^ 40 * 217639 * 2
def baseEnd_217639 : Nat := 99336369923537084543647

theorem tailTrace_217639 : CollatzResearch.WordTrace tailWord_217639 prefixEnd_217639 99336369923537084543647 := by
  unfold tailWord_217639
  simp only [CollatzResearch.WordTrace]
  refine ⟨7937946458538547627071971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5291964305692365084714647 7937946458538547627071971)
  ·
    refine ⟨11906919687807821440607957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7937946458538547627071971 11906919687807821440607957)
    ·
      refine ⟨279068430182995815014249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 11906919687807821440607957 279068430182995815014249)
      ·
        refine ⟨209301322637246861260687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279068430182995815014249 209301322637246861260687)
        ·
          refine ⟨313951983955870291891031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209301322637246861260687 313951983955870291891031)
          ·
            refine ⟨470927975933805437836547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313951983955870291891031 470927975933805437836547)
            ·
              refine ⟨706391963900708156754821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470927975933805437836547 706391963900708156754821)
              ·
                refine ⟨132448493231382779391529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 706391963900708156754821 132448493231382779391529)
                ·
                  refine ⟨99336369923537084543647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132448493231382779391529 99336369923537084543647)
                  ·
                    rfl

theorem cell20_217639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 2].length) (baseStart_217639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217639 prefixEnd_217639 := by exact prefixLift 217639
  have htrace : WordTrace (prefixWord ++ tailWord_217639) baseStart_217639 baseEnd_217639 := by
    simpa [prefixWord, tailWord_217639, baseEnd_217639] using wordTrace_append hprefix tailTrace_217639
  have hstable : (prefixWord ++ tailWord_217639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217639).length < 2 ^ (prefixWord ++ tailWord_217639).sum := by decide
  have hdescent : baseEnd_217639 < baseStart_217639 := by decide
  rcases family_descends (prefixWord ++ tailWord_217639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217681 : List Nat := [1, 2, 2, 1, 3, 4, 2, 3, 2]
def baseStart_217681 : Nat := 118140960795 + 217681 * 2 ^ 59
def prefixEnd_217681 : Nat := 4983230072969 + 3 ^ 40 * 217681 * 2
def baseEnd_217681 : Nat := 99355539867971605143475

theorem tailTrace_217681 : CollatzResearch.WordTrace tailWord_217681 prefixEnd_217681 99355539867971605143475 := by
  unfold tailWord_217681
  simp only [CollatzResearch.WordTrace]
  refine ⟨7939478324386388800100897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5292985549590925866733931 7939478324386388800100897)
  ·
    refine ⟨5954608743289791600075673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7939478324386388800100897 5954608743289791600075673)
    ·
      refine ⟨4465956557467343700056755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5954608743289791600075673 4465956557467343700056755)
      ·
        refine ⟨6698934836201015550085133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4465956557467343700056755 6698934836201015550085133)
        ·
          refine ⟨2512100563575380831281925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6698934836201015550085133 2512100563575380831281925)
          ·
            refine ⟨471018855670383905865361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2512100563575380831281925 471018855670383905865361)
            ·
              refine ⟨353264141752787929399021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471018855670383905865361 353264141752787929399021)
              ·
                refine ⟨132474053157295473524633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353264141752787929399021 132474053157295473524633)
                ·
                  refine ⟨99355539867971605143475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132474053157295473524633 99355539867971605143475)
                  ·
                    rfl

theorem cell20_217681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 2].length) (baseStart_217681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217681 prefixEnd_217681 := by exact prefixLift 217681
  have htrace : WordTrace (prefixWord ++ tailWord_217681) baseStart_217681 baseEnd_217681 := by
    simpa [prefixWord, tailWord_217681, baseEnd_217681] using wordTrace_append hprefix tailTrace_217681
  have hstable : (prefixWord ++ tailWord_217681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217681).length < 2 ^ (prefixWord ++ tailWord_217681).sum := by decide
  have hdescent : baseEnd_217681 < baseStart_217681 := by decide
  rcases family_descends (prefixWord ++ tailWord_217681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217698 : List Nat := [3, 3, 2, 3, 1, 1, 2, 1, 4]
def baseStart_217698 : Nat := 118140960795 + 217698 * 2 ^ 59
def prefixEnd_217698 : Nat := 4983230072969 + 3 ^ 40 * 217698 * 2
def baseEnd_217698 : Nat := 99363299131195101576739

theorem tailTrace_217698 : CollatzResearch.WordTrace tailWord_217698 prefixEnd_217698 99363299131195101576739 := by
  unfold tailWord_217698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1985024591331200175867437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5293398910216533802313165 1985024591331200175867437)
  ·
    refine ⟨744384221749200065950289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1985024591331200175867437 744384221749200065950289)
    ·
      refine ⟨558288166311900049462717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 744384221749200065950289 558288166311900049462717)
      ·
        refine ⟨209358062366962518548519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 558288166311900049462717 209358062366962518548519)
        ·
          refine ⟨314037093550443777822779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209358062366962518548519 314037093550443777822779)
          ·
            refine ⟨471055640325665666734169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314037093550443777822779 471055640325665666734169)
            ·
              refine ⟨353291730244249250050627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471055640325665666734169 353291730244249250050627)
              ·
                refine ⟨529937595366373875075941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353291730244249250050627 529937595366373875075941)
                ·
                  refine ⟨99363299131195101576739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 529937595366373875075941 99363299131195101576739)
                  ·
                    rfl

theorem cell20_217698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_217698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217698 prefixEnd_217698 := by exact prefixLift 217698
  have htrace : WordTrace (prefixWord ++ tailWord_217698) baseStart_217698 baseEnd_217698 := by
    simpa [prefixWord, tailWord_217698, baseEnd_217698] using wordTrace_append hprefix tailTrace_217698
  have hstable : (prefixWord ++ tailWord_217698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217698).length < 2 ^ (prefixWord ++ tailWord_217698).sum := by decide
  have hdescent : baseEnd_217698 < baseStart_217698 := by decide
  rcases family_descends (prefixWord ++ tailWord_217698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217712 : List Nat := [2, 1, 1, 1, 7, 1, 3, 1, 3]
def baseStart_217712 : Nat := 118140960795 + 217712 * 2 ^ 59
def prefixEnd_217712 : Nat := 4983230072969 + 3 ^ 40 * 217712 * 2
def baseEnd_217712 : Nat := 99369689112673275110015

theorem tailTrace_217712 : CollatzResearch.WordTrace tailWord_217712 prefixEnd_217712 99369689112673275110015 := by
  unfold tailWord_217712
  simp only [CollatzResearch.WordTrace]
  refine ⟨3970304493637040547239695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5293739324849387396319593 3970304493637040547239695)
  ·
    refine ⟨5955456740455560820859543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3970304493637040547239695 5955456740455560820859543)
    ·
      refine ⟨8933185110683341231289315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5955456740455560820859543 8933185110683341231289315)
      ·
        refine ⟨13399777666025011846933973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8933185110683341231289315 13399777666025011846933973)
        ·
          refine ⟨314057289047461215162515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 13399777666025011846933973 314057289047461215162515)
          ·
            refine ⟨471085933571191822743773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314057289047461215162515 471085933571191822743773)
            ·
              refine ⟨176657225089196933528915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 471085933571191822743773 176657225089196933528915)
              ·
                refine ⟨264985837633795400293373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176657225089196933528915 264985837633795400293373)
                ·
                  refine ⟨99369689112673275110015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 264985837633795400293373 99369689112673275110015)
                  ·
                    rfl

theorem cell20_217712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 3].length) (baseStart_217712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217712 prefixEnd_217712 := by exact prefixLift 217712
  have htrace : WordTrace (prefixWord ++ tailWord_217712) baseStart_217712 baseEnd_217712 := by
    simpa [prefixWord, tailWord_217712, baseEnd_217712] using wordTrace_append hprefix tailTrace_217712
  have hstable : (prefixWord ++ tailWord_217712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217712).length < 2 ^ (prefixWord ++ tailWord_217712).sum := by decide
  have hdescent : baseEnd_217712 < baseStart_217712 := by decide
  rcases family_descends (prefixWord ++ tailWord_217712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217740 : List Nat := [2, 2, 1, 2, 1, 1, 2, 7, 2]
def baseStart_217740 : Nat := 118140960795 + 217740 * 2 ^ 59
def prefixEnd_217740 : Nat := 4983230072969 + 3 ^ 40 * 217740 * 2
def baseEnd_217740 : Nat := 99382469075629622176567

theorem tailTrace_217740 : CollatzResearch.WordTrace tailWord_217740 prefixEnd_217740 99382469075629622176567 := by
  unfold tailWord_217740
  simp only [CollatzResearch.WordTrace]
  refine ⟨3970815115586320938249337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5294420154115094584332449 3970815115586320938249337)
  ·
    refine ⟨2978111336689740703687003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3970815115586320938249337 2978111336689740703687003)
    ·
      refine ⟨4467167005034611055530505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2978111336689740703687003 4467167005034611055530505)
      ·
        refine ⟨3350375253775958291647879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4467167005034611055530505 3350375253775958291647879)
        ·
          refine ⟨5025562880663937437471819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3350375253775958291647879 5025562880663937437471819)
          ·
            refine ⟨7538344320995906156207729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5025562880663937437471819 7538344320995906156207729)
            ·
              refine ⟨5653758240746929617155797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7538344320995906156207729 5653758240746929617155797)
              ·
                refine ⟨132509958767506162902089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5653758240746929617155797 132509958767506162902089)
                ·
                  refine ⟨99382469075629622176567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132509958767506162902089 99382469075629622176567)
                  ·
                    rfl

theorem cell20_217740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_217740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217740 prefixEnd_217740 := by exact prefixLift 217740
  have htrace : WordTrace (prefixWord ++ tailWord_217740) baseStart_217740 baseEnd_217740 := by
    simpa [prefixWord, tailWord_217740, baseEnd_217740] using wordTrace_append hprefix tailTrace_217740
  have hstable : (prefixWord ++ tailWord_217740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217740).length < 2 ^ (prefixWord ++ tailWord_217740).sum := by decide
  have hdescent : baseEnd_217740 < baseStart_217740 := by decide
  rcases family_descends (prefixWord ++ tailWord_217740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217805 : List Nat := [1, 6, 2, 1, 2, 1, 2, 2, 3]
def baseStart_217805 : Nat := 118140960795 + 217805 * 2 ^ 59
def prefixEnd_217805 : Nat := 4983230072969 + 3 ^ 40 * 217805 * 2
def baseEnd_217805 : Nat := 99412136846778285009635

theorem tailTrace_217805 : CollatzResearch.WordTrace tailWord_217805 prefixEnd_217805 99412136846778285009635 := by
  unfold tailWord_217805
  simp only [CollatzResearch.WordTrace]
  refine ⟨7944000975937157977614869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5296000650624771985076579 7944000975937157977614869)
  ·
    refine ⟨372375045747054280200697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7944000975937157977614869 372375045747054280200697)
    ·
      refine ⟨279281284310290710150523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372375045747054280200697 279281284310290710150523)
      ·
        refine ⟨418921926465436065225785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279281284310290710150523 418921926465436065225785)
        ·
          refine ⟨314191444849077048919339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418921926465436065225785 314191444849077048919339)
          ·
            refine ⟨471287167273615573379009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314191444849077048919339 471287167273615573379009)
            ·
              refine ⟨353465375455211680034257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471287167273615573379009 353465375455211680034257)
              ·
                refine ⟨265099031591408760025693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353465375455211680034257 265099031591408760025693)
                ·
                  refine ⟨99412136846778285009635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265099031591408760025693 99412136846778285009635)
                  ·
                    rfl

theorem cell20_217805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_217805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217805 prefixEnd_217805 := by exact prefixLift 217805
  have htrace : WordTrace (prefixWord ++ tailWord_217805) baseStart_217805 baseEnd_217805 := by
    simpa [prefixWord, tailWord_217805, baseEnd_217805] using wordTrace_append hprefix tailTrace_217805
  have hstable : (prefixWord ++ tailWord_217805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217805).length < 2 ^ (prefixWord ++ tailWord_217805).sum := by decide
  have hdescent : baseEnd_217805 < baseStart_217805 := by decide
  rcases family_descends (prefixWord ++ tailWord_217805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217806 : List Nat := [4, 1, 1, 1, 3, 10]
def baseStart_217806 : Nat := 118140960795 + 217806 * 2 ^ 59
def prefixEnd_217806 : Nat := 4983230072969 + 3 ^ 40 * 217806 * 2
def baseEnd_217806 : Nat := 3681947899038026888011

theorem tailTrace_217806 : CollatzResearch.WordTrace tailWord_217806 prefixEnd_217806 3681947899038026888011 := by
  unfold tailWord_217806
  simp only [CollatzResearch.WordTrace]
  refine ⟨993004681116691893550159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5296024965955690098934181 993004681116691893550159)
  ·
    refine ⟨1489507021675037840325239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 993004681116691893550159 1489507021675037840325239)
    ·
      refine ⟨2234260532512556760487859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1489507021675037840325239 2234260532512556760487859)
      ·
        refine ⟨3351390798768835140731789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2234260532512556760487859 3351390798768835140731789)
        ·
          refine ⟨1256771549538313177774421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3351390798768835140731789 1256771549538313177774421)
          ·
            refine ⟨3681947899038026888011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1256771549538313177774421 3681947899038026888011)
            ·
              rfl

theorem cell20_217806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 10].length) (baseStart_217806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217806 prefixEnd_217806 := by exact prefixLift 217806
  have htrace : WordTrace (prefixWord ++ tailWord_217806) baseStart_217806 baseEnd_217806 := by
    simpa [prefixWord, tailWord_217806, baseEnd_217806] using wordTrace_append hprefix tailTrace_217806
  have hstable : (prefixWord ++ tailWord_217806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217806).length < 2 ^ (prefixWord ++ tailWord_217806).sum := by decide
  have hdescent : baseEnd_217806 < baseStart_217806 := by decide
  rcases family_descends (prefixWord ++ tailWord_217806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217812 : List Nat := [2, 4, 1, 3, 2, 1, 1, 4, 2]
def baseStart_217812 : Nat := 118140960795 + 217812 * 2 ^ 59
def prefixEnd_217812 : Nat := 4983230072969 + 3 ^ 40 * 217812 * 2
def baseEnd_217812 : Nat := 99415331837517371776273

theorem tailTrace_217812 : CollatzResearch.WordTrace tailWord_217812 prefixEnd_217812 99415331837517371776273 := by
  unfold tailWord_217812
  simp only [CollatzResearch.WordTrace]
  refine ⟨3972128143455899086559845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5296170857941198782079793 3972128143455899086559845)
  ·
    refine ⟨744774026897981078729971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3972128143455899086559845 744774026897981078729971)
    ·
      refine ⟨1117161040346971618094957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 744774026897981078729971 1117161040346971618094957)
      ·
        refine ⟨418935390130114356785609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1117161040346971618094957 418935390130114356785609)
        ·
          refine ⟨314201542597585767589207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418935390130114356785609 314201542597585767589207)
          ·
            refine ⟨471302313896378651383811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314201542597585767589207 471302313896378651383811)
            ·
              refine ⟨706953470844567977075717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471302313896378651383811 706953470844567977075717)
              ·
                refine ⟨132553775783356495701697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 706953470844567977075717 132553775783356495701697)
                ·
                  refine ⟨99415331837517371776273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132553775783356495701697 99415331837517371776273)
                  ·
                    rfl

theorem cell20_217812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_217812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217812 prefixEnd_217812 := by exact prefixLift 217812
  have htrace : WordTrace (prefixWord ++ tailWord_217812) baseStart_217812 baseEnd_217812 := by
    simpa [prefixWord, tailWord_217812, baseEnd_217812] using wordTrace_append hprefix tailTrace_217812
  have hstable : (prefixWord ++ tailWord_217812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217812).length < 2 ^ (prefixWord ++ tailWord_217812).sum := by decide
  have hdescent : baseEnd_217812 < baseStart_217812 := by decide
  rcases family_descends (prefixWord ++ tailWord_217812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217823 : List Nat := [1, 1, 2, 3, 2, 5, 1, 5]
def baseStart_217823 : Nat := 118140960795 + 217823 * 2 ^ 59
def prefixEnd_217823 : Nat := 4983230072969 + 3 ^ 40 * 217823 * 2
def baseEnd_217823 : Nat := 33140117512416740803187

theorem tailTrace_217823 : CollatzResearch.WordTrace tailWord_217823 prefixEnd_217823 33140117512416740803187 := by
  unfold tailWord_217823
  simp only [CollatzResearch.WordTrace]
  refine ⟨7944657489871947051770123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5296438326581298034513415 7944657489871947051770123)
  ·
    refine ⟨11916986234807920577655185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7944657489871947051770123 11916986234807920577655185)
    ·
      refine ⟨8937739676105940433241389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11916986234807920577655185 8937739676105940433241389)
      ·
        refine ⟨3351652378539727662465521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8937739676105940433241389 3351652378539727662465521)
        ·
          refine ⟨2513739283904795746849141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3351652378539727662465521 2513739283904795746849141)
          ·
            refine ⟨235663057866074601267107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2513739283904795746849141 235663057866074601267107)
            ·
              refine ⟨353494586799111901900661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235663057866074601267107 353494586799111901900661)
              ·
                refine ⟨33140117512416740803187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 353494586799111901900661 33140117512416740803187)
                ·
                  rfl

theorem cell20_217823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 5].length) (baseStart_217823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217823 prefixEnd_217823 := by exact prefixLift 217823
  have htrace : WordTrace (prefixWord ++ tailWord_217823) baseStart_217823 baseEnd_217823 := by
    simpa [prefixWord, tailWord_217823, baseEnd_217823] using wordTrace_append hprefix tailTrace_217823
  have hstable : (prefixWord ++ tailWord_217823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217823).length < 2 ^ (prefixWord ++ tailWord_217823).sum := by decide
  have hdescent : baseEnd_217823 < baseStart_217823 := by decide
  rcases family_descends (prefixWord ++ tailWord_217823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217875 : List Nat := [1, 1, 1, 2, 1, 3, 6, 1, 4]
def baseStart_217875 : Nat := 118140960795 + 217875 * 2 ^ 59
def prefixEnd_217875 : Nat := 4983230072969 + 3 ^ 40 * 217875 * 2
def baseEnd_217875 : Nat := 99444086754169152676015

theorem tailTrace_217875 : CollatzResearch.WordTrace tailWord_217875 prefixEnd_217875 99444086754169152676015 := by
  unfold tailWord_217875
  simp only [CollatzResearch.WordTrace]
  refine ⟨7946554085683559932663079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5297702723789039955108719 7946554085683559932663079)
  ·
    refine ⟨11919831128525339898994619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7946554085683559932663079 11919831128525339898994619)
    ·
      refine ⟨17879746692788009848491929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11919831128525339898994619 17879746692788009848491929)
      ·
        refine ⟨13409810019591007386368947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17879746692788009848491929 13409810019591007386368947)
        ·
          refine ⟨20114715029386511079553421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13409810019591007386368947 20114715029386511079553421)
          ·
            refine ⟨7543018136019941654832533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20114715029386511079553421 7543018136019941654832533)
            ·
              refine ⟨353578975125934765070275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7543018136019941654832533 353578975125934765070275)
              ·
                refine ⟨530368462688902147605413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353578975125934765070275 530368462688902147605413)
                ·
                  refine ⟨99444086754169152676015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 530368462688902147605413 99444086754169152676015)
                  ·
                    rfl

theorem cell20_217875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 4].length) (baseStart_217875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217875 prefixEnd_217875 := by exact prefixLift 217875
  have htrace : WordTrace (prefixWord ++ tailWord_217875) baseStart_217875 baseEnd_217875 := by
    simpa [prefixWord, tailWord_217875, baseEnd_217875] using wordTrace_append hprefix tailTrace_217875
  have hstable : (prefixWord ++ tailWord_217875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217875).length < 2 ^ (prefixWord ++ tailWord_217875).sum := by decide
  have hdescent : baseEnd_217875 < baseStart_217875 := by decide
  rcases family_descends (prefixWord ++ tailWord_217875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217882 : List Nat := [3, 1, 1, 3, 2, 1, 2, 7]
def baseStart_217882 : Nat := 118140960795 + 217882 * 2 ^ 59
def prefixEnd_217882 : Nat := 4983230072969 + 3 ^ 40 * 217882 * 2
def baseEnd_217882 : Nat := 33149093914969413147551

theorem tailTrace_217882 : CollatzResearch.WordTrace tailWord_217882 prefixEnd_217882 33149093914969413147551 := by
  unfold tailWord_217882
  simp only [CollatzResearch.WordTrace]
  refine ⟨1986702349164550032041975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5297872931105466752111933 1986702349164550032041975)
  ·
    refine ⟨2980053523746825048062963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1986702349164550032041975 2980053523746825048062963)
    ·
      refine ⟨4470080285620237572094445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2980053523746825048062963 4470080285620237572094445)
      ·
        refine ⟨1676280107107589089535417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4470080285620237572094445 1676280107107589089535417)
        ·
          refine ⟨1257210080330691817151563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1676280107107589089535417 1257210080330691817151563)
          ·
            refine ⟨1885815120496037725727345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257210080330691817151563 1885815120496037725727345)
            ·
              refine ⟨1414361340372028294295509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1885815120496037725727345 1414361340372028294295509)
              ·
                refine ⟨33149093914969413147551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1414361340372028294295509 33149093914969413147551)
                ·
                  rfl

theorem cell20_217882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_217882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217882 prefixEnd_217882 := by exact prefixLift 217882
  have htrace : WordTrace (prefixWord ++ tailWord_217882) baseStart_217882 baseEnd_217882 := by
    simpa [prefixWord, tailWord_217882, baseEnd_217882] using wordTrace_append hprefix tailTrace_217882
  have hstable : (prefixWord ++ tailWord_217882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217882).length < 2 ^ (prefixWord ++ tailWord_217882).sum := by decide
  have hdescent : baseEnd_217882 < baseStart_217882 := by decide
  rcases family_descends (prefixWord ++ tailWord_217882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217909 : List Nat := [1, 3, 3, 1, 3, 1, 3, 3, 2]
def baseStart_217909 : Nat := 118140960795 + 217909 * 2 ^ 59
def prefixEnd_217909 : Nat := 4983230072969 + 3 ^ 40 * 217909 * 2
def baseEnd_217909 : Nat := 99459605280616145542543

theorem tailTrace_217909 : CollatzResearch.WordTrace tailWord_217909 prefixEnd_217909 99459605280616145542543 := by
  unfold tailWord_217909
  simp only [CollatzResearch.WordTrace]
  refine ⟨7947794167560383739400781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5298529445040255826267187 7947794167560383739400781)
  ·
    refine ⟨2980422812835143902275293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7947794167560383739400781 2980422812835143902275293)
    ·
      refine ⟨1117658554813178963353235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2980422812835143902275293 1117658554813178963353235)
      ·
        refine ⟨1676487832219768445029853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1117658554813178963353235 1676487832219768445029853)
        ·
          refine ⟨628682937082413166886195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1676487832219768445029853 628682937082413166886195)
          ·
            refine ⟨943024405623619750329293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628682937082413166886195 943024405623619750329293)
            ·
              refine ⟨353634152108857406373485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 943024405623619750329293 353634152108857406373485)
              ·
                refine ⟨132612807040821527390057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353634152108857406373485 132612807040821527390057)
                ·
                  refine ⟨99459605280616145542543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132612807040821527390057 99459605280616145542543)
                  ·
                    rfl

theorem cell20_217909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_217909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217909 prefixEnd_217909 := by exact prefixLift 217909
  have htrace : WordTrace (prefixWord ++ tailWord_217909) baseStart_217909 baseEnd_217909 := by
    simpa [prefixWord, tailWord_217909, baseEnd_217909] using wordTrace_append hprefix tailTrace_217909
  have hstable : (prefixWord ++ tailWord_217909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217909).length < 2 ^ (prefixWord ++ tailWord_217909).sum := by decide
  have hdescent : baseEnd_217909 < baseStart_217909 := by decide
  rcases family_descends (prefixWord ++ tailWord_217909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217937 : List Nat := [1, 2, 2, 1, 6, 1, 2, 5]
def baseStart_217937 : Nat := 118140960795 + 217937 * 2 ^ 59
def prefixEnd_217937 : Nat := 4983230072969 + 3 ^ 40 * 217937 * 2
def baseEnd_217937 : Nat := 33157461747857497536365

theorem tailTrace_217937 : CollatzResearch.WordTrace tailWord_217937 prefixEnd_217937 33157461747857497536365 := by
  unfold tailWord_217937
  simp only [CollatzResearch.WordTrace]
  refine ⟨7948815411458944521420065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5299210274305963014280043 7948815411458944521420065)
  ·
    refine ⟨5961611558594208391065049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7948815411458944521420065 5961611558594208391065049)
    ·
      refine ⟨4471208668945656293298787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5961611558594208391065049 4471208668945656293298787)
      ·
        refine ⟨6706813003418484439948181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4471208668945656293298787 6706813003418484439948181)
        ·
          refine ⟨314381859535241458122571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6706813003418484439948181 314381859535241458122571)
          ·
            refine ⟨471572789302862187183857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314381859535241458122571 471572789302862187183857)
            ·
              refine ⟨353679591977146640387893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471572789302862187183857 353679591977146640387893)
              ·
                refine ⟨33157461747857497536365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 353679591977146640387893 33157461747857497536365)
                ·
                  rfl

theorem cell20_217937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 5].length) (baseStart_217937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217937 prefixEnd_217937 := by exact prefixLift 217937
  have htrace : WordTrace (prefixWord ++ tailWord_217937) baseStart_217937 baseEnd_217937 := by
    simpa [prefixWord, tailWord_217937, baseEnd_217937] using wordTrace_append hprefix tailTrace_217937
  have hstable : (prefixWord ++ tailWord_217937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217937).length < 2 ^ (prefixWord ++ tailWord_217937).sum := by decide
  have hdescent : baseEnd_217937 < baseStart_217937 := by decide
  rcases family_descends (prefixWord ++ tailWord_217937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217996 : List Nat := [2, 2, 1, 2, 1, 2, 5, 5]
def baseStart_217996 : Nat := 118140960795 + 217996 * 2 ^ 59
def prefixEnd_217996 : Nat := 4983230072969 + 3 ^ 40 * 217996 * 2
def baseEnd_217996 : Nat := 33166438150410169880729

theorem tailTrace_217996 : CollatzResearch.WordTrace tailWord_217996 prefixEnd_217996 33166438150410169880729 := by
  unfold tailWord_217996
  simp only [CollatzResearch.WordTrace]
  refine ⟨3975483659122598798908921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5300644878830131731878561 3975483659122598798908921)
  ·
    refine ⟨2981612744341949099181691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3975483659122598798908921 2981612744341949099181691)
    ·
      refine ⟨4472419116512923648772537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2981612744341949099181691 4472419116512923648772537)
      ·
        refine ⟨3354314337384692736579403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4472419116512923648772537 3354314337384692736579403)
        ·
          refine ⟨5031471506077039104869105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3354314337384692736579403 5031471506077039104869105)
          ·
            refine ⟨3773603629557779328651829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5031471506077039104869105 3773603629557779328651829)
            ·
              refine ⟨353775340271041812061109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3773603629557779328651829 353775340271041812061109)
              ·
                refine ⟨33166438150410169880729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 353775340271041812061109 33166438150410169880729)
                ·
                  rfl

theorem cell20_217996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_217996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_217996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_217996 prefixEnd_217996 := by exact prefixLift 217996
  have htrace : WordTrace (prefixWord ++ tailWord_217996) baseStart_217996 baseEnd_217996 := by
    simpa [prefixWord, tailWord_217996, baseEnd_217996] using wordTrace_append hprefix tailTrace_217996
  have hstable : (prefixWord ++ tailWord_217996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217996).length < 2 ^ (prefixWord ++ tailWord_217996).sum := by decide
  have hdescent : baseEnd_217996 < baseStart_217996 := by decide
  rcases family_descends (prefixWord ++ tailWord_217996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218013 : List Nat := [1, 4, 2, 1, 2, 1, 5, 4]
def baseStart_218013 : Nat := 118140960795 + 218013 * 2 ^ 59
def prefixEnd_218013 : Nat := 4983230072969 + 3 ^ 40 * 218013 * 2
def baseEnd_218013 : Nat := 33169024571484668691817

theorem tailTrace_218013 : CollatzResearch.WordTrace tailWord_218013 prefixEnd_218013 33169024571484668691817 := by
  unfold tailWord_218013
  simp only [CollatzResearch.WordTrace]
  refine ⟨7951587359183609501186693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5301058239455739667457795 7951587359183609501186693)
  ·
    refine ⟨1490922629846926781472505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7951587359183609501186693 1490922629846926781472505)
    ·
      refine ⟨1118191972385195086104379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1490922629846926781472505 1118191972385195086104379)
      ·
        refine ⟨1677287958577792629156569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1118191972385195086104379 1677287958577792629156569)
        ·
          refine ⟨1257965968933344471867427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1677287958577792629156569 1257965968933344471867427)
          ·
            refine ⟨1886948953400016707801141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257965968933344471867427 1886948953400016707801141)
            ·
              refine ⟨176901464381251566356357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1886948953400016707801141 176901464381251566356357)
              ·
                refine ⟨33169024571484668691817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176901464381251566356357 33169024571484668691817)
                ·
                  rfl

theorem cell20_218013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 4].length) (baseStart_218013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218013 prefixEnd_218013 := by exact prefixLift 218013
  have htrace : WordTrace (prefixWord ++ tailWord_218013) baseStart_218013 baseEnd_218013 := by
    simpa [prefixWord, tailWord_218013, baseEnd_218013] using wordTrace_append hprefix tailTrace_218013
  have hstable : (prefixWord ++ tailWord_218013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218013).length < 2 ^ (prefixWord ++ tailWord_218013).sum := by decide
  have hdescent : baseEnd_218013 < baseStart_218013 := by decide
  rcases family_descends (prefixWord ++ tailWord_218013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218068 : List Nat := [2, 4, 1, 2, 1, 4, 2, 4]
def baseStart_218068 : Nat := 118140960795 + 218068 * 2 ^ 59
def prefixEnd_218068 : Nat := 4983230072969 + 3 ^ 40 * 218068 * 2
def baseEnd_218068 : Nat := 33177392404372753080631

theorem tailTrace_218068 : CollatzResearch.WordTrace tailWord_218068 prefixEnd_218068 33177392404372753080631 := by
  unfold tailWord_218068
  simp only [CollatzResearch.WordTrace]
  refine ⟨3976796686992176947219429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5302395582656235929625905 3976796686992176947219429)
  ·
    refine ⟨745649378811033177603643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3976796686992176947219429 745649378811033177603643)
    ·
      refine ⟨1118474068216549766405465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 745649378811033177603643 1118474068216549766405465)
      ·
        refine ⟨838855551162412324804099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1118474068216549766405465 838855551162412324804099)
        ·
          refine ⟨1258283326743618487206149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838855551162412324804099 1258283326743618487206149)
          ·
            refine ⟨235928123764428466351153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1258283326743618487206149 235928123764428466351153)
            ·
              refine ⟨176946092823321349763365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235928123764428466351153 176946092823321349763365)
              ·
                refine ⟨33177392404372753080631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176946092823321349763365 33177392404372753080631)
                ·
                  rfl

theorem cell20_218068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_218068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218068 prefixEnd_218068 := by exact prefixLift 218068
  have htrace : WordTrace (prefixWord ++ tailWord_218068) baseStart_218068 baseEnd_218068 := by
    simpa [prefixWord, tailWord_218068, baseEnd_218068] using wordTrace_append hprefix tailTrace_218068
  have hstable : (prefixWord ++ tailWord_218068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218068).length < 2 ^ (prefixWord ++ tailWord_218068).sum := by decide
  have hdescent : baseEnd_218068 < baseStart_218068 := by decide
  rcases family_descends (prefixWord ++ tailWord_218068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218072 : List Nat := [2, 1, 2, 2, 2, 4, 1, 6]
def baseStart_218072 : Nat := 118140960795 + 218072 * 2 ^ 59
def prefixEnd_218072 : Nat := 4983230072969 + 3 ^ 40 * 218072 * 2
def baseEnd_218072 : Nat := 33178000974037341036181

theorem tailTrace_218072 : CollatzResearch.WordTrace tailWord_218072 prefixEnd_218072 33178000974037341036181 := by
  unfold tailWord_218072
  simp only [CollatzResearch.WordTrace]
  refine ⟨3976869632984931288792235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5302492843979908385056313 3976869632984931288792235)
  ·
    refine ⟨5965304449477396933188353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3976869632984931288792235 5965304449477396933188353)
    ·
      refine ⟨4473978337108047699891265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5965304449477396933188353 4473978337108047699891265)
      ·
        refine ⟨3355483752831035774918449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4473978337108047699891265 3355483752831035774918449)
        ·
          refine ⟨2516612814623276831188837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3355483752831035774918449 2516612814623276831188837)
          ·
            refine ⟨471864902741864405847907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2516612814623276831188837 471864902741864405847907)
            ·
              refine ⟨707797354112796608771861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471864902741864405847907 707797354112796608771861)
              ·
                refine ⟨33178000974037341036181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 707797354112796608771861 33178000974037341036181)
                ·
                  rfl

theorem cell20_218072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_218072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218072 prefixEnd_218072 := by exact prefixLift 218072
  have htrace : WordTrace (prefixWord ++ tailWord_218072) baseStart_218072 baseEnd_218072 := by
    simpa [prefixWord, tailWord_218072, baseEnd_218072] using wordTrace_append hprefix tailTrace_218072
  have hstable : (prefixWord ++ tailWord_218072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218072).length < 2 ^ (prefixWord ++ tailWord_218072).sum := by decide
  have hdescent : baseEnd_218072 < baseStart_218072 := by decide
  rcases family_descends (prefixWord ++ tailWord_218072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218113 : List Nat := [1, 2, 4, 1, 2, 2, 4, 1, 3]
def baseStart_218113 : Nat := 118140960795 + 218113 * 2 ^ 59
def prefixEnd_218113 : Nat := 4983230072969 + 3 ^ 40 * 218113 * 2
def baseEnd_218113 : Nat := 99552716439298102741709

theorem tailTrace_218113 : CollatzResearch.WordTrace tailWord_218113 prefixEnd_218113 99552716439298102741709 := by
  unfold tailWord_218113
  simp only [CollatzResearch.WordTrace]
  refine ⟨7955234658821326579826993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5303489772547551053217995 7955234658821326579826993)
  ·
    refine ⟨5966425994115994934870245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7955234658821326579826993 5966425994115994934870245)
    ·
      refine ⟨1118704873896749050288171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5966425994115994934870245 1118704873896749050288171)
      ·
        refine ⟨1678057310845123575432257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1118704873896749050288171 1678057310845123575432257)
        ·
          refine ⟨1258542983133842681574193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1678057310845123575432257 1258542983133842681574193)
          ·
            refine ⟨943907237350382011180645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1258542983133842681574193 943907237350382011180645)
            ·
              refine ⟨176982607003196627096371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 943907237350382011180645 176982607003196627096371)
              ·
                refine ⟨265473910504794940644557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176982607003196627096371 265473910504794940644557)
                ·
                  refine ⟨99552716439298102741709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265473910504794940644557 99552716439298102741709)
                  ·
                    rfl

theorem cell20_218113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 3].length) (baseStart_218113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218113 prefixEnd_218113 := by exact prefixLift 218113
  have htrace : WordTrace (prefixWord ++ tailWord_218113) baseStart_218113 baseEnd_218113 := by
    simpa [prefixWord, tailWord_218113, baseEnd_218113] using wordTrace_append hprefix tailTrace_218113
  have hstable : (prefixWord ++ tailWord_218113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218113).length < 2 ^ (prefixWord ++ tailWord_218113).sum := by decide
  have hdescent : baseEnd_218113 < baseStart_218113 := by decide
  rcases family_descends (prefixWord ++ tailWord_218113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218148 : List Nat := [2, 3, 1, 4, 1, 9]
def baseStart_218148 : Nat := 118140960795 + 218148 * 2 ^ 59
def prefixEnd_218148 : Nat := 4983230072969 + 3 ^ 40 * 218148 * 2
def baseEnd_218148 : Nat := 3687729310851612465737

theorem tailTrace_218148 : CollatzResearch.WordTrace tailWord_218148 prefixEnd_218148 3687729310851612465737 := by
  unfold tailWord_218148
  simp only [CollatzResearch.WordTrace]
  refine ⟨3978255606847263778675549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5304340809129685038234065 3978255606847263778675549)
  ·
    refine ⟨1491845852567723917003331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3978255606847263778675549 1491845852567723917003331)
    ·
      refine ⟨2237768778851585875504997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1491845852567723917003331 2237768778851585875504997)
      ·
        refine ⟨419581646034672351657187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2237768778851585875504997 419581646034672351657187)
        ·
          refine ⟨629372469052008527485781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419581646034672351657187 629372469052008527485781)
          ·
            refine ⟨3687729310851612465737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 629372469052008527485781 3687729310851612465737)
            ·
              rfl

theorem cell20_218148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 9].length) (baseStart_218148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218148 prefixEnd_218148 := by exact prefixLift 218148
  have htrace : WordTrace (prefixWord ++ tailWord_218148) baseStart_218148 baseEnd_218148 := by
    simpa [prefixWord, tailWord_218148, baseEnd_218148] using wordTrace_append hprefix tailTrace_218148
  have hstable : (prefixWord ++ tailWord_218148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218148).length < 2 ^ (prefixWord ++ tailWord_218148).sum := by decide
  have hdescent : baseEnd_218148 < baseStart_218148 := by decide
  rcases family_descends (prefixWord ++ tailWord_218148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218151 : List Nat := [1, 1, 7, 1, 1, 1, 1, 4, 3]
def baseStart_218151 : Nat := 118140960795 + 218151 * 2 ^ 59
def prefixEnd_218151 : Nat := 4983230072969 + 3 ^ 40 * 218151 * 2
def baseEnd_218151 : Nat := 99570060674738859474887

theorem tailTrace_218151 : CollatzResearch.WordTrace tailWord_218151 prefixEnd_218151 99570060674738859474887 := by
  unfold tailWord_218151
  simp only [CollatzResearch.WordTrace]
  refine ⟨7956620632683659069710307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5304413755122439379806871 7956620632683659069710307)
  ·
    refine ⟨11934930949025488604565461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7956620632683659069710307 11934930949025488604565461)
    ·
      refine ⟨279724944117784889169503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 11934930949025488604565461 279724944117784889169503)
      ·
        refine ⟨419587416176677333754255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279724944117784889169503 419587416176677333754255)
        ·
          refine ⟨629381124265016000631383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419587416176677333754255 629381124265016000631383)
          ·
            refine ⟨944071686397524000947075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629381124265016000631383 944071686397524000947075)
            ·
              refine ⟨1416107529596286001420613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944071686397524000947075 1416107529596286001420613)
              ·
                refine ⟨265520161799303625266365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1416107529596286001420613 265520161799303625266365)
                ·
                  refine ⟨99570060674738859474887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265520161799303625266365 99570060674738859474887)
                  ·
                    rfl

theorem cell20_218151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 3].length) (baseStart_218151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218151 prefixEnd_218151 := by exact prefixLift 218151
  have htrace : WordTrace (prefixWord ++ tailWord_218151) baseStart_218151 baseEnd_218151 := by
    simpa [prefixWord, tailWord_218151, baseEnd_218151] using wordTrace_append hprefix tailTrace_218151
  have hstable : (prefixWord ++ tailWord_218151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218151).length < 2 ^ (prefixWord ++ tailWord_218151).sum := by decide
  have hdescent : baseEnd_218151 < baseStart_218151 := by decide
  rcases family_descends (prefixWord ++ tailWord_218151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218172 : List Nat := [2, 2, 2, 2, 2, 2, 2, 3, 3]
def baseStart_218172 : Nat := 118140960795 + 218172 * 2 ^ 59
def prefixEnd_218172 : Nat := 4983230072969 + 3 ^ 40 * 218172 * 2
def baseEnd_218172 : Nat := 99579645646956119774801

theorem tailTrace_218172 : CollatzResearch.WordTrace tailWord_218172 prefixEnd_218172 99579645646956119774801 := by
  unfold tailWord_218172
  simp only [CollatzResearch.WordTrace]
  refine ⟨3978693282803789828112385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5304924377071719770816513 3978693282803789828112385)
  ·
    refine ⟨2984019962102842371084289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3978693282803789828112385 2984019962102842371084289)
    ·
      refine ⟨2238014971577131778313217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2984019962102842371084289 2238014971577131778313217)
      ·
        refine ⟨1678511228682848833734913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2238014971577131778313217 1678511228682848833734913)
        ·
          refine ⟨1258883421512136625301185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1678511228682848833734913 1258883421512136625301185)
          ·
            refine ⟨944162566134102468975889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1258883421512136625301185 944162566134102468975889)
            ·
              refine ⟨708121924600576851731917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 944162566134102468975889 708121924600576851731917)
              ·
                refine ⟨265545721725216319399469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 708121924600576851731917 265545721725216319399469)
                ·
                  refine ⟨99579645646956119774801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265545721725216319399469 99579645646956119774801)
                  ·
                    rfl

theorem cell20_218172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_218172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218172 prefixEnd_218172 := by exact prefixLift 218172
  have htrace : WordTrace (prefixWord ++ tailWord_218172) baseStart_218172 baseEnd_218172 := by
    simpa [prefixWord, tailWord_218172, baseEnd_218172] using wordTrace_append hprefix tailTrace_218172
  have hstable : (prefixWord ++ tailWord_218172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218172).length < 2 ^ (prefixWord ++ tailWord_218172).sum := by decide
  have hdescent : baseEnd_218172 < baseStart_218172 := by decide
  rcases family_descends (prefixWord ++ tailWord_218172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218196 : List Nat := [2, 4, 1, 1, 1, 1, 3, 5, 2]
def baseStart_218196 : Nat := 118140960795 + 218196 * 2 ^ 59
def prefixEnd_218196 : Nat := 4983230072969 + 3 ^ 40 * 218196 * 2
def baseEnd_218196 : Nat := 99590599900918702974703

theorem tailTrace_218196 : CollatzResearch.WordTrace tailWord_218196 prefixEnd_218196 99590599900918702974703 := by
  unfold tailWord_218196
  simp only [CollatzResearch.WordTrace]
  refine ⟨3979130958760315877549221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5305507945013754503398961 3979130958760315877549221)
  ·
    refine ⟨746087054767559227040479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3979130958760315877549221 746087054767559227040479)
    ·
      refine ⟨1119130582151338840560719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 746087054767559227040479 1119130582151338840560719)
      ·
        refine ⟨1678695873227008260841079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119130582151338840560719 1678695873227008260841079)
        ·
          refine ⟨2518043809840512391261619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678695873227008260841079 2518043809840512391261619)
          ·
            refine ⟨3777065714760768586892429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2518043809840512391261619 3777065714760768586892429)
            ·
              refine ⟨1416399643035288220084661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3777065714760768586892429 1416399643035288220084661)
              ·
                refine ⟨132787466534558270632937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1416399643035288220084661 132787466534558270632937)
                ·
                  refine ⟨99590599900918702974703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132787466534558270632937 99590599900918702974703)
                  ·
                    rfl

theorem cell20_218196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_218196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218196 prefixEnd_218196 := by exact prefixLift 218196
  have htrace : WordTrace (prefixWord ++ tailWord_218196) baseStart_218196 baseEnd_218196 := by
    simpa [prefixWord, tailWord_218196, baseEnd_218196] using wordTrace_append hprefix tailTrace_218196
  have hstable : (prefixWord ++ tailWord_218196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218196).length < 2 ^ (prefixWord ++ tailWord_218196).sum := by decide
  have hdescent : baseEnd_218196 < baseStart_218196 := by decide
  rcases family_descends (prefixWord ++ tailWord_218196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218200 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 6]
def baseStart_218200 : Nat := 118140960795 + 218200 * 2 ^ 59
def prefixEnd_218200 : Nat := 4983230072969 + 3 ^ 40 * 218200 * 2
def baseEnd_218200 : Nat := 99592425609912466841353

theorem tailTrace_218200 : CollatzResearch.WordTrace tailWord_218200 prefixEnd_218200 99592425609912466841353 := by
  unfold tailWord_218200
  simp only [CollatzResearch.WordTrace]
  refine ⟨3979203904753070219122027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5305605206337426958829369 3979203904753070219122027)
  ·
    refine ⟨5968805857129605328683041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3979203904753070219122027 5968805857129605328683041)
    ·
      refine ⟨4476604392847203996512281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5968805857129605328683041 4476604392847203996512281)
      ·
        refine ⟨3357453294635402997384211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4476604392847203996512281 3357453294635402997384211)
        ·
          refine ⟨5036179941953104496076317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3357453294635402997384211 5036179941953104496076317)
          ·
            refine ⟨1888567478232414186028619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5036179941953104496076317 1888567478232414186028619)
            ·
              refine ⟨2832851217348621279042929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888567478232414186028619 2832851217348621279042929)
              ·
                refine ⟨2124638413011465959282197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2832851217348621279042929 2124638413011465959282197)
                ·
                  refine ⟨99592425609912466841353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2124638413011465959282197 99592425609912466841353)
                  ·
                    rfl

theorem cell20_218200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_218200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218200 prefixEnd_218200 := by exact prefixLift 218200
  have htrace : WordTrace (prefixWord ++ tailWord_218200) baseStart_218200 baseEnd_218200 := by
    simpa [prefixWord, tailWord_218200, baseEnd_218200] using wordTrace_append hprefix tailTrace_218200
  have hstable : (prefixWord ++ tailWord_218200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218200).length < 2 ^ (prefixWord ++ tailWord_218200).sum := by decide
  have hdescent : baseEnd_218200 < baseStart_218200 := by decide
  rcases family_descends (prefixWord ++ tailWord_218200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218206 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_218206 : Nat := 118140960795 + 218206 * 2 ^ 59
def prefixEnd_218206 : Nat := 4983230072969 + 3 ^ 40 * 218206 * 2
def baseEnd_218206 : Nat := 99595164173403112641329

theorem tailTrace_218206 : CollatzResearch.WordTrace tailWord_218206 prefixEnd_218206 99595164173403112641329 := by
  unfold tailWord_218206
  simp only [CollatzResearch.WordTrace]
  refine ⟨994828330935550432870309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5305751098322935641974981 994828330935550432870309)
  ·
    refine ⟨186530312050415706163183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 994828330935550432870309 186530312050415706163183)
    ·
      refine ⟨279795468075623559244775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186530312050415706163183 279795468075623559244775)
      ·
        refine ⟨419693202113435338867163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279795468075623559244775 419693202113435338867163)
        ·
          refine ⟨629539803170153008300745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419693202113435338867163 629539803170153008300745)
          ·
            refine ⟨472154852377614756225559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 629539803170153008300745 472154852377614756225559)
            ·
              refine ⟨708232278566422134338339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472154852377614756225559 708232278566422134338339)
              ·
                refine ⟨1062348417849633201507509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708232278566422134338339 1062348417849633201507509)
                ·
                  refine ⟨99595164173403112641329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1062348417849633201507509 99595164173403112641329)
                  ·
                    rfl

theorem cell20_218206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_218206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218206 prefixEnd_218206 := by exact prefixLift 218206
  have htrace : WordTrace (prefixWord ++ tailWord_218206) baseStart_218206 baseEnd_218206 := by
    simpa [prefixWord, tailWord_218206, baseEnd_218206] using wordTrace_append hprefix tailTrace_218206
  have hstable : (prefixWord ++ tailWord_218206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218206).length < 2 ^ (prefixWord ++ tailWord_218206).sum := by decide
  have hdescent : baseEnd_218206 < baseStart_218206 := by decide
  rcases family_descends (prefixWord ++ tailWord_218206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218207 : List Nat := [1, 1, 2, 3, 1, 1, 11]
def baseStart_218207 : Nat := 118140960795 + 218207 * 2 ^ 59
def prefixEnd_218207 : Nat := 4983230072969 + 3 ^ 40 * 218207 * 2
def baseEnd_218207 : Nat := 11066180066739061511999

theorem tailTrace_218207 : CollatzResearch.WordTrace tailWord_218207 prefixEnd_218207 11066180066739061511999 := by
  unfold tailWord_218207
  simp only [CollatzResearch.WordTrace]
  refine ⟨7958663120480780633748875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5305775413653853755832583 7958663120480780633748875)
  ·
    refine ⟨11937994680721170950623313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7958663120480780633748875 11937994680721170950623313)
    ·
      refine ⟨8953496010540878212967485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11937994680721170950623313 8953496010540878212967485)
      ·
        refine ⟨3357561003952829329862807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8953496010540878212967485 3357561003952829329862807)
        ·
          refine ⟨5036341505929243994794211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3357561003952829329862807 5036341505929243994794211)
          ·
            refine ⟨7554512258893865992191317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5036341505929243994794211 7554512258893865992191317)
            ·
              refine ⟨11066180066739061511999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7554512258893865992191317 11066180066739061511999)
              ·
                rfl

theorem cell20_218207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 11].length) (baseStart_218207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218207 prefixEnd_218207 := by exact prefixLift 218207
  have htrace : WordTrace (prefixWord ++ tailWord_218207) baseStart_218207 baseEnd_218207 := by
    simpa [prefixWord, tailWord_218207, baseEnd_218207] using wordTrace_append hprefix tailTrace_218207
  have hstable : (prefixWord ++ tailWord_218207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218207).length < 2 ^ (prefixWord ++ tailWord_218207).sum := by decide
  have hdescent : baseEnd_218207 < baseStart_218207 := by decide
  rcases family_descends (prefixWord ++ tailWord_218207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218217 : List Nat := [1, 2, 1, 1, 1, 7, 2, 1, 4]
def baseStart_218217 : Nat := 118140960795 + 218217 * 2 ^ 59
def prefixEnd_218217 : Nat := 4983230072969 + 3 ^ 40 * 218217 * 2
def baseEnd_218217 : Nat := 99600184873135963274617

theorem tailTrace_218217 : CollatzResearch.WordTrace tailWord_218217 prefixEnd_218217 99600184873135963274617 := by
  unfold tailWord_218217
  simp only [CollatzResearch.WordTrace]
  refine ⟨7959027850444552341612905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5306018566963034894408603 7959027850444552341612905)
  ·
    refine ⟨5969270887833414256209679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7959027850444552341612905 5969270887833414256209679)
    ·
      refine ⟨8953906331750121384314519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5969270887833414256209679 8953906331750121384314519)
      ·
        refine ⟨13430859497625182076471779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8953906331750121384314519 13430859497625182076471779)
        ·
          refine ⟨20146289246437773114707669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13430859497625182076471779 20146289246437773114707669)
          ·
            refine ⟨472178654213385307375961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 20146289246437773114707669 472178654213385307375961)
            ·
              refine ⟨354133990660038980531971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472178654213385307375961 354133990660038980531971)
              ·
                refine ⟨531200985990058470797957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354133990660038980531971 531200985990058470797957)
                ·
                  refine ⟨99600184873135963274617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 531200985990058470797957 99600184873135963274617)
                  ·
                    rfl

theorem cell20_218217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_218217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218217 prefixEnd_218217 := by exact prefixLift 218217
  have htrace : WordTrace (prefixWord ++ tailWord_218217) baseStart_218217 baseEnd_218217 := by
    simpa [prefixWord, tailWord_218217, baseEnd_218217] using wordTrace_append hprefix tailTrace_218217
  have hstable : (prefixWord ++ tailWord_218217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218217).length < 2 ^ (prefixWord ++ tailWord_218217).sum := by decide
  have hdescent : baseEnd_218217 < baseStart_218217 := by decide
  rcases family_descends (prefixWord ++ tailWord_218217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218241 : List Nat := [1, 2, 4, 2, 2, 1, 4, 4]
def baseStart_218241 : Nat := 118140960795 + 218241 * 2 ^ 59
def prefixEnd_218241 : Nat := 4983230072969 + 3 ^ 40 * 218241 * 2
def baseEnd_218241 : Nat := 33203713042366182158173

theorem tailTrace_218241 : CollatzResearch.WordTrace tailWord_218241 prefixEnd_218241 33203713042366182158173 := by
  unfold tailWord_218241
  simp only [CollatzResearch.WordTrace]
  refine ⟨7959903202357604440486577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5306602134905069626991051 7959903202357604440486577)
  ·
    refine ⟨5969927401768203330364933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7959903202357604440486577 5969927401768203330364933)
    ·
      refine ⟨1119361387831538124443425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5969927401768203330364933 1119361387831538124443425)
      ·
        refine ⟨839521040873653593332569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1119361387831538124443425 839521040873653593332569)
        ·
          refine ⟨629640780655240194999427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 839521040873653593332569 629640780655240194999427)
          ·
            refine ⟨944461170982860292499141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629640780655240194999427 944461170982860292499141)
            ·
              refine ⟨177086469559286304843589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 944461170982860292499141 177086469559286304843589)
              ·
                refine ⟨33203713042366182158173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177086469559286304843589 33203713042366182158173)
                ·
                  rfl

theorem cell20_218241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 4].length) (baseStart_218241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218241 prefixEnd_218241 := by exact prefixLift 218241
  have htrace : WordTrace (prefixWord ++ tailWord_218241) baseStart_218241 baseEnd_218241 := by
    simpa [prefixWord, tailWord_218241, baseEnd_218241] using wordTrace_append hprefix tailTrace_218241
  have hstable : (prefixWord ++ tailWord_218241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218241).length < 2 ^ (prefixWord ++ tailWord_218241).sum := by decide
  have hdescent : baseEnd_218241 < baseStart_218241 := by decide
  rcases family_descends (prefixWord ++ tailWord_218241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218269 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 5]
def baseStart_218269 : Nat := 118140960795 + 218269 * 2 ^ 59
def prefixEnd_218269 : Nat := 4983230072969 + 3 ^ 40 * 218269 * 2
def baseEnd_218269 : Nat := 99623919090054893541071

theorem tailTrace_218269 : CollatzResearch.WordTrace tailWord_218269 prefixEnd_218269 99623919090054893541071 := by
  unfold tailWord_218269
  simp only [CollatzResearch.WordTrace]
  refine ⟨7960924446256165222505861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5307282964170776815003907 7960924446256165222505861)
  ·
    refine ⟨1492673333673030979219849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7960924446256165222505861 1492673333673030979219849)
    ·
      refine ⟨1119505000254773234414887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1492673333673030979219849 1119505000254773234414887)
      ·
        refine ⟨1679257500382159851622331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119505000254773234414887 1679257500382159851622331)
        ·
          refine ⟨2518886250573239777433497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1679257500382159851622331 2518886250573239777433497)
          ·
            refine ⟨1889164687929929833075123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2518886250573239777433497 1889164687929929833075123)
            ·
              refine ⟨2833747031894894749612685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1889164687929929833075123 2833747031894894749612685)
              ·
                refine ⟨1062655136960585531104757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2833747031894894749612685 1062655136960585531104757)
                ·
                  refine ⟨99623919090054893541071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1062655136960585531104757 99623919090054893541071)
                  ·
                    rfl

theorem cell20_218269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_218269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218269 prefixEnd_218269 := by exact prefixLift 218269
  have htrace : WordTrace (prefixWord ++ tailWord_218269) baseStart_218269 baseEnd_218269 := by
    simpa [prefixWord, tailWord_218269, baseEnd_218269] using wordTrace_append hprefix tailTrace_218269
  have hstable : (prefixWord ++ tailWord_218269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218269).length < 2 ^ (prefixWord ++ tailWord_218269).sum := by decide
  have hdescent : baseEnd_218269 < baseStart_218269 := by decide
  rcases family_descends (prefixWord ++ tailWord_218269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218279 : List Nat := [1, 1, 6, 2, 1, 2, 2, 5]
def baseStart_218279 : Nat := 118140960795 + 218279 * 2 ^ 59
def prefixEnd_218279 : Nat := 4983230072969 + 3 ^ 40 * 218279 * 2
def baseEnd_218279 : Nat := 33209494454179767735899

theorem tailTrace_218279 : CollatzResearch.WordTrace tailWord_218279 prefixEnd_218279 33209494454179767735899 := by
  unfold tailWord_218279
  simp only [CollatzResearch.WordTrace]
  refine ⟨7961289176219936930369891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5307526117479957953579927 7961289176219936930369891)
  ·
    refine ⟨11941933764329905395554837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7961289176219936930369891 11941933764329905395554837)
    ·
      refine ⟨559778145202964315416633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11941933764329905395554837 559778145202964315416633)
      ·
        refine ⟨419833608902223236562475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 559778145202964315416633 419833608902223236562475)
        ·
          refine ⟨629750413353334854843713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419833608902223236562475 629750413353334854843713)
          ·
            refine ⟨472312810015001141132785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 629750413353334854843713 472312810015001141132785)
            ·
              refine ⟨354234607511250855849589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472312810015001141132785 354234607511250855849589)
              ·
                refine ⟨33209494454179767735899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 354234607511250855849589 33209494454179767735899)
                ·
                  rfl

theorem cell20_218279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 5].length) (baseStart_218279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218279 prefixEnd_218279 := by exact prefixLift 218279
  have htrace : WordTrace (prefixWord ++ tailWord_218279) baseStart_218279 baseEnd_218279 := by
    simpa [prefixWord, tailWord_218279, baseEnd_218279] using wordTrace_append hprefix tailTrace_218279
  have hstable : (prefixWord ++ tailWord_218279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218279).length < 2 ^ (prefixWord ++ tailWord_218279).sum := by decide
  have hdescent : baseEnd_218279 < baseStart_218279 := by decide
  rcases family_descends (prefixWord ++ tailWord_218279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218282 : List Nat := [3, 1, 5, 1, 1, 1, 4, 1, 3]
def baseStart_218282 : Nat := 118140960795 + 218282 * 2 ^ 59
def prefixEnd_218282 : Nat := 4983230072969 + 3 ^ 40 * 218282 * 2
def baseEnd_218282 : Nat := 99629852644284626107685

theorem tailTrace_218282 : CollatzResearch.WordTrace tailWord_218282 prefixEnd_218282 99629852644284626107685 := by
  unfold tailWord_218282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1990349648802267110682275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5307599063472712295152733 1990349648802267110682275)
  ·
    refine ⟨2985524473203400666023413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1990349648802267110682275 2985524473203400666023413)
    ·
      refine ⟨279892919362818812439695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2985524473203400666023413 279892919362818812439695)
      ·
        refine ⟨419839379044228218659543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279892919362818812439695 419839379044228218659543)
        ·
          refine ⟨629759068566342327989315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419839379044228218659543 629759068566342327989315)
          ·
            refine ⟨944638602849513491983973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629759068566342327989315 944638602849513491983973)
            ·
              refine ⟨177119738034283779746995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 944638602849513491983973 177119738034283779746995)
              ·
                refine ⟨265679607051425669620493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177119738034283779746995 265679607051425669620493)
                ·
                  refine ⟨99629852644284626107685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265679607051425669620493 99629852644284626107685)
                  ·
                    rfl

theorem cell20_218282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_218282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218282 prefixEnd_218282 := by exact prefixLift 218282
  have htrace : WordTrace (prefixWord ++ tailWord_218282) baseStart_218282 baseEnd_218282 := by
    simpa [prefixWord, tailWord_218282, baseEnd_218282] using wordTrace_append hprefix tailTrace_218282
  have hstable : (prefixWord ++ tailWord_218282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218282).length < 2 ^ (prefixWord ++ tailWord_218282).sum := by decide
  have hdescent : baseEnd_218282 < baseStart_218282 := by decide
  rcases family_descends (prefixWord ++ tailWord_218282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218300 : List Nat := [2, 2, 2, 3, 2, 1, 2, 6]
def baseStart_218300 : Nat := 118140960795 + 218300 * 2 ^ 59
def prefixEnd_218300 : Nat := 4983230072969 + 3 ^ 40 * 218300 * 2
def baseEnd_218300 : Nat := 33212689444918854502537

theorem tailTrace_218300 : CollatzResearch.WordTrace tailWord_218300 prefixEnd_218300 33212689444918854502537 := by
  unfold tailWord_218300
  simp only [CollatzResearch.WordTrace]
  refine ⟨3981027554571928758442177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5308036739429238344589569 3981027554571928758442177)
  ·
    refine ⟨2985770665928946568831633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3981027554571928758442177 2985770665928946568831633)
    ·
      refine ⟨2239327999446709926623725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2985770665928946568831633 2239327999446709926623725)
      ·
        refine ⟨839747999792516222483897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2239327999446709926623725 839747999792516222483897)
        ·
          refine ⟨629810999844387166862923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 839747999792516222483897 629810999844387166862923)
          ·
            refine ⟨944716499766580750294385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629810999844387166862923 944716499766580750294385)
            ·
              refine ⟨708537374824935562720789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 944716499766580750294385 708537374824935562720789)
              ·
                refine ⟨33212689444918854502537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 708537374824935562720789 33212689444918854502537)
                ·
                  rfl

theorem cell20_218300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_218300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218300 prefixEnd_218300 := by exact prefixLift 218300
  have htrace : WordTrace (prefixWord ++ tailWord_218300) baseStart_218300 baseEnd_218300 := by
    simpa [prefixWord, tailWord_218300, baseEnd_218300] using wordTrace_append hprefix tailTrace_218300
  have hstable : (prefixWord ++ tailWord_218300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218300).length < 2 ^ (prefixWord ++ tailWord_218300).sum := by decide
  have hdescent : baseEnd_218300 < baseStart_218300 := by decide
  rcases family_descends (prefixWord ++ tailWord_218300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218317 : List Nat := [1, 6, 2, 2, 9]
def baseStart_218317 : Nat := 118140960795 + 218317 * 2 ^ 59
def prefixEnd_218317 : Nat := 4983230072969 + 3 ^ 40 * 218317 * 2
def baseEnd_218317 : Nat := 1230195402444198270875

theorem tailTrace_218317 : CollatzResearch.WordTrace tailWord_218317 prefixEnd_218317 1230195402444198270875 := by
  unfold tailWord_218317
  simp only [CollatzResearch.WordTrace]
  refine ⟨7962675150082269420253205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5308450100054846280168803 7962675150082269420253205)
  ·
    refine ⟨373250397660106379074369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7962675150082269420253205 373250397660106379074369)
    ·
      refine ⟨279937798245079784305777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373250397660106379074369 279937798245079784305777)
      ·
        refine ⟨209953348683809838229333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279937798245079784305777 209953348683809838229333)
        ·
          refine ⟨1230195402444198270875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 209953348683809838229333 1230195402444198270875)
          ·
            rfl

theorem cell20_218317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 9].length) (baseStart_218317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218317 prefixEnd_218317 := by exact prefixLift 218317
  have htrace : WordTrace (prefixWord ++ tailWord_218317) baseStart_218317 baseEnd_218317 := by
    simpa [prefixWord, tailWord_218317, baseEnd_218317] using wordTrace_append hprefix tailTrace_218317
  have hstable : (prefixWord ++ tailWord_218317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218317).length < 2 ^ (prefixWord ++ tailWord_218317).sum := by decide
  have hdescent : baseEnd_218317 < baseStart_218317 := by decide
  rcases family_descends (prefixWord ++ tailWord_218317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218376 : List Nat := [2, 1, 3, 2, 4, 1, 7]
def baseStart_218376 : Nat := 118140960795 + 218376 * 2 ^ 59
def prefixEnd_218376 : Nat := 4983230072969 + 3 ^ 40 * 218376 * 2
def baseEnd_218376 : Nat := 11074750756182008552663

theorem tailTrace_218376 : CollatzResearch.WordTrace tailWord_218376 prefixEnd_218376 11074750756182008552663 := by
  unfold tailWord_218376
  simp only [CollatzResearch.WordTrace]
  refine ⟨3982413528434261248325491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5309884704579014997767321 3982413528434261248325491)
  ·
    refine ⟨5973620292651391872488237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3982413528434261248325491 5973620292651391872488237)
    ·
      refine ⟨2240107609744271952183089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5973620292651391872488237 2240107609744271952183089)
      ·
        refine ⟨1680080707308203964137317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2240107609744271952183089 1680080707308203964137317)
        ·
          refine ⟨315015132620288243275747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1680080707308203964137317 315015132620288243275747)
          ·
            refine ⟨472522698930432364913621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315015132620288243275747 472522698930432364913621)
            ·
              refine ⟨11074750756182008552663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 472522698930432364913621 11074750756182008552663)
              ·
                rfl

theorem cell20_218376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 7].length) (baseStart_218376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218376 prefixEnd_218376 := by exact prefixLift 218376
  have htrace : WordTrace (prefixWord ++ tailWord_218376) baseStart_218376 baseEnd_218376 := by
    simpa [prefixWord, tailWord_218376, baseEnd_218376] using wordTrace_append hprefix tailTrace_218376
  have hstable : (prefixWord ++ tailWord_218376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218376).length < 2 ^ (prefixWord ++ tailWord_218376).sum := by decide
  have hdescent : baseEnd_218376 < baseStart_218376 := by decide
  rcases family_descends (prefixWord ++ tailWord_218376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218410 : List Nat := [3, 1, 4, 2, 1, 3, 2, 4]
def baseStart_218410 : Nat := 118140960795 + 218410 * 2 ^ 59
def prefixEnd_218410 : Nat := 4983230072969 + 3 ^ 40 * 218410 * 2
def baseEnd_218410 : Nat := 33229425110695023280165

theorem tailTrace_218410 : CollatzResearch.WordTrace tailWord_218410 prefixEnd_218410 33229425110695023280165 := by
  unfold tailWord_218410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1991516784686336575847171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5310711425830230868925789 1991516784686336575847171)
  ·
    refine ⟨2987275177029504863770757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1991516784686336575847171 2987275177029504863770757)
    ·
      refine ⟨560114095693032161957017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2987275177029504863770757 560114095693032161957017)
      ·
        refine ⟨420085571769774121467763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560114095693032161957017 420085571769774121467763)
        ·
          refine ⟨630128357654661182201645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420085571769774121467763 630128357654661182201645)
          ·
            refine ⟨236298134120497943325617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 630128357654661182201645 236298134120497943325617)
            ·
              refine ⟨177223600590373457494213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236298134120497943325617 177223600590373457494213)
              ·
                refine ⟨33229425110695023280165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177223600590373457494213 33229425110695023280165)
                ·
                  rfl

theorem cell20_218410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_218410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218410 prefixEnd_218410 := by exact prefixLift 218410
  have htrace : WordTrace (prefixWord ++ tailWord_218410) baseStart_218410 baseEnd_218410 := by
    simpa [prefixWord, tailWord_218410, baseEnd_218410] using wordTrace_append hprefix tailTrace_218410
  have hstable : (prefixWord ++ tailWord_218410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218410).length < 2 ^ (prefixWord ++ tailWord_218410).sum := by decide
  have hdescent : baseEnd_218410 < baseStart_218410 := by decide
  rcases family_descends (prefixWord ++ tailWord_218410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218421 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 5]
def baseStart_218421 : Nat := 118140960795 + 218421 * 2 ^ 59
def prefixEnd_218421 : Nat := 4983230072969 + 3 ^ 40 * 218421 * 2
def baseEnd_218421 : Nat := 99693296031817920473783

theorem tailTrace_218421 : CollatzResearch.WordTrace tailWord_218421 prefixEnd_218421 99693296031817920473783 := by
  unfold tailWord_218421
  simp only [CollatzResearch.WordTrace]
  refine ⟨7966468341705495182039117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5310978894470330121359411 7966468341705495182039117)
  ·
    refine ⟨2987425628139560693264669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7966468341705495182039117 2987425628139560693264669)
    ·
      refine ⟨1120284610552335259974251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2987425628139560693264669 1120284610552335259974251)
      ·
        refine ⟨1680426915828502889961377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1120284610552335259974251 1680426915828502889961377)
        ·
          refine ⟨1260320186871377167471033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1680426915828502889961377 1260320186871377167471033)
          ·
            refine ⟨945240140153532875603275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1260320186871377167471033 945240140153532875603275)
            ·
              refine ⟨1417860210230299313404913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945240140153532875603275 1417860210230299313404913)
              ·
                refine ⟨1063395157672724485053685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1417860210230299313404913 1063395157672724485053685)
                ·
                  refine ⟨99693296031817920473783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1063395157672724485053685 99693296031817920473783)
                  ·
                    rfl

theorem cell20_218421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_218421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218421 prefixEnd_218421 := by exact prefixLift 218421
  have htrace : WordTrace (prefixWord ++ tailWord_218421) baseStart_218421 baseEnd_218421 := by
    simpa [prefixWord, tailWord_218421, baseEnd_218421] using wordTrace_append hprefix tailTrace_218421
  have hstable : (prefixWord ++ tailWord_218421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218421).length < 2 ^ (prefixWord ++ tailWord_218421).sum := by decide
  have hdescent : baseEnd_218421 < baseStart_218421 := by decide
  rcases family_descends (prefixWord ++ tailWord_218421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218452 : List Nat := [2, 4, 1, 1, 2, 1, 4, 5]
def baseStart_218452 : Nat := 118140960795 + 218452 * 2 ^ 59
def prefixEnd_218452 : Nat := 4983230072969 + 3 ^ 40 * 218452 * 2
def baseEnd_218452 : Nat := 33235815092173196813441

theorem tailTrace_218452 : CollatzResearch.WordTrace tailWord_218452 prefixEnd_218452 33235815092173196813441 := by
  unfold tailWord_218452
  simp only [CollatzResearch.WordTrace]
  refine ⟨3983799502296593738208805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5311732669728791650945073 3983799502296593738208805)
  ·
    refine ⟨746962406680611325914151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3983799502296593738208805 746962406680611325914151)
    ·
      refine ⟨1120443610020916988871227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 746962406680611325914151 1120443610020916988871227)
      ·
        refine ⟨1680665415031375483306841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1120443610020916988871227 1680665415031375483306841)
        ·
          refine ⟨1260499061273531612480131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1680665415031375483306841 1260499061273531612480131)
          ·
            refine ⟨1890748591910297418720197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1260499061273531612480131 1890748591910297418720197)
            ·
              refine ⟨354515360983180766010037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1890748591910297418720197 354515360983180766010037)
              ·
                refine ⟨33235815092173196813441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 354515360983180766010037 33235815092173196813441)
                ·
                  rfl

theorem cell20_218452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_218452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218452 prefixEnd_218452 := by exact prefixLift 218452
  have htrace : WordTrace (prefixWord ++ tailWord_218452) baseStart_218452 baseEnd_218452 := by
    simpa [prefixWord, tailWord_218452, baseEnd_218452] using wordTrace_append hprefix tailTrace_218452
  have hstable : (prefixWord ++ tailWord_218452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218452).length < 2 ^ (prefixWord ++ tailWord_218452).sum := by decide
  have hdescent : baseEnd_218452 < baseStart_218452 := by decide
  rcases family_descends (prefixWord ++ tailWord_218452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218455 : List Nat := [1, 1, 3, 2, 3, 4, 2, 1, 3]
def baseStart_218455 : Nat := 118140960795 + 218455 * 2 ^ 59
def prefixEnd_218455 : Nat := 4983230072969 + 3 ^ 40 * 218455 * 2
def baseEnd_218455 : Nat := 99708814558264913340311

theorem tailTrace_218455 : CollatzResearch.WordTrace tailWord_218455 prefixEnd_218455 99708814558264913340311 := by
  unfold tailWord_218455
  simp only [CollatzResearch.WordTrace]
  refine ⟨7967708423582318988776819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5311805615721545992517879 7967708423582318988776819)
  ·
    refine ⟨11951562635373478483165229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7967708423582318988776819 11951562635373478483165229)
    ·
      refine ⟨4481835988265054431186961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11951562635373478483165229 4481835988265054431186961)
      ·
        refine ⟨3361376991198790823390221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4481835988265054431186961 3361376991198790823390221)
        ·
          refine ⟨1260516371699546558771333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3361376991198790823390221 1260516371699546558771333)
          ·
            refine ⟨236346819693664979769625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1260516371699546558771333 236346819693664979769625)
            ·
              refine ⟨177260114770248734827219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236346819693664979769625 177260114770248734827219)
              ·
                refine ⟨265890172155373102240829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177260114770248734827219 265890172155373102240829)
                ·
                  refine ⟨99708814558264913340311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265890172155373102240829 99708814558264913340311)
                  ·
                    rfl

theorem cell20_218455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 3].length) (baseStart_218455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218455 prefixEnd_218455 := by exact prefixLift 218455
  have htrace : WordTrace (prefixWord ++ tailWord_218455) baseStart_218455 baseEnd_218455 := by
    simpa [prefixWord, tailWord_218455, baseEnd_218455] using wordTrace_append hprefix tailTrace_218455
  have hstable : (prefixWord ++ tailWord_218455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218455).length < 2 ^ (prefixWord ++ tailWord_218455).sum := by decide
  have hdescent : baseEnd_218455 < baseStart_218455 := by decide
  rcases family_descends (prefixWord ++ tailWord_218455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218500 : List Nat := [2, 3, 2, 1, 1, 4, 1, 4, 2]
def baseStart_218500 : Nat := 118140960795 + 218500 * 2 ^ 59
def prefixEnd_218500 : Nat := 4983230072969 + 3 ^ 40 * 218500 * 2
def baseEnd_218500 : Nat := 99729353784444756840127

theorem tailTrace_218500 : CollatzResearch.WordTrace tailWord_218500 prefixEnd_218500 99729353784444756840127 := by
  unfold tailWord_218500
  simp only [CollatzResearch.WordTrace]
  refine ⟨3984674854209645837082477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5312899805612861116109969 3984674854209645837082477)
  ·
    refine ⟨1494253070328617188905929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3984674854209645837082477 1494253070328617188905929)
    ·
      refine ⟨1120689802746462891679447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1494253070328617188905929 1120689802746462891679447)
      ·
        refine ⟨1681034704119694337519171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1120689802746462891679447 1681034704119694337519171)
        ·
          refine ⟨2521552056179541506278757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1681034704119694337519171 2521552056179541506278757)
          ·
            refine ⟨472791010533664032427267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2521552056179541506278757 472791010533664032427267)
            ·
              refine ⟨709186515800496048640901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472791010533664032427267 709186515800496048640901)
              ·
                refine ⟨132972471712593009120169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 709186515800496048640901 132972471712593009120169)
                ·
                  refine ⟨99729353784444756840127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132972471712593009120169 99729353784444756840127)
                  ·
                    rfl

theorem cell20_218500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_218500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218500 prefixEnd_218500 := by exact prefixLift 218500
  have htrace : WordTrace (prefixWord ++ tailWord_218500) baseStart_218500 baseEnd_218500 := by
    simpa [prefixWord, tailWord_218500, baseEnd_218500] using wordTrace_append hprefix tailTrace_218500
  have hstable : (prefixWord ++ tailWord_218500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218500).length < 2 ^ (prefixWord ++ tailWord_218500).sum := by decide
  have hdescent : baseEnd_218500 < baseStart_218500 := by decide
  rcases family_descends (prefixWord ++ tailWord_218500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218524 : List Nat := [2, 2, 3, 4, 1, 1, 3, 4]
def baseStart_218524 : Nat := 118140960795 + 218524 * 2 ^ 59
def prefixEnd_218524 : Nat := 4983230072969 + 3 ^ 40 * 218524 * 2
def baseEnd_218524 : Nat := 33246769346135780013343

theorem tailTrace_218524 : CollatzResearch.WordTrace tailWord_218524 prefixEnd_218524 33246769346135780013343 := by
  unfold tailWord_218524
  simp only [CollatzResearch.WordTrace]
  refine ⟨3985112530166171886519313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5313483373554895848692417 3985112530166171886519313)
  ·
    refine ⟨2988834397624628914889485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3985112530166171886519313 2988834397624628914889485)
    ·
      refine ⟨1120812899109235843083557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2988834397624628914889485 1120812899109235843083557)
      ·
        refine ⟨210152418582981720578167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1120812899109235843083557 210152418582981720578167)
        ·
          refine ⟨315228627874472580867251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210152418582981720578167 315228627874472580867251)
          ·
            refine ⟨472842941811708871300877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315228627874472580867251 472842941811708871300877)
            ·
              refine ⟨177316103179390826737829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 472842941811708871300877 177316103179390826737829)
              ·
                refine ⟨33246769346135780013343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177316103179390826737829 33246769346135780013343)
                ·
                  rfl

theorem cell20_218524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_218524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218524 prefixEnd_218524 := by exact prefixLift 218524
  have htrace : WordTrace (prefixWord ++ tailWord_218524) baseStart_218524 baseEnd_218524 := by
    simpa [prefixWord, tailWord_218524, baseEnd_218524] using wordTrace_append hprefix tailTrace_218524
  have hstable : (prefixWord ++ tailWord_218524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218524).length < 2 ^ (prefixWord ++ tailWord_218524).sum := by decide
  have hdescent : baseEnd_218524 < baseStart_218524 := by decide
  rcases family_descends (prefixWord ++ tailWord_218524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218528 : List Nat := [2, 1, 1, 4, 1, 2, 5, 4]
def baseStart_218528 : Nat := 118140960795 + 218528 * 2 ^ 59
def prefixEnd_218528 : Nat := 4983230072969 + 3 ^ 40 * 218528 * 2
def baseEnd_218528 : Nat := 33247377915800367968893

theorem tailTrace_218528 : CollatzResearch.WordTrace tailWord_218528 prefixEnd_218528 33247377915800367968893 := by
  unfold tailWord_218528
  simp only [CollatzResearch.WordTrace]
  refine ⟨3985185476158926228092119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5313580634878568304122825 3985185476158926228092119)
  ·
    refine ⟨5977778214238389342138179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3985185476158926228092119 5977778214238389342138179)
    ·
      refine ⟨8966667321357584013207269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5977778214238389342138179 8966667321357584013207269)
      ·
        refine ⟨1681250122754547002476363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8966667321357584013207269 1681250122754547002476363)
        ·
          refine ⟨2521875184131820503714545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1681250122754547002476363 2521875184131820503714545)
          ·
            refine ⟨1891406388098865377785909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2521875184131820503714545 1891406388098865377785909)
            ·
              refine ⟨177319348884268629167429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1891406388098865377785909 177319348884268629167429)
              ·
                refine ⟨33247377915800367968893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177319348884268629167429 33247377915800367968893)
                ·
                  rfl

theorem cell20_218528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_218528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218528 prefixEnd_218528 := by exact prefixLift 218528
  have htrace : WordTrace (prefixWord ++ tailWord_218528) baseStart_218528 baseEnd_218528 := by
    simpa [prefixWord, tailWord_218528, baseEnd_218528] using wordTrace_append hprefix tailTrace_218528
  have hstable : (prefixWord ++ tailWord_218528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218528).length < 2 ^ (prefixWord ++ tailWord_218528).sum := by decide
  have hdescent : baseEnd_218528 < baseStart_218528 := by decide
  rcases family_descends (prefixWord ++ tailWord_218528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218535 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 5]
def baseStart_218535 : Nat := 118140960795 + 218535 * 2 ^ 59
def prefixEnd_218535 : Nat := 4983230072969 + 3 ^ 40 * 218535 * 2
def baseEnd_218535 : Nat := 99745328738140190673317

theorem tailTrace_218535 : CollatzResearch.WordTrace tailWord_218535 prefixEnd_218535 99745328738140190673317 := by
  unfold tailWord_218535
  simp only [CollatzResearch.WordTrace]
  refine ⟨7970626263292492651689059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5313750842194995101126039 7970626263292492651689059)
  ·
    refine ⟨11955939394938738977533589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7970626263292492651689059 11955939394938738977533589)
    ·
      refine ⟨560434659137753389571887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11955939394938738977533589 560434659137753389571887)
      ·
        refine ⟨840651988706630084357831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560434659137753389571887 840651988706630084357831)
        ·
          refine ⟨1260977983059945126536747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 840651988706630084357831 1260977983059945126536747)
          ·
            refine ⟨1891466974589917689805121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1260977983059945126536747 1891466974589917689805121)
            ·
              refine ⟨1418600230942438267353841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1891466974589917689805121 1418600230942438267353841)
              ·
                refine ⟨1063950173206828700515381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1418600230942438267353841 1063950173206828700515381)
                ·
                  refine ⟨99745328738140190673317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1063950173206828700515381 99745328738140190673317)
                  ·
                    rfl

theorem cell20_218535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_218535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218535 prefixEnd_218535 := by exact prefixLift 218535
  have htrace : WordTrace (prefixWord ++ tailWord_218535) baseStart_218535 baseEnd_218535 := by
    simpa [prefixWord, tailWord_218535, baseEnd_218535] using wordTrace_append hprefix tailTrace_218535
  have hstable : (prefixWord ++ tailWord_218535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218535).length < 2 ^ (prefixWord ++ tailWord_218535).sum := by decide
  have hdescent : baseEnd_218535 < baseStart_218535 := by decide
  rcases family_descends (prefixWord ++ tailWord_218535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218614 : List Nat := [5, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_218614 : Nat := 118140960795 + 218614 * 2 ^ 59
def prefixEnd_218614 : Nat := 4983230072969 + 3 ^ 40 * 218614 * 2
def baseEnd_218614 : Nat := 99781386490767027039661

theorem tailTrace_218614 : CollatzResearch.WordTrace tailWord_218614 prefixEnd_218614 99781386490767027039661 := by
  unfold tailWord_218614
  simp only [CollatzResearch.WordTrace]
  refine ⟨498344226875393071488431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5315671753337526095876597 498344226875393071488431)
  ·
    refine ⟨747516340313089607232647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 498344226875393071488431 747516340313089607232647)
    ·
      refine ⟨1121274510469634410848971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 747516340313089607232647 1121274510469634410848971)
      ·
        refine ⟨1681911765704451616273457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1121274510469634410848971 1681911765704451616273457)
        ·
          refine ⟨1261433824278338712205093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1681911765704451616273457 1261433824278338712205093)
          ·
            refine ⟨236518842052188508538455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1261433824278338712205093 236518842052188508538455)
            ·
              refine ⟨354778263078282762807683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236518842052188508538455 354778263078282762807683)
              ·
                refine ⟨532167394617424144211525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354778263078282762807683 532167394617424144211525)
                ·
                  refine ⟨99781386490767027039661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 532167394617424144211525 99781386490767027039661)
                  ·
                    rfl

theorem cell20_218614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_218614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218614 prefixEnd_218614 := by exact prefixLift 218614
  have htrace : WordTrace (prefixWord ++ tailWord_218614) baseStart_218614 baseEnd_218614 := by
    simpa [prefixWord, tailWord_218614, baseEnd_218614] using wordTrace_append hprefix tailTrace_218614
  have hstable : (prefixWord ++ tailWord_218614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218614).length < 2 ^ (prefixWord ++ tailWord_218614).sum := by decide
  have hdescent : baseEnd_218614 < baseStart_218614 := by decide
  rcases family_descends (prefixWord ++ tailWord_218614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218663 : List Nat := [1, 1, 7, 11]
def baseStart_218663 : Nat := 118140960795 + 218663 * 2 ^ 59
def prefixEnd_218663 : Nat := 4983230072969 + 3 ^ 40 * 218663 * 2
def baseEnd_218663 : Nat := 410715026444200141589

theorem tailTrace_218663 : CollatzResearch.WordTrace tailWord_218663 prefixEnd_218663 410715026444200141589 := by
  unfold tailWord_218663
  simp only [CollatzResearch.WordTrace]
  refine ⟨7975294806828770512348643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5316863204552513674899095 7975294806828770512348643)
  ·
    refine ⟨11962942210243155768522965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7975294806828770512348643 11962942210243155768522965)
    ·
      refine ⟨280381458052573963324757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 11962942210243155768522965 280381458052573963324757)
      ·
        refine ⟨410715026444200141589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 280381458052573963324757 410715026444200141589)
        ·
          rfl

theorem cell20_218663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 11].length) (baseStart_218663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218663 prefixEnd_218663 := by exact prefixLift 218663
  have htrace : WordTrace (prefixWord ++ tailWord_218663) baseStart_218663 baseEnd_218663 := by
    simpa [prefixWord, tailWord_218663, baseEnd_218663] using wordTrace_append hprefix tailTrace_218663
  have hstable : (prefixWord ++ tailWord_218663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218663).length < 2 ^ (prefixWord ++ tailWord_218663).sum := by decide
  have hdescent : baseEnd_218663 < baseStart_218663 := by decide
  rcases family_descends (prefixWord ++ tailWord_218663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218666 : List Nat := [3, 1, 4, 1, 1, 1, 4, 2, 3]
def baseStart_218666 : Nat := 118140960795 + 218666 * 2 ^ 59
def prefixEnd_218666 : Nat := 4983230072969 + 3 ^ 40 * 218666 * 2
def baseEnd_218666 : Nat := 99805120707685957306115

theorem tailTrace_218666 : CollatzResearch.WordTrace tailWord_218666 prefixEnd_218666 99805120707685957306115 := by
  unfold tailWord_218666
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993851056454475506176963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5316936150545268016471901 1993851056454475506176963)
  ·
    refine ⟨2990776584681713259265445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1993851056454475506176963 2990776584681713259265445)
    ·
      refine ⟨560770609627821236112271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2990776584681713259265445 560770609627821236112271)
      ·
        refine ⟨841155914441731854168407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560770609627821236112271 841155914441731854168407)
        ·
          refine ⟨1261733871662597781252611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841155914441731854168407 1261733871662597781252611)
          ·
            refine ⟨1892600807493896671878917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261733871662597781252611 1892600807493896671878917)
            ·
              refine ⟨354862651405105625977297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1892600807493896671878917 354862651405105625977297)
              ·
                refine ⟨266146988553829219482973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354862651405105625977297 266146988553829219482973)
                ·
                  refine ⟨99805120707685957306115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266146988553829219482973 99805120707685957306115)
                  ·
                    rfl

theorem cell20_218666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_218666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218666 prefixEnd_218666 := by exact prefixLift 218666
  have htrace : WordTrace (prefixWord ++ tailWord_218666) baseStart_218666 baseEnd_218666 := by
    simpa [prefixWord, tailWord_218666, baseEnd_218666] using wordTrace_append hprefix tailTrace_218666
  have hstable : (prefixWord ++ tailWord_218666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218666).length < 2 ^ (prefixWord ++ tailWord_218666).sum := by decide
  have hdescent : baseEnd_218666 < baseStart_218666 := by decide
  rcases family_descends (prefixWord ++ tailWord_218666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218680 : List Nat := [2, 1, 2, 1, 4, 4, 1, 5]
def baseStart_218680 : Nat := 118140960795 + 218680 * 2 ^ 59
def prefixEnd_218680 : Nat := 4983230072969 + 3 ^ 40 * 218680 * 2
def baseEnd_218680 : Nat := 33270503563054710279797

theorem tailTrace_218680 : CollatzResearch.WordTrace tailWord_218680 prefixEnd_218680 33270503563054710279797 := by
  unfold tailWord_218680
  simp only [CollatzResearch.WordTrace]
  refine ⟨3987957423883591207858747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5317276565178121610478329 3987957423883591207858747)
  ·
    refine ⟨5981936135825386811788121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3987957423883591207858747 5981936135825386811788121)
    ·
      refine ⟨4486452101869040108841091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5981936135825386811788121 4486452101869040108841091)
      ·
        refine ⟨6729678152803560163261637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4486452101869040108841091 6729678152803560163261637)
        ·
          refine ⟨1261814653650667530611557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6729678152803560163261637 1261814653650667530611557)
          ·
            refine ⟨236590247559500161989667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1261814653650667530611557 236590247559500161989667)
            ·
              refine ⟨354885371339250242984501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236590247559500161989667 354885371339250242984501)
              ·
                refine ⟨33270503563054710279797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 354885371339250242984501 33270503563054710279797)
                ·
                  rfl

theorem cell20_218680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_218680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218680 prefixEnd_218680 := by exact prefixLift 218680
  have htrace : WordTrace (prefixWord ++ tailWord_218680) baseStart_218680 baseEnd_218680 := by
    simpa [prefixWord, tailWord_218680, baseEnd_218680] using wordTrace_append hprefix tailTrace_218680
  have hstable : (prefixWord ++ tailWord_218680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218680).length < 2 ^ (prefixWord ++ tailWord_218680).sum := by decide
  have hdescent : baseEnd_218680 < baseStart_218680 := by decide
  rcases family_descends (prefixWord ++ tailWord_218680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218687 : List Nat := [1, 1, 2, 2, 3, 3, 2, 3, 3]
def baseStart_218687 : Nat := 118140960795 + 218687 * 2 ^ 59
def prefixEnd_218687 : Nat := 4983230072969 + 3 ^ 40 * 218687 * 2
def baseEnd_218687 : Nat := 99814705679903217606029

theorem tailTrace_218687 : CollatzResearch.WordTrace tailWord_218687 prefixEnd_218687 99814705679903217606029 := by
  unfold tailWord_218687
  simp only [CollatzResearch.WordTrace]
  refine ⟨7976170158741822611222315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5317446772494548407481543 7976170158741822611222315)
  ·
    refine ⟨11964255238112733916833473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7976170158741822611222315 11964255238112733916833473)
    ·
      refine ⟨8973191428584550437625105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11964255238112733916833473 8973191428584550437625105)
      ·
        refine ⟨6729893571438412828218829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8973191428584550437625105 6729893571438412828218829)
        ·
          refine ⟨2523710089289404810582061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6729893571438412828218829 2523710089289404810582061)
          ·
            refine ⟨946391283483526803968273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2523710089289404810582061 946391283483526803968273)
            ·
              refine ⟨709793462612645102976205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946391283483526803968273 709793462612645102976205)
              ·
                refine ⟨266172548479741913616077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 709793462612645102976205 266172548479741913616077)
                ·
                  refine ⟨99814705679903217606029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266172548479741913616077 99814705679903217606029)
                  ·
                    rfl

theorem cell20_218687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 3].length) (baseStart_218687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218687 prefixEnd_218687 := by exact prefixLift 218687
  have htrace : WordTrace (prefixWord ++ tailWord_218687) baseStart_218687 baseEnd_218687 := by
    simpa [prefixWord, tailWord_218687, baseEnd_218687] using wordTrace_append hprefix tailTrace_218687
  have hstable : (prefixWord ++ tailWord_218687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218687).length < 2 ^ (prefixWord ++ tailWord_218687).sum := by decide
  have hdescent : baseEnd_218687 < baseStart_218687 := by decide
  rcases family_descends (prefixWord ++ tailWord_218687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218711 : List Nat := [1, 1, 3, 2, 2, 3, 1, 5, 2]
def baseStart_218711 : Nat := 118140960795 + 218711 * 2 ^ 59
def prefixEnd_218711 : Nat := 4983230072969 + 3 ^ 40 * 218711 * 2
def baseEnd_218711 : Nat := 99825659933865800805931

theorem tailTrace_218711 : CollatzResearch.WordTrace tailWord_218711 prefixEnd_218711 99825659933865800805931 := by
  unfold tailWord_218711
  simp only [CollatzResearch.WordTrace]
  refine ⟨7977045510654874710095987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5318030340436583140063991 7977045510654874710095987)
  ·
    refine ⟨11965568265982312065143981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7977045510654874710095987 11965568265982312065143981)
    ·
      refine ⟨4487088099743367024428993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11965568265982312065143981 4487088099743367024428993)
      ·
        refine ⟨3365316074807525268321745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4487088099743367024428993 3365316074807525268321745)
        ·
          refine ⟨2523987056105643951241309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3365316074807525268321745 2523987056105643951241309)
          ·
            refine ⟨946495146039616481715491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2523987056105643951241309 946495146039616481715491)
            ·
              refine ⟨1419742719059424722573237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946495146039616481715491 1419742719059424722573237)
              ·
                refine ⟨133100879911821067741241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1419742719059424722573237 133100879911821067741241)
                ·
                  refine ⟨99825659933865800805931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133100879911821067741241 99825659933865800805931)
                  ·
                    rfl

theorem cell20_218711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 2].length) (baseStart_218711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218711 prefixEnd_218711 := by exact prefixLift 218711
  have htrace : WordTrace (prefixWord ++ tailWord_218711) baseStart_218711 baseEnd_218711 := by
    simpa [prefixWord, tailWord_218711, baseEnd_218711] using wordTrace_append hprefix tailTrace_218711
  have hstable : (prefixWord ++ tailWord_218711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218711).length < 2 ^ (prefixWord ++ tailWord_218711).sum := by decide
  have hdescent : baseEnd_218711 < baseStart_218711 := by decide
  rcases family_descends (prefixWord ++ tailWord_218711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218717 : List Nat := [1, 4, 4, 2, 2, 1, 1, 2, 3]
def baseStart_218717 : Nat := 118140960795 + 218717 * 2 ^ 59
def prefixEnd_218717 : Nat := 4983230072969 + 3 ^ 40 * 218717 * 2
def baseEnd_218717 : Nat := 99828398497356446605907

theorem tailTrace_218717 : CollatzResearch.WordTrace tailWord_218717 prefixEnd_218717 99828398497356446605907 := by
  unfold tailWord_218717
  simp only [CollatzResearch.WordTrace]
  refine ⟨7977264348633137734814405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5318176232422091823209603 7977264348633137734814405)
  ·
    refine ⟨1495737065368713325277701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7977264348633137734814405 1495737065368713325277701)
    ·
      refine ⟨280450699756633748489569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1495737065368713325277701 280450699756633748489569)
      ·
        refine ⟨210338024817475311367177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280450699756633748489569 210338024817475311367177)
        ·
          refine ⟨157753518613106483525383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210338024817475311367177 157753518613106483525383)
          ·
            refine ⟨236630277919659725288075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157753518613106483525383 236630277919659725288075)
            ·
              refine ⟨354945416879489587932113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236630277919659725288075 354945416879489587932113)
              ·
                refine ⟨266209062659617190949085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354945416879489587932113 266209062659617190949085)
                ·
                  refine ⟨99828398497356446605907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266209062659617190949085 99828398497356446605907)
                  ·
                    rfl

theorem cell20_218717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_218717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218717 prefixEnd_218717 := by exact prefixLift 218717
  have htrace : WordTrace (prefixWord ++ tailWord_218717) baseStart_218717 baseEnd_218717 := by
    simpa [prefixWord, tailWord_218717, baseEnd_218717] using wordTrace_append hprefix tailTrace_218717
  have hstable : (prefixWord ++ tailWord_218717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218717).length < 2 ^ (prefixWord ++ tailWord_218717).sum := by decide
  have hdescent : baseEnd_218717 < baseStart_218717 := by decide
  rcases family_descends (prefixWord ++ tailWord_218717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218725 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 5]
def baseStart_218725 : Nat := 118140960795 + 218725 * 2 ^ 59
def prefixEnd_218725 : Nat := 4983230072969 + 3 ^ 40 * 218725 * 2
def baseEnd_218725 : Nat := 99832049915343974339207

theorem tailTrace_218725 : CollatzResearch.WordTrace tailWord_218725 prefixEnd_218725 99832049915343974339207 := by
  unfold tailWord_218725
  simp only [CollatzResearch.WordTrace]
  refine ⟨7977556132604155101105629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5318370755069436734070419 7977556132604155101105629)
  ·
    refine ⟨2991583549726558162914611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7977556132604155101105629 2991583549726558162914611)
    ·
      refine ⟨4487375324589837244371917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2991583549726558162914611 4487375324589837244371917)
      ·
        refine ⟨1682765746721188966639469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4487375324589837244371917 1682765746721188966639469)
        ·
          refine ⟨631037155020445862489801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1682765746721188966639469 631037155020445862489801)
          ·
            refine ⟨473277866265334396867351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 631037155020445862489801 473277866265334396867351)
            ·
              refine ⟨709916799398001595301027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473277866265334396867351 709916799398001595301027)
              ·
                refine ⟨1064875199097002392951541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709916799398001595301027 1064875199097002392951541)
                ·
                  refine ⟨99832049915343974339207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1064875199097002392951541 99832049915343974339207)
                  ·
                    rfl

theorem cell20_218725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_218725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218725 prefixEnd_218725 := by exact prefixLift 218725
  have htrace : WordTrace (prefixWord ++ tailWord_218725) baseStart_218725 baseEnd_218725 := by
    simpa [prefixWord, tailWord_218725, baseEnd_218725] using wordTrace_append hprefix tailTrace_218725
  have hstable : (prefixWord ++ tailWord_218725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218725).length < 2 ^ (prefixWord ++ tailWord_218725).sum := by decide
  have hdescent : baseEnd_218725 < baseStart_218725 := by decide
  rcases family_descends (prefixWord ++ tailWord_218725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218728 : List Nat := [2, 1, 4, 3, 1, 1, 2, 4, 2]
def baseStart_218728 : Nat := 118140960795 + 218728 * 2 ^ 59
def prefixEnd_218728 : Nat := 4983230072969 + 3 ^ 40 * 218728 * 2
def baseEnd_218728 : Nat := 99833419197089297239195

theorem tailTrace_218728 : CollatzResearch.WordTrace tailWord_218728 prefixEnd_218728 99833419197089297239195 := by
  unfold tailWord_218728
  simp only [CollatzResearch.WordTrace]
  refine ⟨3988832775796643306732419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5318443701062191075643225 3988832775796643306732419)
  ·
    refine ⟨5983249163694964960098629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3988832775796643306732419 5983249163694964960098629)
    ·
      refine ⟨1121859218192805930018493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5983249163694964960098629 1121859218192805930018493)
      ·
        refine ⟨420697206822302223756935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1121859218192805930018493 420697206822302223756935)
        ·
          refine ⟨631045810233453335635403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420697206822302223756935 631045810233453335635403)
          ·
            refine ⟨946568715350180003453105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631045810233453335635403 946568715350180003453105)
            ·
              refine ⟨709926536512635002589829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946568715350180003453105 709926536512635002589829)
              ·
                refine ⟨133111225596119062985593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 709926536512635002589829 133111225596119062985593)
                ·
                  refine ⟨99833419197089297239195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133111225596119062985593 99833419197089297239195)
                  ·
                    rfl

theorem cell20_218728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 2].length) (baseStart_218728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218728 prefixEnd_218728 := by exact prefixLift 218728
  have htrace : WordTrace (prefixWord ++ tailWord_218728) baseStart_218728 baseEnd_218728 := by
    simpa [prefixWord, tailWord_218728, baseEnd_218728] using wordTrace_append hprefix tailTrace_218728
  have hstable : (prefixWord ++ tailWord_218728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218728).length < 2 ^ (prefixWord ++ tailWord_218728).sum := by decide
  have hdescent : baseEnd_218728 < baseStart_218728 := by decide
  rcases family_descends (prefixWord ++ tailWord_218728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218756 : List Nat := [2, 3, 2, 1, 4, 1, 1, 6]
def baseStart_218756 : Nat := 118140960795 + 218756 * 2 ^ 59
def prefixEnd_218756 : Nat := 4983230072969 + 3 ^ 40 * 218756 * 2
def baseEnd_218756 : Nat := 33282066386681881435249

theorem tailTrace_218756 : CollatzResearch.WordTrace tailWord_218756 prefixEnd_218756 33282066386681881435249 := by
  unfold tailWord_218756
  simp only [CollatzResearch.WordTrace]
  refine ⟨3989343397745923697742061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5319124530327898263656081 3989343397745923697742061)
  ·
    refine ⟨1496003774154721386653273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3989343397745923697742061 1496003774154721386653273)
    ·
      refine ⟨1122002830616041039989955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1496003774154721386653273 1122002830616041039989955)
      ·
        refine ⟨1683004245924061559984933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1122002830616041039989955 1683004245924061559984933)
        ·
          refine ⟨315563296110761542497175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1683004245924061559984933 315563296110761542497175)
          ·
            refine ⟨473344944166142313745763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315563296110761542497175 473344944166142313745763)
            ·
              refine ⟨710017416249213470618645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473344944166142313745763 710017416249213470618645)
              ·
                refine ⟨33282066386681881435249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 710017416249213470618645 33282066386681881435249)
                ·
                  rfl

theorem cell20_218756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_218756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218756 prefixEnd_218756 := by exact prefixLift 218756
  have htrace : WordTrace (prefixWord ++ tailWord_218756) baseStart_218756 baseEnd_218756 := by
    simpa [prefixWord, tailWord_218756, baseEnd_218756] using wordTrace_append hprefix tailTrace_218756
  have hstable : (prefixWord ++ tailWord_218756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218756).length < 2 ^ (prefixWord ++ tailWord_218756).sum := by decide
  have hdescent : baseEnd_218756 < baseStart_218756 := by decide
  rcases family_descends (prefixWord ++ tailWord_218756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218766 : List Nat := [4, 1, 1, 3, 1, 2, 3, 3, 2]
def baseStart_218766 : Nat := 118140960795 + 218766 * 2 ^ 59
def prefixEnd_218766 : Nat := 4983230072969 + 3 ^ 40 * 218766 * 2
def baseEnd_218766 : Nat := 99850763432530053972373

theorem tailTrace_218766 : CollatzResearch.WordTrace tailWord_218766 prefixEnd_218766 99850763432530053972373 := by
  unfold tailWord_218766
  simp only [CollatzResearch.WordTrace]
  refine ⟨997381440681952387918519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5319367683637079402232101 997381440681952387918519)
  ·
    refine ⟨1496072161022928581877779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 997381440681952387918519 1496072161022928581877779)
    ·
      refine ⟨2244108241534392872816669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1496072161022928581877779 2244108241534392872816669)
      ·
        refine ⟨841540590575397327306251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2244108241534392872816669 841540590575397327306251)
        ·
          refine ⟨1262310885863095990959377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841540590575397327306251 1262310885863095990959377)
          ·
            refine ⟨946733164397321993219533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1262310885863095990959377 946733164397321993219533)
            ·
              refine ⟨355024936648995747457325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 946733164397321993219533 355024936648995747457325)
              ·
                refine ⟨133134351243373405296497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355024936648995747457325 133134351243373405296497)
                ·
                  refine ⟨99850763432530053972373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133134351243373405296497 99850763432530053972373)
                  ·
                    rfl

theorem cell20_218766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_218766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218766 prefixEnd_218766 := by exact prefixLift 218766
  have htrace : WordTrace (prefixWord ++ tailWord_218766) baseStart_218766 baseEnd_218766 := by
    simpa [prefixWord, tailWord_218766, baseEnd_218766] using wordTrace_append hprefix tailTrace_218766
  have hstable : (prefixWord ++ tailWord_218766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218766).length < 2 ^ (prefixWord ++ tailWord_218766).sum := by decide
  have hdescent : baseEnd_218766 < baseStart_218766 := by decide
  rcases family_descends (prefixWord ++ tailWord_218766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218783 : List Nat := [1, 1, 2, 7, 2, 1, 1, 1, 4]
def baseStart_218783 : Nat := 118140960795 + 218783 * 2 ^ 59
def prefixEnd_218783 : Nat := 4983230072969 + 3 ^ 40 * 218783 * 2
def baseEnd_218783 : Nat := 99858522695753550405637

theorem tailTrace_218783 : CollatzResearch.WordTrace tailWord_218783 prefixEnd_218783 99858522695753550405637 := by
  unfold tailWord_218783
  simp only [CollatzResearch.WordTrace]
  refine ⟨7979671566394031006717003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5319781044262687337811335 7979671566394031006717003)
  ·
    refine ⟨11969507349591046510075505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7979671566394031006717003 11969507349591046510075505)
    ·
      refine ⟨8977130512193284882556629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11969507349591046510075505 8977130512193284882556629)
      ·
        refine ⟨210401496379530114434921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 8977130512193284882556629 210401496379530114434921)
        ·
          refine ⟨157801122284647585826191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210401496379530114434921 157801122284647585826191)
          ·
            refine ⟨236701683426971378739287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157801122284647585826191 236701683426971378739287)
            ·
              refine ⟨355052525140457068108931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236701683426971378739287 355052525140457068108931)
              ·
                refine ⟨532578787710685602163397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355052525140457068108931 532578787710685602163397)
                ·
                  refine ⟨99858522695753550405637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 532578787710685602163397 99858522695753550405637)
                  ·
                    rfl

theorem cell20_218783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 4].length) (baseStart_218783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218783 prefixEnd_218783 := by exact prefixLift 218783
  have htrace : WordTrace (prefixWord ++ tailWord_218783) baseStart_218783 baseEnd_218783 := by
    simpa [prefixWord, tailWord_218783, baseEnd_218783] using wordTrace_append hprefix tailTrace_218783
  have hstable : (prefixWord ++ tailWord_218783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218783).length < 2 ^ (prefixWord ++ tailWord_218783).sum := by decide
  have hdescent : baseEnd_218783 < baseStart_218783 := by decide
  rcases family_descends (prefixWord ++ tailWord_218783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218838 : List Nat := [5, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_218838 : Nat := 118140960795 + 218838 * 2 ^ 59
def prefixEnd_218838 : Nat := 4983230072969 + 3 ^ 40 * 218838 * 2
def baseEnd_218838 : Nat := 99883626194417803572079

theorem tailTrace_218838 : CollatzResearch.WordTrace tailWord_218838 prefixEnd_218838 99883626194417803572079 := by
  unfold tailWord_218838
  simp only [CollatzResearch.WordTrace]
  refine ⟨498854848824673462498073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5321118387463183599979445 498854848824673462498073)
  ·
    refine ⟨374141136618505096873555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 498854848824673462498073 374141136618505096873555)
    ·
      refine ⟨561211704927757645310333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374141136618505096873555 561211704927757645310333)
      ·
        refine ⟨210454389347909116991375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 561211704927757645310333 210454389347909116991375)
        ·
          refine ⟨315681584021863675487063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210454389347909116991375 315681584021863675487063)
          ·
            refine ⟨473522376032795513230595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315681584021863675487063 473522376032795513230595)
            ·
              refine ⟨710283564049193269845893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473522376032795513230595 710283564049193269845893)
              ·
                refine ⟨133178168259223738096105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 710283564049193269845893 133178168259223738096105)
                ·
                  refine ⟨99883626194417803572079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133178168259223738096105 99883626194417803572079)
                  ·
                    rfl

theorem cell20_218838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_218838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218838 prefixEnd_218838 := by exact prefixLift 218838
  have htrace : WordTrace (prefixWord ++ tailWord_218838) baseStart_218838 baseEnd_218838 := by
    simpa [prefixWord, tailWord_218838, baseEnd_218838] using wordTrace_append hprefix tailTrace_218838
  have hstable : (prefixWord ++ tailWord_218838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218838).length < 2 ^ (prefixWord ++ tailWord_218838).sum := by decide
  have hdescent : baseEnd_218838 < baseStart_218838 := by decide
  rcases family_descends (prefixWord ++ tailWord_218838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218839 : List Nat := [1, 1, 3, 2, 1, 3, 4, 2, 3]
def baseStart_218839 : Nat := 118140960795 + 218839 * 2 ^ 59
def prefixEnd_218839 : Nat := 4983230072969 + 3 ^ 40 * 218839 * 2
def baseEnd_218839 : Nat := 99884082621666244538741

theorem tailTrace_218839 : CollatzResearch.WordTrace tailWord_218839 prefixEnd_218839 99884082621666244538741 := by
  unfold tailWord_218839
  simp only [CollatzResearch.WordTrace]
  refine ⟨7981714054191152570755571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5321142702794101713837047 7981714054191152570755571)
  ·
    refine ⟨11972571081286728856133357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7981714054191152570755571 11972571081286728856133357)
    ·
      refine ⟨4489714155482523321050009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11972571081286728856133357 4489714155482523321050009)
      ·
        refine ⟨3367285616611892490787507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4489714155482523321050009 3367285616611892490787507)
        ·
          refine ⟨5050928424917838736181261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3367285616611892490787507 5050928424917838736181261)
          ·
            refine ⟨1894098159344189526067973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5050928424917838736181261 1894098159344189526067973)
            ·
              refine ⟨355143404877035536137745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1894098159344189526067973 355143404877035536137745)
              ·
                refine ⟨266357553657776652103309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355143404877035536137745 266357553657776652103309)
                ·
                  refine ⟨99884082621666244538741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266357553657776652103309 99884082621666244538741)
                  ·
                    rfl

theorem cell20_218839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 3].length) (baseStart_218839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218839 prefixEnd_218839 := by exact prefixLift 218839
  have htrace : WordTrace (prefixWord ++ tailWord_218839) baseStart_218839 baseEnd_218839 := by
    simpa [prefixWord, tailWord_218839, baseEnd_218839] using wordTrace_append hprefix tailTrace_218839
  have hstable : (prefixWord ++ tailWord_218839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218839).length < 2 ^ (prefixWord ++ tailWord_218839).sum := by decide
  have hdescent : baseEnd_218839 < baseStart_218839 := by decide
  rcases family_descends (prefixWord ++ tailWord_218839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218842 : List Nat := [3, 1, 1, 2, 2, 3, 4, 2, 2]
def baseStart_218842 : Nat := 118140960795 + 218842 * 2 ^ 59
def prefixEnd_218842 : Nat := 4983230072969 + 3 ^ 40 * 218842 * 2
def baseEnd_218842 : Nat := 99885451903411567438729

theorem tailTrace_218842 : CollatzResearch.WordTrace tailWord_218842 prefixEnd_218842 99885451903411567438729 := by
  unfold tailWord_218842
  simp only [CollatzResearch.WordTrace]
  refine ⟨1995455868295071020778695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5321215648786856055409853 1995455868295071020778695)
  ·
    refine ⟨2993183802442606531168043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1995455868295071020778695 2993183802442606531168043)
    ·
      refine ⟨4489775703663909796752065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2993183802442606531168043 4489775703663909796752065)
      ·
        refine ⟨3367331777747932347564049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4489775703663909796752065 3367331777747932347564049)
        ·
          refine ⟨2525498833310949260673037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3367331777747932347564049 2525498833310949260673037)
          ·
            refine ⟨947062062491605972752389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2525498833310949260673037 947062062491605972752389)
            ·
              refine ⟨177574136717176119891073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 947062062491605972752389 177574136717176119891073)
              ·
                refine ⟨133180602537882089918305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177574136717176119891073 133180602537882089918305)
                ·
                  refine ⟨99885451903411567438729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133180602537882089918305 99885451903411567438729)
                  ·
                    rfl

theorem cell20_218842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_218842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218842 prefixEnd_218842 := by exact prefixLift 218842
  have htrace : WordTrace (prefixWord ++ tailWord_218842) baseStart_218842 baseEnd_218842 := by
    simpa [prefixWord, tailWord_218842, baseEnd_218842] using wordTrace_append hprefix tailTrace_218842
  have hstable : (prefixWord ++ tailWord_218842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218842).length < 2 ^ (prefixWord ++ tailWord_218842).sum := by decide
  have hdescent : baseEnd_218842 < baseStart_218842 := by decide
  rcases family_descends (prefixWord ++ tailWord_218842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218849 : List Nat := [1, 2, 3, 1, 6, 1, 1, 5]
def baseStart_218849 : Nat := 118140960795 + 218849 * 2 ^ 59
def prefixEnd_218849 : Nat := 4983230072969 + 3 ^ 40 * 218849 * 2
def baseEnd_218849 : Nat := 33296215631383551401789

theorem tailTrace_218849 : CollatzResearch.WordTrace tailWord_218849 prefixEnd_218849 33296215631383551401789 := by
  unfold tailWord_218849
  simp only [CollatzResearch.WordTrace]
  refine ⟨7982078784154924278619601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5321385856103282852413067 7982078784154924278619601)
  ·
    refine ⟨5986559088116193208964701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7982078784154924278619601 5986559088116193208964701)
    ·
      refine ⟨2244959658043572453361763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5986559088116193208964701 2244959658043572453361763)
      ·
        refine ⟨3367439487065358680042645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2244959658043572453361763 3367439487065358680042645)
        ·
          refine ⟨157848725956188688126999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3367439487065358680042645 157848725956188688126999)
          ·
            refine ⟨236773088934283032190499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157848725956188688126999 236773088934283032190499)
            ·
              refine ⟨355159633401424548285749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236773088934283032190499 355159633401424548285749)
              ·
                refine ⟨33296215631383551401789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 355159633401424548285749 33296215631383551401789)
                ·
                  rfl

theorem cell20_218849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 5].length) (baseStart_218849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218849 prefixEnd_218849 := by exact prefixLift 218849
  have htrace : WordTrace (prefixWord ++ tailWord_218849) baseStart_218849 baseEnd_218849 := by
    simpa [prefixWord, tailWord_218849, baseEnd_218849] using wordTrace_append hprefix tailTrace_218849
  have hstable : (prefixWord ++ tailWord_218849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218849).length < 2 ^ (prefixWord ++ tailWord_218849).sum := by decide
  have hdescent : baseEnd_218849 < baseStart_218849 := by decide
  rcases family_descends (prefixWord ++ tailWord_218849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218867 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 6]
def baseStart_218867 : Nat := 118140960795 + 218867 * 2 ^ 59
def prefixEnd_218867 : Nat := 4983230072969 + 3 ^ 40 * 218867 * 2
def baseEnd_218867 : Nat := 99896862584622591605293

theorem tailTrace_218867 : CollatzResearch.WordTrace tailWord_218867 prefixEnd_218867 99896862584622591605293 := by
  unfold tailWord_218867
  simp only [CollatzResearch.WordTrace]
  refine ⟨7982735298089713352774855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5321823532059808901849903 7982735298089713352774855)
  ·
    refine ⟨11974102947134570029162283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7982735298089713352774855 11974102947134570029162283)
    ·
      refine ⟨17961154420701855043743425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11974102947134570029162283 17961154420701855043743425)
      ·
        refine ⟨13470865815526391282807569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17961154420701855043743425 13470865815526391282807569)
        ·
          refine ⟨10103149361644793462105677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13470865815526391282807569 10103149361644793462105677)
          ·
            refine ⟨3788681010616797548289629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10103149361644793462105677 3788681010616797548289629)
            ·
              refine ⟨1420755378981299080608611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3788681010616797548289629 1420755378981299080608611)
              ·
                refine ⟨2131133068471948620912917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1420755378981299080608611 2131133068471948620912917)
                ·
                  refine ⟨99896862584622591605293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2131133068471948620912917 99896862584622591605293)
                  ·
                    rfl

theorem cell20_218867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_218867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218867 prefixEnd_218867 := by exact prefixLift 218867
  have htrace : WordTrace (prefixWord ++ tailWord_218867) baseStart_218867 baseEnd_218867 := by
    simpa [prefixWord, tailWord_218867, baseEnd_218867] using wordTrace_append hprefix tailTrace_218867
  have hstable : (prefixWord ++ tailWord_218867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218867).length < 2 ^ (prefixWord ++ tailWord_218867).sum := by decide
  have hdescent : baseEnd_218867 < baseStart_218867 := by decide
  rcases family_descends (prefixWord ++ tailWord_218867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218901 : List Nat := [1, 3, 2, 1, 2, 3, 2, 4, 2]
def baseStart_218901 : Nat := 118140960795 + 218901 * 2 ^ 59
def prefixEnd_218901 : Nat := 4983230072969 + 3 ^ 40 * 218901 * 2
def baseEnd_218901 : Nat := 99912381111069584471821

theorem tailTrace_218901 : CollatzResearch.WordTrace tailWord_218901 prefixEnd_218901 99912381111069584471821 := by
  unfold tailWord_218901
  simp only [CollatzResearch.WordTrace]
  refine ⟨7983975379966537159512557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5322650253311024773008371 7983975379966537159512557)
  ·
    refine ⟨2993990767487451434817209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7983975379966537159512557 2993990767487451434817209)
    ·
      refine ⟨2245493075615588576112907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2993990767487451434817209 2245493075615588576112907)
      ·
        refine ⟨3368239613423382864169361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2245493075615588576112907 3368239613423382864169361)
        ·
          refine ⟨2526179710067537148127021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3368239613423382864169361 2526179710067537148127021)
          ·
            refine ⟨947317391275326430547633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2526179710067537148127021 947317391275326430547633)
            ·
              refine ⟨710488043456494822910725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 947317391275326430547633 710488043456494822910725)
              ·
                refine ⟨133216508148092779295761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 710488043456494822910725 133216508148092779295761)
                ·
                  refine ⟨99912381111069584471821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133216508148092779295761 99912381111069584471821)
                  ·
                    rfl

theorem cell20_218901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_218901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218901 prefixEnd_218901 := by exact prefixLift 218901
  have htrace : WordTrace (prefixWord ++ tailWord_218901) baseStart_218901 baseEnd_218901 := by
    simpa [prefixWord, tailWord_218901, baseEnd_218901] using wordTrace_append hprefix tailTrace_218901
  have hstable : (prefixWord ++ tailWord_218901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218901).length < 2 ^ (prefixWord ++ tailWord_218901).sum := by decide
  have hdescent : baseEnd_218901 < baseStart_218901 := by decide
  rcases family_descends (prefixWord ++ tailWord_218901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218929 : List Nat := [1, 2, 2, 3, 2, 3, 1, 6]
def baseStart_218929 : Nat := 118140960795 + 218929 * 2 ^ 59
def prefixEnd_218929 : Nat := 4983230072969 + 3 ^ 40 * 218929 * 2
def baseEnd_218929 : Nat := 33308387024675310512791

theorem tailTrace_218929 : CollatzResearch.WordTrace tailWord_218929 prefixEnd_218929 33308387024675310512791 := by
  unfold tailWord_218929
  simp only [CollatzResearch.WordTrace]
  refine ⟨7984996623865097941531841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5323331082576731961021227 7984996623865097941531841)
  ·
    refine ⟨5988747467898823456148881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7984996623865097941531841 5988747467898823456148881)
    ·
      refine ⟨4491560600924117592111661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5988747467898823456148881 4491560600924117592111661)
      ·
        refine ⟨1684335225346544097041873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4491560600924117592111661 1684335225346544097041873)
        ·
          refine ⟨1263251419009908072781405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1684335225346544097041873 1263251419009908072781405)
          ·
            refine ⟨473719282128715527293027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1263251419009908072781405 473719282128715527293027)
            ·
              refine ⟨710578923193073290939541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473719282128715527293027 710578923193073290939541)
              ·
                refine ⟨33308387024675310512791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 710578923193073290939541 33308387024675310512791)
                ·
                  rfl

theorem cell20_218929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 6].length) (baseStart_218929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218929 prefixEnd_218929 := by exact prefixLift 218929
  have htrace : WordTrace (prefixWord ++ tailWord_218929) baseStart_218929 baseEnd_218929 := by
    simpa [prefixWord, tailWord_218929, baseEnd_218929] using wordTrace_append hprefix tailTrace_218929
  have hstable : (prefixWord ++ tailWord_218929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218929).length < 2 ^ (prefixWord ++ tailWord_218929).sum := by decide
  have hdescent : baseEnd_218929 < baseStart_218929 := by decide
  rcases family_descends (prefixWord ++ tailWord_218929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218936 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 5]
def baseStart_218936 : Nat := 118140960795 + 218936 * 2 ^ 59
def prefixEnd_218936 : Nat := 4983230072969 + 3 ^ 40 * 218936 * 2
def baseEnd_218936 : Nat := 99928356064765018305011

theorem tailTrace_218936 : CollatzResearch.WordTrace tailWord_218936 prefixEnd_218936 99928356064765018305011 := by
  unfold tailWord_218936
  simp only [CollatzResearch.WordTrace]
  refine ⟨3992625967419869068518331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5323501289893158758024441 3992625967419869068518331)
  ·
    refine ⟨5988938951129803602777497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3992625967419869068518331 5988938951129803602777497)
    ·
      refine ⟨4491704213347352702083123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5988938951129803602777497 4491704213347352702083123)
      ·
        refine ⟨6737556320021029053124685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4491704213347352702083123 6737556320021029053124685)
        ·
          refine ⟨2526583620007885894921757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6737556320021029053124685 2526583620007885894921757)
          ·
            refine ⟨947468857502957210595659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2526583620007885894921757 947468857502957210595659)
            ·
              refine ⟨1421203286254435815893489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947468857502957210595659 1421203286254435815893489)
              ·
                refine ⟨1065902464690826861920117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1421203286254435815893489 1065902464690826861920117)
                ·
                  refine ⟨99928356064765018305011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1065902464690826861920117 99928356064765018305011)
                  ·
                    rfl

theorem cell20_218936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_218936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218936 prefixEnd_218936 := by exact prefixLift 218936
  have htrace : WordTrace (prefixWord ++ tailWord_218936) baseStart_218936 baseEnd_218936 := by
    simpa [prefixWord, tailWord_218936, baseEnd_218936] using wordTrace_append hprefix tailTrace_218936
  have hstable : (prefixWord ++ tailWord_218936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218936).length < 2 ^ (prefixWord ++ tailWord_218936).sum := by decide
  have hdescent : baseEnd_218936 < baseStart_218936 := by decide
  rcases family_descends (prefixWord ++ tailWord_218936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218956 : List Nat := [2, 2, 1, 3, 5, 1, 1, 1, 4]
def baseStart_218956 : Nat := 118140960795 + 218956 * 2 ^ 59
def prefixEnd_218956 : Nat := 4983230072969 + 3 ^ 40 * 218956 * 2
def baseEnd_218956 : Nat := 99937484609733837638263

theorem tailTrace_218956 : CollatzResearch.WordTrace tailWord_218956 prefixEnd_218956 99937484609733837638263 := by
  unfold tailWord_218956
  simp only [CollatzResearch.WordTrace]
  refine ⟨3992990697383640776382361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5323987596511521035176481 3992990697383640776382361)
  ·
    refine ⟨2994743023037730582286771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3992990697383640776382361 2994743023037730582286771)
    ·
      refine ⟨4492114534556595873430157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2994743023037730582286771 4492114534556595873430157)
      ·
        refine ⟨1684542950458723452536309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4492114534556595873430157 1684542950458723452536309)
        ·
          refine ⟨157925901605505323675279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1684542950458723452536309 157925901605505323675279)
          ·
            refine ⟨236888852408257985512919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157925901605505323675279 236888852408257985512919)
            ·
              refine ⟨355333278612386978269379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236888852408257985512919 355333278612386978269379)
              ·
                refine ⟨532999917918580467404069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355333278612386978269379 532999917918580467404069)
                ·
                  refine ⟨99937484609733837638263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 532999917918580467404069 99937484609733837638263)
                  ·
                    rfl

theorem cell20_218956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_218956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218956 prefixEnd_218956 := by exact prefixLift 218956
  have htrace : WordTrace (prefixWord ++ tailWord_218956) baseStart_218956 baseEnd_218956 := by
    simpa [prefixWord, tailWord_218956, baseEnd_218956] using wordTrace_append hprefix tailTrace_218956
  have hstable : (prefixWord ++ tailWord_218956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218956).length < 2 ^ (prefixWord ++ tailWord_218956).sum := by decide
  have hdescent : baseEnd_218956 < baseStart_218956 := by decide
  rcases family_descends (prefixWord ++ tailWord_218956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218981 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 6]
def baseStart_218981 : Nat := 118140960795 + 218981 * 2 ^ 59
def prefixEnd_218981 : Nat := 4983230072969 + 3 ^ 40 * 218981 * 2
def baseEnd_218981 : Nat := 99948895290944861804827

theorem tailTrace_218981 : CollatzResearch.WordTrace tailWord_218981 prefixEnd_218981 99948895290944861804827 := by
  unfold tailWord_218981
  simp only [CollatzResearch.WordTrace]
  refine ⟨7986893219676710822424797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5324595479784473881616531 7986893219676710822424797)
  ·
    refine ⟨2995084957378766558409299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7986893219676710822424797 2995084957378766558409299)
    ·
      refine ⟨4492627436068149837613949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2995084957378766558409299 4492627436068149837613949)
      ·
        refine ⟨1684735288525556189105231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4492627436068149837613949 1684735288525556189105231)
        ·
          refine ⟨2527102932788334283657847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1684735288525556189105231 2527102932788334283657847)
          ·
            refine ⟨3790654399182501425486771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2527102932788334283657847 3790654399182501425486771)
            ·
              refine ⟨5685981598773752138230157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3790654399182501425486771 5685981598773752138230157)
              ·
                refine ⟨2132243099540157051836309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5685981598773752138230157 2132243099540157051836309)
                ·
                  refine ⟨99948895290944861804827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2132243099540157051836309 99948895290944861804827)
                  ·
                    rfl

theorem cell20_218981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_218981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_218981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_218981 prefixEnd_218981 := by exact prefixLift 218981
  have htrace : WordTrace (prefixWord ++ tailWord_218981) baseStart_218981 baseEnd_218981 := by
    simpa [prefixWord, tailWord_218981, baseEnd_218981] using wordTrace_append hprefix tailTrace_218981
  have hstable : (prefixWord ++ tailWord_218981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218981).length < 2 ^ (prefixWord ++ tailWord_218981).sum := by decide
  have hdescent : baseEnd_218981 < baseStart_218981 := by decide
  rcases family_descends (prefixWord ++ tailWord_218981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219012 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 5]
def baseStart_219012 : Nat := 118140960795 + 219012 * 2 ^ 59
def prefixEnd_219012 : Nat := 4983230072969 + 3 ^ 40 * 219012 * 2
def baseEnd_219012 : Nat := 99963044535646531771367

theorem tailTrace_219012 : CollatzResearch.WordTrace tailWord_219012 prefixEnd_219012 99963044535646531771367 := by
  unfold tailWord_219012
  simp only [CollatzResearch.WordTrace]
  refine ⟨3994011941282201558401645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5325349255042935411202193 3994011941282201558401645)
  ·
    refine ⟨1497754477980825584400617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3994011941282201558401645 1497754477980825584400617)
    ·
      refine ⟨1123315858485619188300463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1497754477980825584400617 1123315858485619188300463)
      ·
        refine ⟨1684973787728428782450695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1123315858485619188300463 1684973787728428782450695)
        ·
          refine ⟨2527460681592643173676043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1684973787728428782450695 2527460681592643173676043)
          ·
            refine ⟨3791191022388964760514065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2527460681592643173676043 3791191022388964760514065)
            ·
              refine ⟨2843393266791723570385549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3791191022388964760514065 2843393266791723570385549)
              ·
                refine ⟨1066272475046896338894581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2843393266791723570385549 1066272475046896338894581)
                ·
                  refine ⟨99963044535646531771367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1066272475046896338894581 99963044535646531771367)
                  ·
                    rfl

theorem cell20_219012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_219012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219012 prefixEnd_219012 := by exact prefixLift 219012
  have htrace : WordTrace (prefixWord ++ tailWord_219012) baseStart_219012 baseEnd_219012 := by
    simpa [prefixWord, tailWord_219012, baseEnd_219012] using wordTrace_append hprefix tailTrace_219012
  have hstable : (prefixWord ++ tailWord_219012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219012).length < 2 ^ (prefixWord ++ tailWord_219012).sum := by decide
  have hdescent : baseEnd_219012 < baseStart_219012 := by decide
  rcases family_descends (prefixWord ++ tailWord_219012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219019 : List Nat := [1, 1, 1, 1, 4, 2, 1, 5, 4]
def baseStart_219019 : Nat := 118140960795 + 219019 * 2 ^ 59
def prefixEnd_219019 : Nat := 4983230072969 + 3 ^ 40 * 219019 * 2
def baseEnd_219019 : Nat := 99966239526385618538005

theorem tailTrace_219019 : CollatzResearch.WordTrace tailWord_219019 prefixEnd_219019 99966239526385618538005 := by
  unfold tailWord_219019
  simp only [CollatzResearch.WordTrace]
  refine ⟨7988279193539043312308111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5325519462359362208205407 7988279193539043312308111)
  ·
    refine ⟨11982418790308564968462167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7988279193539043312308111 11982418790308564968462167)
    ·
      refine ⟨17973628185462847452693251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11982418790308564968462167 17973628185462847452693251)
      ·
        refine ⟨26960442278194271179039877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17973628185462847452693251 26960442278194271179039877)
        ·
          refine ⟨5055082927161425846069977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26960442278194271179039877 5055082927161425846069977)
          ·
            refine ⟨3791312195371069384552483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5055082927161425846069977 3791312195371069384552483)
            ·
              refine ⟨5686968293056604076828725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3791312195371069384552483 5686968293056604076828725)
              ·
                refine ⟨533153277474056632202693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5686968293056604076828725 533153277474056632202693)
                ·
                  refine ⟨99966239526385618538005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 533153277474056632202693 99966239526385618538005)
                  ·
                    rfl

theorem cell20_219019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_219019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219019 prefixEnd_219019 := by exact prefixLift 219019
  have htrace : WordTrace (prefixWord ++ tailWord_219019) baseStart_219019 baseEnd_219019 := by
    simpa [prefixWord, tailWord_219019, baseEnd_219019] using wordTrace_append hprefix tailTrace_219019
  have hstable : (prefixWord ++ tailWord_219019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219019).length < 2 ^ (prefixWord ++ tailWord_219019).sum := by decide
  have hdescent : baseEnd_219019 < baseStart_219019 := by decide
  rcases family_descends (prefixWord ++ tailWord_219019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219036 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 6]
def baseStart_219036 : Nat := 118140960795 + 219036 * 2 ^ 59
def prefixEnd_219036 : Nat := 4983230072969 + 3 ^ 40 * 219036 * 2
def baseEnd_219036 : Nat := 99973998789609114971269

theorem tailTrace_219036 : CollatzResearch.WordTrace tailWord_219036 prefixEnd_219036 99973998789609114971269 := by
  unfold tailWord_219036
  simp only [CollatzResearch.WordTrace]
  refine ⟨3994449617238727607838481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5325932822984970143784641 3994449617238727607838481)
  ·
    refine ⟨2995837212929045705878861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3994449617238727607838481 2995837212929045705878861)
    ·
      refine ⟨1123438954848392139704573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2995837212929045705878861 1123438954848392139704573)
      ·
        refine ⟨421289608068147052389215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1123438954848392139704573 421289608068147052389215)
        ·
          refine ⟨631934412102220578583823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421289608068147052389215 631934412102220578583823)
          ·
            refine ⟨947901618153330867875735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631934412102220578583823 947901618153330867875735)
            ·
              refine ⟨1421852427229996301813603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947901618153330867875735 1421852427229996301813603)
              ·
                refine ⟨2132778640844994452720405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421852427229996301813603 2132778640844994452720405)
                ·
                  refine ⟨99973998789609114971269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2132778640844994452720405 99973998789609114971269)
                  ·
                    rfl

theorem cell20_219036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_219036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219036 prefixEnd_219036 := by exact prefixLift 219036
  have htrace : WordTrace (prefixWord ++ tailWord_219036) baseStart_219036 baseEnd_219036 := by
    simpa [prefixWord, tailWord_219036, baseEnd_219036] using wordTrace_append hprefix tailTrace_219036
  have hstable : (prefixWord ++ tailWord_219036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219036).length < 2 ^ (prefixWord ++ tailWord_219036).sum := by decide
  have hdescent : baseEnd_219036 < baseStart_219036 := by decide
  rcases family_descends (prefixWord ++ tailWord_219036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219064 : List Nat := [2, 1, 2, 1, 2, 3, 9]
def baseStart_219064 : Nat := 118140960795 + 219064 * 2 ^ 59
def prefixEnd_219064 : Nat := 4983230072969 + 3 ^ 40 * 219064 * 2
def baseEnd_219064 : Nat := 11109642083618384670869

theorem tailTrace_219064 : CollatzResearch.WordTrace tailWord_219064 prefixEnd_219064 11109642083618384670869 := by
  unfold tailWord_219064
  simp only [CollatzResearch.WordTrace]
  refine ⟨3994960239188007998848123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5326613652250677331797497 3994960239188007998848123)
  ·
    refine ⟨5992440358782011998272185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3994960239188007998848123 5992440358782011998272185)
    ·
      refine ⟨4494330269086508998704139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5992440358782011998272185 4494330269086508998704139)
      ·
        refine ⟨6741495403629763498056209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4494330269086508998704139 6741495403629763498056209)
        ·
          refine ⟨5056121552722322623542157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6741495403629763498056209 5056121552722322623542157)
          ·
            refine ⟨1896045582270870983828309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5056121552722322623542157 1896045582270870983828309)
            ·
              refine ⟨11109642083618384670869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1896045582270870983828309 11109642083618384670869)
              ·
                rfl

theorem cell20_219064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 9].length) (baseStart_219064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219064 prefixEnd_219064 := by exact prefixLift 219064
  have htrace : WordTrace (prefixWord ++ tailWord_219064) baseStart_219064 baseEnd_219064 := by
    simpa [prefixWord, tailWord_219064, baseEnd_219064] using wordTrace_append hprefix tailTrace_219064
  have hstable : (prefixWord ++ tailWord_219064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219064).length < 2 ^ (prefixWord ++ tailWord_219064).sum := by decide
  have hdescent : baseEnd_219064 < baseStart_219064 := by decide
  rcases family_descends (prefixWord ++ tailWord_219064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219084 : List Nat := [2, 2, 1, 4, 1, 3, 3, 1, 3]
def baseStart_219084 : Nat := 118140960795 + 219084 * 2 ^ 59
def prefixEnd_219084 : Nat := 4983230072969 + 3 ^ 40 * 219084 * 2
def baseEnd_219084 : Nat := 99995907297534281371073

theorem tailTrace_219084 : CollatzResearch.WordTrace tailWord_219084 prefixEnd_219084 99995907297534281371073 := by
  unfold tailWord_219084
  simp only [CollatzResearch.WordTrace]
  refine ⟨3995324969151779706712153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5327099958869039608949537 3995324969151779706712153)
  ·
    refine ⟨2996493726863834780034115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3995324969151779706712153 2996493726863834780034115)
    ·
      refine ⟨4494740590295752170051173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2996493726863834780034115 4494740590295752170051173)
      ·
        refine ⟨842763860680453531884595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4494740590295752170051173 842763860680453531884595)
        ·
          refine ⟨1264145791020680297826893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842763860680453531884595 1264145791020680297826893)
          ·
            refine ⟨474054671632755111685085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1264145791020680297826893 474054671632755111685085)
            ·
              refine ⟨177770501862283166881907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 474054671632755111685085 177770501862283166881907)
              ·
                refine ⟨266655752793424750322861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177770501862283166881907 266655752793424750322861)
                ·
                  refine ⟨99995907297534281371073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266655752793424750322861 99995907297534281371073)
                  ·
                    rfl

theorem cell20_219084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_219084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219084 prefixEnd_219084 := by exact prefixLift 219084
  have htrace : WordTrace (prefixWord ++ tailWord_219084) baseStart_219084 baseEnd_219084 := by
    simpa [prefixWord, tailWord_219084, baseEnd_219084] using wordTrace_append hprefix tailTrace_219084
  have hstable : (prefixWord ++ tailWord_219084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219084).length < 2 ^ (prefixWord ++ tailWord_219084).sum := by decide
  have hdescent : baseEnd_219084 < baseStart_219084 := by decide
  rcases family_descends (prefixWord ++ tailWord_219084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219088 : List Nat := [2, 1, 1, 1, 1, 2, 4, 5, 3]
def baseStart_219088 : Nat := 118140960795 + 219088 * 2 ^ 59
def prefixEnd_219088 : Nat := 4983230072969 + 3 ^ 40 * 219088 * 2
def baseEnd_219088 : Nat := 99997733006528045237723

theorem tailTrace_219088 : CollatzResearch.WordTrace tailWord_219088 prefixEnd_219088 99997733006528045237723 := by
  unfold tailWord_219088
  simp only [CollatzResearch.WordTrace]
  refine ⟨3995397915144534048284959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5327197220192712064379945 3995397915144534048284959)
  ·
    refine ⟨5993096872716801072427439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3995397915144534048284959 5993096872716801072427439)
    ·
      refine ⟨8989645309075201608641159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5993096872716801072427439 8989645309075201608641159)
      ·
        refine ⟨13484467963612802412961739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8989645309075201608641159 13484467963612802412961739)
        ·
          refine ⟨20226701945419203619442609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13484467963612802412961739 20226701945419203619442609)
          ·
            refine ⟨15170026459064402714581957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20226701945419203619442609 15170026459064402714581957)
            ·
              refine ⟨2844379961074575508984117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15170026459064402714581957 2844379961074575508984117)
              ·
                refine ⟨266660621350741453967261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2844379961074575508984117 266660621350741453967261)
                ·
                  refine ⟨99997733006528045237723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266660621350741453967261 99997733006528045237723)
                  ·
                    rfl

theorem cell20_219088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_219088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219088 prefixEnd_219088 := by exact prefixLift 219088
  have htrace : WordTrace (prefixWord ++ tailWord_219088) baseStart_219088 baseEnd_219088 := by
    simpa [prefixWord, tailWord_219088, baseEnd_219088] using wordTrace_append hprefix tailTrace_219088
  have hstable : (prefixWord ++ tailWord_219088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219088).length < 2 ^ (prefixWord ++ tailWord_219088).sum := by decide
  have hdescent : baseEnd_219088 < baseStart_219088 := by decide
  rcases family_descends (prefixWord ++ tailWord_219088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219094 : List Nat := [5, 2, 1, 1, 3, 2, 2, 4]
def baseStart_219094 : Nat := 118140960795 + 219094 * 2 ^ 59
def prefixEnd_219094 : Nat := 4983230072969 + 3 ^ 40 * 219094 * 2
def baseEnd_219094 : Nat := 33333490523339563679233

theorem tailTrace_219094 : CollatzResearch.WordTrace tailWord_219094 prefixEnd_219094 33333490523339563679233 := by
  unfold tailWord_219094
  simp only [CollatzResearch.WordTrace]
  refine ⟨499438416766708195080521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5327343112178220747525557 499438416766708195080521)
  ·
    refine ⟨374578812575031146310391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 499438416766708195080521 374578812575031146310391)
    ·
      refine ⟨561868218862546719465587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374578812575031146310391 561868218862546719465587)
      ·
        refine ⟨842802328293820079198381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561868218862546719465587 842802328293820079198381)
        ·
          refine ⟨316050873110182529699393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 842802328293820079198381 316050873110182529699393)
          ·
            refine ⟨237038154832636897274545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316050873110182529699393 237038154832636897274545)
            ·
              refine ⟨177778616124477672955909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237038154832636897274545 177778616124477672955909)
              ·
                refine ⟨33333490523339563679233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177778616124477672955909 33333490523339563679233)
                ·
                  rfl

theorem cell20_219094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_219094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219094 prefixEnd_219094 := by exact prefixLift 219094
  have htrace : WordTrace (prefixWord ++ tailWord_219094) baseStart_219094 baseEnd_219094 := by
    simpa [prefixWord, tailWord_219094, baseEnd_219094] using wordTrace_append hprefix tailTrace_219094
  have hstable : (prefixWord ++ tailWord_219094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219094).length < 2 ^ (prefixWord ++ tailWord_219094).sum := by decide
  have hdescent : baseEnd_219094 < baseStart_219094 := by decide
  rcases family_descends (prefixWord ++ tailWord_219094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219095 : List Nat := [1, 1, 3, 2, 1, 1, 3, 4, 4]
def baseStart_219095 : Nat := 118140960795 + 219095 * 2 ^ 59
def prefixEnd_219095 : Nat := 4983230072969 + 3 ^ 40 * 219095 * 2
def baseEnd_219095 : Nat := 100000927997267132004361

theorem tailTrace_219095 : CollatzResearch.WordTrace tailWord_219095 prefixEnd_219095 100000927997267132004361 := by
  unfold tailWord_219095
  simp only [CollatzResearch.WordTrace]
  refine ⟨7991051141263708292074739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5327367427509138861383159 7991051141263708292074739)
  ·
    refine ⟨11986576711895562438112109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7991051141263708292074739 11986576711895562438112109)
    ·
      refine ⟨4494966266960835914292041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11986576711895562438112109 4494966266960835914292041)
      ·
        refine ⟨3371224700220626935719031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4494966266960835914292041 3371224700220626935719031)
        ·
          refine ⟨5056837050330940403578547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3371224700220626935719031 5056837050330940403578547)
          ·
            refine ⟨7585255575496410605367821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5056837050330940403578547 7585255575496410605367821)
            ·
              refine ⟨2844470840811153977012933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7585255575496410605367821 2844470840811153977012933)
              ·
                refine ⟨533338282652091370689925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2844470840811153977012933 533338282652091370689925)
                ·
                  refine ⟨100000927997267132004361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 533338282652091370689925 100000927997267132004361)
                  ·
                    rfl

theorem cell20_219095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_219095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219095 prefixEnd_219095 := by exact prefixLift 219095
  have htrace : WordTrace (prefixWord ++ tailWord_219095) baseStart_219095 baseEnd_219095 := by
    simpa [prefixWord, tailWord_219095, baseEnd_219095] using wordTrace_append hprefix tailTrace_219095
  have hstable : (prefixWord ++ tailWord_219095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219095).length < 2 ^ (prefixWord ++ tailWord_219095).sum := by decide
  have hdescent : baseEnd_219095 < baseStart_219095 := by decide
  rcases family_descends (prefixWord ++ tailWord_219095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219143 : List Nat := [1, 1, 4, 3, 1, 3, 1, 3, 3]
def baseStart_219143 : Nat := 118140960795 + 219143 * 2 ^ 59
def prefixEnd_219143 : Nat := 4983230072969 + 3 ^ 40 * 219143 * 2
def baseEnd_219143 : Nat := 100022836505192298404165

theorem tailTrace_219143 : CollatzResearch.WordTrace tailWord_219143 prefixEnd_219143 100022836505192298404165 := by
  unfold tailWord_219143
  simp only [CollatzResearch.WordTrace]
  refine ⟨7992801845089812489822083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5328534563393208326548055 7992801845089812489822083)
  ·
    refine ⟨11989202767634718734733125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7992801845089812489822083 11989202767634718734733125)
    ·
      refine ⟨2247975518931509762762461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11989202767634718734733125 2247975518931509762762461)
      ·
        refine ⟨842990819599316161035923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2247975518931509762762461 842990819599316161035923)
        ·
          refine ⟨1264486229398974241553885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842990819599316161035923 1264486229398974241553885)
          ·
            refine ⟨474182336024615340582707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1264486229398974241553885 474182336024615340582707)
            ·
              refine ⟨711273504036923010874061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474182336024615340582707 711273504036923010874061)
              ·
                refine ⟨266727564013846129077773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 711273504036923010874061 266727564013846129077773)
                ·
                  refine ⟨100022836505192298404165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266727564013846129077773 100022836505192298404165)
                  ·
                    rfl

theorem cell20_219143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 3].length) (baseStart_219143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219143 prefixEnd_219143 := by exact prefixLift 219143
  have htrace : WordTrace (prefixWord ++ tailWord_219143) baseStart_219143 baseEnd_219143 := by
    simpa [prefixWord, tailWord_219143, baseEnd_219143] using wordTrace_append hprefix tailTrace_219143
  have hstable : (prefixWord ++ tailWord_219143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219143).length < 2 ^ (prefixWord ++ tailWord_219143).sum := by decide
  have hdescent : baseEnd_219143 < baseStart_219143 := by decide
  rcases family_descends (prefixWord ++ tailWord_219143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219184 : List Nat := [2, 1, 1, 1, 2, 7, 2, 2, 2]
def baseStart_219184 : Nat := 118140960795 + 219184 * 2 ^ 59
def prefixEnd_219184 : Nat := 4983230072969 + 3 ^ 40 * 219184 * 2
def baseEnd_219184 : Nat := 100041550022378378037331

theorem tailTrace_219184 : CollatzResearch.WordTrace tailWord_219184 prefixEnd_219184 100041550022378378037331 := by
  unfold tailWord_219184
  simp only [CollatzResearch.WordTrace]
  refine ⟨3997148618970638246032303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5329531491960850994709737 3997148618970638246032303)
  ·
    refine ⟨5995722928455957369048455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3997148618970638246032303 5995722928455957369048455)
    ·
      refine ⟨8993584392683936053572683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5995722928455957369048455 8993584392683936053572683)
      ·
        refine ⟨13490376589025904080359025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8993584392683936053572683 13490376589025904080359025)
        ·
          refine ⟨10117782441769428060269269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13490376589025904080359025 10117782441769428060269269)
          ·
            refine ⟨237135525978970970162561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 10117782441769428060269269 237135525978970970162561)
            ·
              refine ⟨177851644484228227621921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237135525978970970162561 177851644484228227621921)
              ·
                refine ⟨133388733363171170716441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177851644484228227621921 133388733363171170716441)
                ·
                  refine ⟨100041550022378378037331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133388733363171170716441 100041550022378378037331)
                  ·
                    rfl

theorem cell20_219184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 2].length) (baseStart_219184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219184 prefixEnd_219184 := by exact prefixLift 219184
  have htrace : WordTrace (prefixWord ++ tailWord_219184) baseStart_219184 baseEnd_219184 := by
    simpa [prefixWord, tailWord_219184, baseEnd_219184] using wordTrace_append hprefix tailTrace_219184
  have hstable : (prefixWord ++ tailWord_219184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219184).length < 2 ^ (prefixWord ++ tailWord_219184).sum := by decide
  have hdescent : baseEnd_219184 < baseStart_219184 := by decide
  rcases family_descends (prefixWord ++ tailWord_219184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219209 : List Nat := [1, 2, 1, 1, 2, 2, 5, 2, 4]
def baseStart_219209 : Nat := 118140960795 + 219209 * 2 ^ 59
def prefixEnd_219209 : Nat := 4983230072969 + 3 ^ 40 * 219209 * 2
def baseEnd_219209 : Nat := 100052960703589402203895

theorem tailTrace_219209 : CollatzResearch.WordTrace tailWord_219209 prefixEnd_219209 100052960703589402203895 := by
  unfold tailWord_219209
  simp only [CollatzResearch.WordTrace]
  refine ⟨7995209062850705761724681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5330139375233803841149787 7995209062850705761724681)
  ·
    refine ⟨5996406797138029321293511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7995209062850705761724681 5996406797138029321293511)
    ·
      refine ⟨8994610195707043981940267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5996406797138029321293511 8994610195707043981940267)
      ·
        refine ⟨13491915293560565972910401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8994610195707043981940267 13491915293560565972910401)
        ·
          refine ⟨10118936470170424479682801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13491915293560565972910401 10118936470170424479682801)
          ·
            refine ⟨7589202352627818359762101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10118936470170424479682801 7589202352627818359762101)
            ·
              refine ⟨711487720558857971227697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7589202352627818359762101 711487720558857971227697)
              ·
                refine ⟨533615790419143478420773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 711487720558857971227697 533615790419143478420773)
                ·
                  refine ⟨100052960703589402203895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 533615790419143478420773 100052960703589402203895)
                  ·
                    rfl

theorem cell20_219209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_219209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219209 prefixEnd_219209 := by exact prefixLift 219209
  have htrace : WordTrace (prefixWord ++ tailWord_219209) baseStart_219209 baseEnd_219209 := by
    simpa [prefixWord, tailWord_219209, baseEnd_219209] using wordTrace_append hprefix tailTrace_219209
  have hstable : (prefixWord ++ tailWord_219209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219209).length < 2 ^ (prefixWord ++ tailWord_219209).sum := by decide
  have hdescent : baseEnd_219209 < baseStart_219209 := by decide
  rcases family_descends (prefixWord ++ tailWord_219209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219247 : List Nat := [1, 1, 2, 1, 3, 4, 1, 3, 4]
def baseStart_219247 : Nat := 118140960795 + 219247 * 2 ^ 59
def prefixEnd_219247 : Nat := 4983230072969 + 3 ^ 40 * 219247 * 2
def baseEnd_219247 : Nat := 100070304939030158937073

theorem tailTrace_219247 : CollatzResearch.WordTrace tailWord_219247 prefixEnd_219247 100070304939030158937073 := by
  unfold tailWord_219247
  simp only [CollatzResearch.WordTrace]
  refine ⟨7996595036713038251607995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5331063357808692167738663 7996595036713038251607995)
  ·
    refine ⟨11994892555069557377411993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7996595036713038251607995 11994892555069557377411993)
    ·
      refine ⟨8996169416302168033058995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11994892555069557377411993 8996169416302168033058995)
      ·
        refine ⟨13494254124453252049588493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8996169416302168033058995 13494254124453252049588493)
        ·
          refine ⟨5060345296669969518595685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13494254124453252049588493 5060345296669969518595685)
          ·
            refine ⟨948814743125619284736691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5060345296669969518595685 948814743125619284736691)
            ·
              refine ⟨1423222114688428927105037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948814743125619284736691 1423222114688428927105037)
              ·
                refine ⟨533708293008160847664389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1423222114688428927105037 533708293008160847664389)
                ·
                  refine ⟨100070304939030158937073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 533708293008160847664389 100070304939030158937073)
                  ·
                    rfl

theorem cell20_219247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_219247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219247 prefixEnd_219247 := by exact prefixLift 219247
  have htrace : WordTrace (prefixWord ++ tailWord_219247) baseStart_219247 baseEnd_219247 := by
    simpa [prefixWord, tailWord_219247, baseEnd_219247] using wordTrace_append hprefix tailTrace_219247
  have hstable : (prefixWord ++ tailWord_219247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219247).length < 2 ^ (prefixWord ++ tailWord_219247).sum := by decide
  have hdescent : baseEnd_219247 < baseStart_219247 := by decide
  rcases family_descends (prefixWord ++ tailWord_219247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219271 : List Nat := [1, 1, 4, 2, 1, 1, 6, 4]
def baseStart_219271 : Nat := 118140960795 + 219271 * 2 ^ 59
def prefixEnd_219271 : Nat := 4983230072969 + 3 ^ 40 * 219271 * 2
def baseEnd_219271 : Nat := 33360419730997580712325

theorem tailTrace_219271 : CollatzResearch.WordTrace tailWord_219271 prefixEnd_219271 33360419730997580712325 := by
  unfold tailWord_219271
  simp only [CollatzResearch.WordTrace]
  refine ⟨7997470388626090350481667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5331646925750726900321111 7997470388626090350481667)
  ·
    refine ⟨11996205582939135525722501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7997470388626090350481667 11996205582939135525722501)
    ·
      refine ⟨2249288546801087911072969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11996205582939135525722501 2249288546801087911072969)
      ·
        refine ⟨1686966410100815933304727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2249288546801087911072969 1686966410100815933304727)
        ·
          refine ⟨2530449615151223899957091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1686966410100815933304727 2530449615151223899957091)
          ·
            refine ⟨3795674422726835849935637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2530449615151223899957091 3795674422726835849935637)
            ·
              refine ⟨177922238565320430465733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3795674422726835849935637 177922238565320430465733)
              ·
                refine ⟨33360419730997580712325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177922238565320430465733 33360419730997580712325)
                ·
                  rfl

theorem cell20_219271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 4].length) (baseStart_219271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219271 prefixEnd_219271 := by exact prefixLift 219271
  have htrace : WordTrace (prefixWord ++ tailWord_219271) baseStart_219271 baseEnd_219271 := by
    simpa [prefixWord, tailWord_219271, baseEnd_219271] using wordTrace_append hprefix tailTrace_219271
  have hstable : (prefixWord ++ tailWord_219271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219271).length < 2 ^ (prefixWord ++ tailWord_219271).sum := by decide
  have hdescent : baseEnd_219271 < baseStart_219271 := by decide
  rcases family_descends (prefixWord ++ tailWord_219271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219288 : List Nat := [2, 1, 2, 4, 4, 1, 6]
def baseStart_219288 : Nat := 118140960795 + 219288 * 2 ^ 59
def prefixEnd_219288 : Nat := 4983230072969 + 3 ^ 40 * 219288 * 2
def baseEnd_219288 : Nat := 11121002050690693174471

theorem tailTrace_219288 : CollatzResearch.WordTrace tailWord_219288 prefixEnd_219288 11121002050690693174471 := by
  unfold tailWord_219288
  simp only [CollatzResearch.WordTrace]
  refine ⟨3999045214782251126925259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5332060286376334835900345 3999045214782251126925259)
  ·
    refine ⟨5998567822173376690387889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3999045214782251126925259 5998567822173376690387889)
    ·
      refine ⟨4498925866630032517790917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5998567822173376690387889 4498925866630032517790917)
      ·
        refine ⟨843548599993131097085797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4498925866630032517790917 843548599993131097085797)
        ·
          refine ⟨158165362498712080703587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 843548599993131097085797 158165362498712080703587)
          ·
            refine ⟨237248043748068121055381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158165362498712080703587 237248043748068121055381)
            ·
              refine ⟨11121002050690693174471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 237248043748068121055381 11121002050690693174471)
              ·
                rfl

theorem cell20_219288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 6].length) (baseStart_219288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219288 prefixEnd_219288 := by exact prefixLift 219288
  have htrace : WordTrace (prefixWord ++ tailWord_219288) baseStart_219288 baseEnd_219288 := by
    simpa [prefixWord, tailWord_219288, baseEnd_219288] using wordTrace_append hprefix tailTrace_219288
  have hstable : (prefixWord ++ tailWord_219288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219288).length < 2 ^ (prefixWord ++ tailWord_219288).sum := by decide
  have hdescent : baseEnd_219288 < baseStart_219288 := by decide
  rcases family_descends (prefixWord ++ tailWord_219288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219309 : List Nat := [1, 5, 2, 1, 2, 1, 1, 7]
def baseStart_219309 : Nat := 118140960795 + 219309 * 2 ^ 59
def prefixEnd_219309 : Nat := 4983230072969 + 3 ^ 40 * 219309 * 2
def baseEnd_219309 : Nat := 33366201142811166290051

theorem tailTrace_219309 : CollatzResearch.WordTrace tailWord_219309 prefixEnd_219309 33366201142811166290051 := by
  unfold tailWord_219309
  simp only [CollatzResearch.WordTrace]
  refine ⟨7998856362488422840364981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5332570908325615226909987 7998856362488422840364981)
  ·
    refine ⟨749892783983289641284217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7998856362488422840364981 749892783983289641284217)
    ·
      refine ⟨562419587987467230963163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 749892783983289641284217 562419587987467230963163)
      ·
        refine ⟨843629381981200846444745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562419587987467230963163 843629381981200846444745)
        ·
          refine ⟨632722036485900634833559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843629381981200846444745 632722036485900634833559)
          ·
            refine ⟨949083054728850952250339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632722036485900634833559 949083054728850952250339)
            ·
              refine ⟨1423624582093276428375509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949083054728850952250339 1423624582093276428375509)
              ·
                refine ⟨33366201142811166290051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1423624582093276428375509 33366201142811166290051)
                ·
                  rfl

theorem cell20_219309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 7].length) (baseStart_219309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219309 prefixEnd_219309 := by exact prefixLift 219309
  have htrace : WordTrace (prefixWord ++ tailWord_219309) baseStart_219309 baseEnd_219309 := by
    simpa [prefixWord, tailWord_219309, baseEnd_219309] using wordTrace_append hprefix tailTrace_219309
  have hstable : (prefixWord ++ tailWord_219309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219309).length < 2 ^ (prefixWord ++ tailWord_219309).sum := by decide
  have hdescent : baseEnd_219309 < baseStart_219309 := by decide
  rcases family_descends (prefixWord ++ tailWord_219309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219337 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 5]
def baseStart_219337 : Nat := 118140960795 + 219337 * 2 ^ 59
def prefixEnd_219337 : Nat := 4983230072969 + 3 ^ 40 * 219337 * 2
def baseEnd_219337 : Nat := 100111383391389845936705

theorem tailTrace_219337 : CollatzResearch.WordTrace tailWord_219337 prefixEnd_219337 100111383391389845936705 := by
  unfold tailWord_219337
  simp only [CollatzResearch.WordTrace]
  refine ⟨7999877606386983622384265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5333251737591322414922843 7999877606386983622384265)
  ·
    refine ⟨5999908204790237716788199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7999877606386983622384265 5999908204790237716788199)
    ·
      refine ⟨8999862307185356575182299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5999908204790237716788199 8999862307185356575182299)
      ·
        refine ⟨13499793460778034862773449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8999862307185356575182299 13499793460778034862773449)
        ·
          refine ⟨10124845095583526147080087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13499793460778034862773449 10124845095583526147080087)
          ·
            refine ⟨15187267643375289220620131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10124845095583526147080087 15187267643375289220620131)
            ·
              refine ⟨22780901465062933830930197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15187267643375289220620131 22780901465062933830930197)
              ·
                refine ⟨1067854756174825023324853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22780901465062933830930197 1067854756174825023324853)
                ·
                  refine ⟨100111383391389845936705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1067854756174825023324853 100111383391389845936705)
                  ·
                    rfl

theorem cell20_219337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_219337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219337 prefixEnd_219337 := by exact prefixLift 219337
  have htrace : WordTrace (prefixWord ++ tailWord_219337) baseStart_219337 baseEnd_219337 := by
    simpa [prefixWord, tailWord_219337, baseEnd_219337] using wordTrace_append hprefix tailTrace_219337
  have hstable : (prefixWord ++ tailWord_219337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219337).length < 2 ^ (prefixWord ++ tailWord_219337).sum := by decide
  have hdescent : baseEnd_219337 < baseStart_219337 := by decide
  rcases family_descends (prefixWord ++ tailWord_219337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219350 : List Nat := [5, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_219350 : Nat := 118140960795 + 219350 * 2 ^ 59
def prefixEnd_219350 : Nat := 4983230072969 + 3 ^ 40 * 219350 * 2
def baseEnd_219350 : Nat := 100117316945619578503319

theorem tailTrace_219350 : CollatzResearch.WordTrace tailWord_219350 prefixEnd_219350 100117316945619578503319 := by
  unfold tailWord_219350
  simp only [CollatzResearch.WordTrace]
  refine ⟨500021984708742927662969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5333567836893257895071669 500021984708742927662969)
  ·
    refine ⟨375016488531557195747227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 500021984708742927662969 375016488531557195747227)
    ·
      refine ⟨562524732797335793620841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375016488531557195747227 562524732797335793620841)
      ·
        refine ⟨421893549598001845215631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 562524732797335793620841 421893549598001845215631)
        ·
          refine ⟨632840324397002767823447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421893549598001845215631 632840324397002767823447)
          ·
            refine ⟨949260486595504151735171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632840324397002767823447 949260486595504151735171)
            ·
              refine ⟨1423890729893256227602757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949260486595504151735171 1423890729893256227602757)
              ·
                refine ⟨266979511854985542675517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1423890729893256227602757 266979511854985542675517)
                ·
                  refine ⟨100117316945619578503319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266979511854985542675517 100117316945619578503319)
                  ·
                    rfl

theorem cell20_219350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_219350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219350 prefixEnd_219350 := by exact prefixLift 219350
  have htrace : WordTrace (prefixWord ++ tailWord_219350) baseStart_219350 baseEnd_219350 := by
    simpa [prefixWord, tailWord_219350, baseEnd_219350] using wordTrace_append hprefix tailTrace_219350
  have hstable : (prefixWord ++ tailWord_219350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219350).length < 2 ^ (prefixWord ++ tailWord_219350).sum := by decide
  have hdescent : baseEnd_219350 < baseStart_219350 := by decide
  rcases family_descends (prefixWord ++ tailWord_219350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219354 : List Nat := [3, 1, 1, 2, 2, 1, 3, 4, 3]
def baseStart_219354 : Nat := 118140960795 + 219354 * 2 ^ 59
def prefixEnd_219354 : Nat := 4983230072969 + 3 ^ 40 * 219354 * 2
def baseEnd_219354 : Nat := 100119142654613342369969

theorem tailTrace_219354 : CollatzResearch.WordTrace tailWord_219354 prefixEnd_219354 100119142654613342369969 := by
  unfold tailWord_219354
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000124411831348881438279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5333665098216930350502077 2000124411831348881438279)
  ·
    refine ⟨3000186617747023322157419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2000124411831348881438279 3000186617747023322157419)
    ·
      refine ⟨4500279926620534983236129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3000186617747023322157419 4500279926620534983236129)
      ·
        refine ⟨3375209944965401237427097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4500279926620534983236129 3375209944965401237427097)
        ·
          refine ⟨2531407458724050928070323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3375209944965401237427097 2531407458724050928070323)
          ·
            refine ⟨3797111188086076392105485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2531407458724050928070323 3797111188086076392105485)
            ·
              refine ⟨1423916695532278647039557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3797111188086076392105485 1423916695532278647039557)
              ·
                refine ⟨266984380412302246319917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1423916695532278647039557 266984380412302246319917)
                ·
                  refine ⟨100119142654613342369969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266984380412302246319917 100119142654613342369969)
                  ·
                    rfl

theorem cell20_219354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_219354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219354 prefixEnd_219354 := by exact prefixLift 219354
  have htrace : WordTrace (prefixWord ++ tailWord_219354) baseStart_219354 baseEnd_219354 := by
    simpa [prefixWord, tailWord_219354, baseEnd_219354] using wordTrace_append hprefix tailTrace_219354
  have hstable : (prefixWord ++ tailWord_219354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219354).length < 2 ^ (prefixWord ++ tailWord_219354).sum := by decide
  have hdescent : baseEnd_219354 < baseStart_219354 := by decide
  rcases family_descends (prefixWord ++ tailWord_219354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219361 : List Nat := [1, 2, 3, 1, 3, 1, 2, 3, 4]
def baseStart_219361 : Nat := 118140960795 + 219361 * 2 ^ 59
def prefixEnd_219361 : Nat := 4983230072969 + 3 ^ 40 * 219361 * 2
def baseEnd_219361 : Nat := 100122337645352429136607

theorem tailTrace_219361 : CollatzResearch.WordTrace tailWord_219361 prefixEnd_219361 100122337645352429136607 := by
  unfold tailWord_219361
  simp only [CollatzResearch.WordTrace]
  refine ⟨8000752958300035721257937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5333835305533357147505291 8000752958300035721257937)
  ·
    refine ⟨6000564718725026790943453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8000752958300035721257937 6000564718725026790943453)
    ·
      refine ⟨2250211769521885046603795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6000564718725026790943453 2250211769521885046603795)
      ·
        refine ⟨3375317654282827569905693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2250211769521885046603795 3375317654282827569905693)
        ·
          refine ⟨1265744120356060338714635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3375317654282827569905693 1265744120356060338714635)
          ·
            refine ⟨1898616180534090508071953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265744120356060338714635 1898616180534090508071953)
            ·
              refine ⟨1423962135400567881053965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1898616180534090508071953 1423962135400567881053965)
              ·
                refine ⟨533985800775212955395237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1423962135400567881053965 533985800775212955395237)
                ·
                  refine ⟨100122337645352429136607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 533985800775212955395237 100122337645352429136607)
                  ·
                    rfl

theorem cell20_219361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_219361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219361 prefixEnd_219361 := by exact prefixLift 219361
  have htrace : WordTrace (prefixWord ++ tailWord_219361) baseStart_219361 baseEnd_219361 := by
    simpa [prefixWord, tailWord_219361, baseEnd_219361] using wordTrace_append hprefix tailTrace_219361
  have hstable : (prefixWord ++ tailWord_219361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219361).length < 2 ^ (prefixWord ++ tailWord_219361).sum := by decide
  have hdescent : baseEnd_219361 < baseStart_219361 := by decide
  rcases family_descends (prefixWord ++ tailWord_219361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219378 : List Nat := [3, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_219378 : Nat := 118140960795 + 219378 * 2 ^ 59
def prefixEnd_219378 : Nat := 4983230072969 + 3 ^ 40 * 219378 * 2
def baseEnd_219378 : Nat := 100130096908575925569871

theorem tailTrace_219378 : CollatzResearch.WordTrace tailWord_219378 prefixEnd_219378 100130096908575925569871 := by
  unfold tailWord_219378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000343249809611906156697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5334248666158965083084525 2000343249809611906156697)
  ·
    refine ⟨1500257437357208929617523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2000343249809611906156697 1500257437357208929617523)
    ·
      refine ⟨2250386156035813394426285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1500257437357208929617523 2250386156035813394426285)
      ·
        refine ⟨843894808513430022909857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2250386156035813394426285 843894808513430022909857)
        ·
          refine ⟨632921106385072517182393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843894808513430022909857 632921106385072517182393)
          ·
            refine ⟨474690829788804387886795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 632921106385072517182393 474690829788804387886795)
            ·
              refine ⟨712036244683206581830193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474690829788804387886795 712036244683206581830193)
              ·
                refine ⟨534027183512404936372645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 712036244683206581830193 534027183512404936372645)
                ·
                  refine ⟨100130096908575925569871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 534027183512404936372645 100130096908575925569871)
                  ·
                    rfl

theorem cell20_219378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_219378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219378 prefixEnd_219378 := by exact prefixLift 219378
  have htrace : WordTrace (prefixWord ++ tailWord_219378) baseStart_219378 baseEnd_219378 := by
    simpa [prefixWord, tailWord_219378, baseEnd_219378] using wordTrace_append hprefix tailTrace_219378
  have hstable : (prefixWord ++ tailWord_219378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219378).length < 2 ^ (prefixWord ++ tailWord_219378).sum := by decide
  have hdescent : baseEnd_219378 < baseStart_219378 := by decide
  rcases family_descends (prefixWord ++ tailWord_219378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219406 : List Nat := [4, 1, 1, 2, 1, 2, 9]
def baseStart_219406 : Nat := 118140960795 + 219406 * 2 ^ 59
def prefixEnd_219406 : Nat := 4983230072969 + 3 ^ 40 * 219406 * 2
def baseEnd_219406 : Nat := 11126986319059141404047

theorem tailTrace_219406 : CollatzResearch.WordTrace tailWord_219406 prefixEnd_219406 11126986319059141404047 := by
  unfold tailWord_219406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1000299280392126050830759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5334929495424672271097381 1000299280392126050830759)
  ·
    refine ⟨1500448920588189076246139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1000299280392126050830759 1500448920588189076246139)
    ·
      refine ⟨2250673380882283614369209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1500448920588189076246139 2250673380882283614369209)
      ·
        refine ⟨1688005035661712710776907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2250673380882283614369209 1688005035661712710776907)
        ·
          refine ⟨2532007553492569066165361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1688005035661712710776907 2532007553492569066165361)
          ·
            refine ⟨1899005665119426799624021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2532007553492569066165361 1899005665119426799624021)
            ·
              refine ⟨11126986319059141404047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1899005665119426799624021 11126986319059141404047)
              ·
                rfl

theorem cell20_219406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 9].length) (baseStart_219406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219406 prefixEnd_219406 := by exact prefixLift 219406
  have htrace : WordTrace (prefixWord ++ tailWord_219406) baseStart_219406 baseEnd_219406 := by
    simpa [prefixWord, tailWord_219406, baseEnd_219406] using wordTrace_append hprefix tailTrace_219406
  have hstable : (prefixWord ++ tailWord_219406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219406).length < 2 ^ (prefixWord ++ tailWord_219406).sum := by decide
  have hdescent : baseEnd_219406 < baseStart_219406 := by decide
  rcases family_descends (prefixWord ++ tailWord_219406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219409 : List Nat := [1, 2, 2, 1, 1, 7, 1, 2, 3]
def baseStart_219409 : Nat := 118140960795 + 219409 * 2 ^ 59
def prefixEnd_219409 : Nat := 4983230072969 + 3 ^ 40 * 219409 * 2
def baseEnd_219409 : Nat := 100144246153277595536411

theorem tailTrace_219409 : CollatzResearch.WordTrace tailWord_219409 prefixEnd_219409 100144246153277595536411 := by
  unfold tailWord_219409
  simp only [CollatzResearch.WordTrace]
  refine ⟨8002503662126139919005281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5335002441417426612670187 8002503662126139919005281)
  ·
    refine ⟨6001877746594604939253961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8002503662126139919005281 6001877746594604939253961)
    ·
      refine ⟨4501408309945953704440471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6001877746594604939253961 4501408309945953704440471)
      ·
        refine ⟨6752112464918930556660707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4501408309945953704440471 6752112464918930556660707)
        ·
          refine ⟨10128168697378395834991061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6752112464918930556660707 10128168697378395834991061)
          ·
            refine ⟨237378953844806152382603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 10128168697378395834991061 237378953844806152382603)
            ·
              refine ⟨356068430767209228573905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237378953844806152382603 356068430767209228573905)
              ·
                refine ⟨267051323075406921430429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356068430767209228573905 267051323075406921430429)
                ·
                  refine ⟨100144246153277595536411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267051323075406921430429 100144246153277595536411)
                  ·
                    rfl

theorem cell20_219409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 3].length) (baseStart_219409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219409 prefixEnd_219409 := by exact prefixLift 219409
  have htrace : WordTrace (prefixWord ++ tailWord_219409) baseStart_219409 baseEnd_219409 := by
    simpa [prefixWord, tailWord_219409, baseEnd_219409] using wordTrace_append hprefix tailTrace_219409
  have hstable : (prefixWord ++ tailWord_219409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219409).length < 2 ^ (prefixWord ++ tailWord_219409).sum := by decide
  have hdescent : baseEnd_219409 < baseStart_219409 := by decide
  rcases family_descends (prefixWord ++ tailWord_219409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219416 : List Nat := [2, 1, 2, 3, 1, 2, 1, 6, 2]
def baseStart_219416 : Nat := 118140960795 + 219416 * 2 ^ 59
def prefixEnd_219416 : Nat := 4983230072969 + 3 ^ 40 * 219416 * 2
def baseEnd_219416 : Nat := 100147441144016682303049

theorem tailTrace_219416 : CollatzResearch.WordTrace tailWord_219416 prefixEnd_219416 100147441144016682303049 := by
  unfold tailWord_219416
  simp only [CollatzResearch.WordTrace]
  refine ⟨4001379486550390057255051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5335172648733853409673401 4001379486550390057255051)
  ·
    refine ⟨6002069229825585085882577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4001379486550390057255051 6002069229825585085882577)
    ·
      refine ⟨4501551922369188814411933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6002069229825585085882577 4501551922369188814411933)
      ·
        refine ⟨1688081970888445805404475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4501551922369188814411933 1688081970888445805404475)
        ·
          refine ⟨2532122956332668708106713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1688081970888445805404475 2532122956332668708106713)
          ·
            refine ⟨1899092217249501531080035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2532122956332668708106713 1899092217249501531080035)
            ·
              refine ⟨2848638325874252296620053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1899092217249501531080035 2848638325874252296620053)
              ·
                refine ⟨133529921525355576404065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2848638325874252296620053 133529921525355576404065)
                ·
                  refine ⟨100147441144016682303049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133529921525355576404065 100147441144016682303049)
                  ·
                    rfl

theorem cell20_219416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 2].length) (baseStart_219416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219416 prefixEnd_219416 := by exact prefixLift 219416
  have htrace : WordTrace (prefixWord ++ tailWord_219416) baseStart_219416 baseEnd_219416 := by
    simpa [prefixWord, tailWord_219416, baseEnd_219416] using wordTrace_append hprefix tailTrace_219416
  have hstable : (prefixWord ++ tailWord_219416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219416).length < 2 ^ (prefixWord ++ tailWord_219416).sum := by decide
  have hdescent : baseEnd_219416 < baseStart_219416 := by decide
  rcases family_descends (prefixWord ++ tailWord_219416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219426 : List Nat := [3, 3, 1, 1, 3, 2, 3, 1, 3]
def baseStart_219426 : Nat := 118140960795 + 219426 * 2 ^ 59
def prefixEnd_219426 : Nat := 4983230072969 + 3 ^ 40 * 219426 * 2
def baseEnd_219426 : Nat := 100152005416501091969675

theorem tailTrace_219426 : CollatzResearch.WordTrace tailWord_219426 prefixEnd_219426 100152005416501091969675 := by
  unfold tailWord_219426
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000780925766137955593533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5335415802043034548249421 2000780925766137955593533)
  ·
    refine ⟨750292847162301733347575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2000780925766137955593533 750292847162301733347575)
    ·
      refine ⟨1125439270743452600021363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 750292847162301733347575 1125439270743452600021363)
      ·
        refine ⟨1688158906115178900032045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1125439270743452600021363 1688158906115178900032045)
        ·
          refine ⟨633059589793192087512017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1688158906115178900032045 633059589793192087512017)
          ·
            refine ⟨474794692344894065634013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 633059589793192087512017 474794692344894065634013)
            ·
              refine ⟨178048009629335274612755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 474794692344894065634013 178048009629335274612755)
              ·
                refine ⟨267072014444002911919133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178048009629335274612755 267072014444002911919133)
                ·
                  refine ⟨100152005416501091969675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267072014444002911919133 100152005416501091969675)
                  ·
                    rfl

theorem cell20_219426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_219426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219426 prefixEnd_219426 := by exact prefixLift 219426
  have htrace : WordTrace (prefixWord ++ tailWord_219426) baseStart_219426 baseEnd_219426 := by
    simpa [prefixWord, tailWord_219426, baseEnd_219426] using wordTrace_append hprefix tailTrace_219426
  have hstable : (prefixWord ++ tailWord_219426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219426).length < 2 ^ (prefixWord ++ tailWord_219426).sum := by decide
  have hdescent : baseEnd_219426 < baseStart_219426 := by decide
  rcases family_descends (prefixWord ++ tailWord_219426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219468 : List Nat := [2, 2, 1, 3, 2, 1, 2, 4, 3]
def baseStart_219468 : Nat := 118140960795 + 219468 * 2 ^ 59
def prefixEnd_219468 : Nat := 4983230072969 + 3 ^ 40 * 219468 * 2
def baseEnd_219468 : Nat := 100171175360935612569503

theorem tailTrace_219468 : CollatzResearch.WordTrace tailWord_219468 prefixEnd_219468 100171175360935612569503 := by
  unfold tailWord_219468
  simp only [CollatzResearch.WordTrace]
  refine ⟨4002327784456196497701529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5336437045941595330268705 4002327784456196497701529)
  ·
    refine ⟨3001745838342147373276147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4002327784456196497701529 3001745838342147373276147)
    ·
      refine ⟨4502618757513221059914221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3001745838342147373276147 4502618757513221059914221)
      ·
        refine ⟨1688482034067457897467833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4502618757513221059914221 1688482034067457897467833)
        ·
          refine ⟨1266361525550593423100875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1688482034067457897467833 1266361525550593423100875)
          ·
            refine ⟨1899542288325890134651313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266361525550593423100875 1899542288325890134651313)
            ·
              refine ⟨1424656716244417600988485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1899542288325890134651313 1424656716244417600988485)
              ·
                refine ⟨267123134295828300185341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1424656716244417600988485 267123134295828300185341)
                ·
                  refine ⟨100171175360935612569503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267123134295828300185341 100171175360935612569503)
                  ·
                    rfl

theorem cell20_219468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_219468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219468 prefixEnd_219468 := by exact prefixLift 219468
  have htrace : WordTrace (prefixWord ++ tailWord_219468) baseStart_219468 baseEnd_219468 := by
    simpa [prefixWord, tailWord_219468, baseEnd_219468] using wordTrace_append hprefix tailTrace_219468
  have hstable : (prefixWord ++ tailWord_219468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219468).length < 2 ^ (prefixWord ++ tailWord_219468).sum := by decide
  have hdescent : baseEnd_219468 < baseStart_219468 := by decide
  rcases family_descends (prefixWord ++ tailWord_219468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219522 : List Nat := [3, 4, 2, 1, 2, 2, 2, 2, 2]
def baseStart_219522 : Nat := 118140960795 + 219522 * 2 ^ 59
def prefixEnd_219522 : Nat := 4983230072969 + 3 ^ 40 * 219522 * 2
def baseEnd_219522 : Nat := 100195822432351424769283

theorem tailTrace_219522 : CollatzResearch.WordTrace tailWord_219522 prefixEnd_219522 100195822432351424769283 := by
  unfold tailWord_219522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2001656277679190054467205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5337750073811173478579213 2001656277679190054467205)
  ·
    refine ⟨375310552064848135212601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2001656277679190054467205 375310552064848135212601)
    ·
      refine ⟨281482914048636101409451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375310552064848135212601 281482914048636101409451)
      ·
        refine ⟨422224371072954152114177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281482914048636101409451 422224371072954152114177)
        ·
          refine ⟨316668278304715614085633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422224371072954152114177 316668278304715614085633)
          ·
            refine ⟨237501208728536710564225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316668278304715614085633 237501208728536710564225)
            ·
              refine ⟨178125906546402532923169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237501208728536710564225 178125906546402532923169)
              ·
                refine ⟨133594429909801899692377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178125906546402532923169 133594429909801899692377)
                ·
                  refine ⟨100195822432351424769283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133594429909801899692377 100195822432351424769283)
                  ·
                    rfl

theorem cell20_219522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_219522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219522 prefixEnd_219522 := by exact prefixLift 219522
  have htrace : WordTrace (prefixWord ++ tailWord_219522) baseStart_219522 baseEnd_219522 := by
    simpa [prefixWord, tailWord_219522, baseEnd_219522] using wordTrace_append hprefix tailTrace_219522
  have hstable : (prefixWord ++ tailWord_219522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219522).length < 2 ^ (prefixWord ++ tailWord_219522).sum := by decide
  have hdescent : baseEnd_219522 < baseStart_219522 := by decide
  rcases family_descends (prefixWord ++ tailWord_219522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219523 : List Nat := [1, 1, 1, 3, 6, 1, 2, 2, 3]
def baseStart_219523 : Nat := 118140960795 + 219523 * 2 ^ 59
def prefixEnd_219523 : Nat := 4983230072969 + 3 ^ 40 * 219523 * 2
def baseEnd_219523 : Nat := 100196278859599865735945

theorem tailTrace_219523 : CollatzResearch.WordTrace tailWord_219523 prefixEnd_219523 100196278859599865735945 := by
  unfold tailWord_219523
  simp only [CollatzResearch.WordTrace]
  refine ⟨8006661583713137388655223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5337774389142091592436815 8006661583713137388655223)
  ·
    refine ⟨12009992375569706082982835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8006661583713137388655223 12009992375569706082982835)
    ·
      refine ⟨18014988563354559124474253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12009992375569706082982835 18014988563354559124474253)
      ·
        refine ⟨6755620711257959671677845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18014988563354559124474253 6755620711257959671677845)
        ·
          refine ⟨316669720840216859609899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6755620711257959671677845 316669720840216859609899)
          ·
            refine ⟨475004581260325289414849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316669720840216859609899 475004581260325289414849)
            ·
              refine ⟨356253435945243967061137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475004581260325289414849 356253435945243967061137)
              ·
                refine ⟨267190076958932975295853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356253435945243967061137 267190076958932975295853)
                ·
                  refine ⟨100196278859599865735945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267190076958932975295853 100196278859599865735945)
                  ·
                    rfl

theorem cell20_219523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 3].length) (baseStart_219523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219523 prefixEnd_219523 := by exact prefixLift 219523
  have htrace : WordTrace (prefixWord ++ tailWord_219523) baseStart_219523 baseEnd_219523 := by
    simpa [prefixWord, tailWord_219523, baseEnd_219523] using wordTrace_append hprefix tailTrace_219523
  have hstable : (prefixWord ++ tailWord_219523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219523).length < 2 ^ (prefixWord ++ tailWord_219523).sum := by decide
  have hdescent : baseEnd_219523 < baseStart_219523 := by decide
  rcases family_descends (prefixWord ++ tailWord_219523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
