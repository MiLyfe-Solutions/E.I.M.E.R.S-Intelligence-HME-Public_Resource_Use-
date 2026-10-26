import V185TrunkScan23Chunk1201

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7120814 : List Nat := [4, 1, 5, 1, 1, 1, 2, 2, 6]
def baseStart_7120814 : Nat := 118140960795 + 7120814 * 2 ^ 59
def prefixEnd_7120814 : Nat := 4983230072969 + 3 ^ 40 * 7120814 * 2
def baseEnd_7120814 : Nat := 406266692585000890686331

theorem tailTrace_7120814 : CollatzResearch.WordTrace tailWord_7120814 prefixEnd_7120814 406266692585000890686331 := by
  unfold tailWord_7120814
  simp only [CollatzResearch.WordTrace]
  refine ⟨32464677903064311381825187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173144948816342994036400997 32464677903064311381825187)
  ·
    refine ⟨48697016854596467072737781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32464677903064311381825187 48697016854596467072737781)
    ·
      refine ⟨4565345330118418788069167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48697016854596467072737781 4565345330118418788069167)
      ·
        refine ⟨6848017995177628182103751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4565345330118418788069167 6848017995177628182103751)
        ·
          refine ⟨10272026992766442273155627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6848017995177628182103751 10272026992766442273155627)
          ·
            refine ⟨15408040489149663409733441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10272026992766442273155627 15408040489149663409733441)
            ·
              refine ⟨11556030366862247557300081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15408040489149663409733441 11556030366862247557300081)
              ·
                refine ⟨8667022775146685667975061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11556030366862247557300081 8667022775146685667975061)
                ·
                  refine ⟨406266692585000890686331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8667022775146685667975061 406266692585000890686331)
                  ·
                    rfl

theorem cell23_7120814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_7120814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120814 prefixEnd_7120814 := by exact prefixLift 7120814
  have htrace : WordTrace (prefixWord ++ tailWord_7120814) baseStart_7120814 baseEnd_7120814 := by
    simpa [prefixWord, tailWord_7120814, baseEnd_7120814] using wordTrace_append hprefix tailTrace_7120814
  have hstable : (prefixWord ++ tailWord_7120814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120814).length < 2 ^ (prefixWord ++ tailWord_7120814).sum := by decide
  have hdescent : baseEnd_7120814 < baseStart_7120814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120826 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6]
def baseStart_7120826 : Nat := 118140960795 + 7120826 * 2 ^ 59
def prefixEnd_7120826 : Nat := 4983230072969 + 3 ^ 40 * 7120826 * 2
def baseEnd_7120826 : Nat := 3656406395032861969226923

theorem tailTrace_7120826 : CollatzResearch.WordTrace tailWord_7120826 prefixEnd_7120826 3656406395032861969226923 := by
  unfold tailWord_7120826
  simp only [CollatzResearch.WordTrace]
  refine ⟨64929465225117754276009583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173145240600314011402692221 64929465225117754276009583)
  ·
    refine ⟨97394197837676631414014375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64929465225117754276009583 97394197837676631414014375)
    ·
      refine ⟨146091296756514947121021563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97394197837676631414014375 146091296756514947121021563)
      ·
        refine ⟨219136945134772420681532345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146091296756514947121021563 219136945134772420681532345)
        ·
          refine ⟨164352708851079315511149259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219136945134772420681532345 164352708851079315511149259)
          ·
            refine ⟨246529063276618973266723889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164352708851079315511149259 246529063276618973266723889)
            ·
              refine ⟨184896797457464229950042917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246529063276618973266723889 184896797457464229950042917)
              ·
                refine ⟨34668149523274543115633047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184896797457464229950042917 34668149523274543115633047)
                ·
                  refine ⟨52002224284911814673449571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34668149523274543115633047 52002224284911814673449571)
                  ·
                    refine ⟨78003336427367722010174357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52002224284911814673449571 78003336427367722010174357)
                    ·
                      refine ⟨3656406395032861969226923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78003336427367722010174357 3656406395032861969226923)
                      ·
                        rfl

theorem cell23_7120826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_7120826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120826 prefixEnd_7120826 := by exact prefixLift 7120826
  have htrace : WordTrace (prefixWord ++ tailWord_7120826) baseStart_7120826 baseEnd_7120826 := by
    simpa [prefixWord, tailWord_7120826, baseEnd_7120826] using wordTrace_append hprefix tailTrace_7120826
  have hstable : (prefixWord ++ tailWord_7120826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120826).length < 2 ^ (prefixWord ++ tailWord_7120826).sum := by decide
  have hdescent : baseEnd_7120826 < baseStart_7120826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120840 : List Nat := [2, 1, 3, 1, 4, 1, 2, 3, 2, 4]
def baseStart_7120840 : Nat := 118140960795 + 7120840 * 2 ^ 59
def prefixEnd_7120840 : Nat := 4983230072969 + 3 ^ 40 * 7120840 * 2
def baseEnd_7120840 : Nat := 1218804527920674971483953

theorem tailTrace_7120840 : CollatzResearch.WordTrace tailWord_7120840 prefixEnd_7120840 1218804527920674971483953 := by
  unfold tailWord_7120840
  simp only [CollatzResearch.WordTrace]
  refine ⟨129859185761210148747523987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173145581014946864996698649 129859185761210148747523987)
  ·
    refine ⟨194788778641815223121285981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129859185761210148747523987 194788778641815223121285981)
    ·
      refine ⟨73045791990680708670482243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194788778641815223121285981 73045791990680708670482243)
      ·
        refine ⟨109568687986021063005723365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73045791990680708670482243 109568687986021063005723365)
        ·
          refine ⟨20544128997378949313573131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109568687986021063005723365 20544128997378949313573131)
          ·
            refine ⟨30816193496068423970359697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20544128997378949313573131 30816193496068423970359697)
            ·
              refine ⟨23112145122051317977769773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30816193496068423970359697 23112145122051317977769773)
              ·
                refine ⟨8667054420769244241663665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23112145122051317977769773 8667054420769244241663665)
                ·
                  refine ⟨6500290815576933181247749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8667054420769244241663665 6500290815576933181247749)
                  ·
                    refine ⟨1218804527920674971483953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6500290815576933181247749 1218804527920674971483953)
                    ·
                      rfl

theorem cell23_7120840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_7120840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120840 prefixEnd_7120840 := by exact prefixLift 7120840
  have htrace : WordTrace (prefixWord ++ tailWord_7120840) baseStart_7120840 baseEnd_7120840 := by
    simpa [prefixWord, tailWord_7120840, baseEnd_7120840] using wordTrace_append hprefix tailTrace_7120840
  have hstable : (prefixWord ++ tailWord_7120840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120840).length < 2 ^ (prefixWord ++ tailWord_7120840).sum := by decide
  have hdescent : baseEnd_7120840 < baseStart_7120840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120843 : List Nat := [1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 4]
def baseStart_7120843 : Nat := 118140960795 + 7120843 * 2 ^ 59
def prefixEnd_7120843 : Nat := 4983230072969 + 3 ^ 40 * 7120843 * 2
def baseEnd_7120843 : Nat := 3656415124203988402714345

theorem tailTrace_7120843 : CollatzResearch.WordTrace tailWord_7120843 prefixEnd_7120843 3656415124203988402714345 := by
  unfold tailWord_7120843
  simp only [CollatzResearch.WordTrace]
  refine ⟨259718480941409429007407183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173145653960939619338271455 259718480941409429007407183)
  ·
    refine ⟨389577721412114143511110775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259718480941409429007407183 389577721412114143511110775)
    ·
      refine ⟨584366582118171215266666163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389577721412114143511110775 584366582118171215266666163)
      ·
        refine ⟨876549873177256822899999245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584366582118171215266666163 876549873177256822899999245)
        ·
          refine ⟨328706202441471308587499717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 876549873177256822899999245 328706202441471308587499717)
          ·
            refine ⟨61632412957775870360156197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 328706202441471308587499717 61632412957775870360156197)
            ·
              refine ⟨11556077429582975692529287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61632412957775870360156197 11556077429582975692529287)
              ·
                refine ⟨17334116144374463538793931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11556077429582975692529287 17334116144374463538793931)
                ·
                  refine ⟨26001174216561695308190897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17334116144374463538793931 26001174216561695308190897)
                  ·
                    refine ⟨19500880662421271481143173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26001174216561695308190897 19500880662421271481143173)
                    ·
                      refine ⟨3656415124203988402714345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19500880662421271481143173 3656415124203988402714345)
                      ·
                        rfl

theorem cell23_7120843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 4].length) (baseStart_7120843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120843 prefixEnd_7120843 := by exact prefixLift 7120843
  have htrace : WordTrace (prefixWord ++ tailWord_7120843) baseStart_7120843 baseEnd_7120843 := by
    simpa [prefixWord, tailWord_7120843, baseEnd_7120843] using wordTrace_append hprefix tailTrace_7120843
  have hstable : (prefixWord ++ tailWord_7120843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120843).length < 2 ^ (prefixWord ++ tailWord_7120843).sum := by decide
  have hdescent : baseEnd_7120843 < baseStart_7120843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120867 : List Nat := [1, 1, 1, 6, 1, 2, 4, 1, 1, 2, 3]
def baseStart_7120867 : Nat := 118140960795 + 7120867 * 2 ^ 59
def prefixEnd_7120867 : Nat := 4983230072969 + 3 ^ 40 * 7120867 * 2
def baseEnd_7120867 : Nat := 3656427447739696308814235

theorem tailTrace_7120867 : CollatzResearch.WordTrace tailWord_7120867 prefixEnd_7120867 3656427447739696308814235 := by
  unfold tailWord_7120867
  simp only [CollatzResearch.WordTrace]
  refine ⟨259719356293322481106280855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173146237528881654070853903 259719356293322481106280855)
  ·
    refine ⟨389579034439983721659421283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259719356293322481106280855 389579034439983721659421283)
    ·
      refine ⟨584368551659975582489131925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389579034439983721659421283 584368551659975582489131925)
      ·
        refine ⟨27392275859061355429178059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 584368551659975582489131925 27392275859061355429178059)
        ·
          refine ⟨41088413788592033143767089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27392275859061355429178059 41088413788592033143767089)
          ·
            refine ⟨30816310341444024857825317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41088413788592033143767089 30816310341444024857825317)
            ·
              refine ⟨5778058189020754660842247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30816310341444024857825317 5778058189020754660842247)
              ·
                refine ⟨8667087283531131991263371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5778058189020754660842247 8667087283531131991263371)
                ·
                  refine ⟨13000630925296697986895057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8667087283531131991263371 13000630925296697986895057)
                  ·
                    refine ⟨9750473193972523490171293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13000630925296697986895057 9750473193972523490171293)
                    ·
                      refine ⟨3656427447739696308814235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9750473193972523490171293 3656427447739696308814235)
                      ·
                        rfl

theorem cell23_7120867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_7120867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120867 prefixEnd_7120867 := by exact prefixLift 7120867
  have htrace : WordTrace (prefixWord ++ tailWord_7120867) baseStart_7120867 baseEnd_7120867 := by
    simpa [prefixWord, tailWord_7120867, baseEnd_7120867] using wordTrace_append hprefix tailTrace_7120867
  have hstable : (prefixWord ++ tailWord_7120867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120867).length < 2 ^ (prefixWord ++ tailWord_7120867).sum := by decide
  have hdescent : baseEnd_7120867 < baseStart_7120867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120896 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 1, 8]
def baseStart_7120896 : Nat := 118140960795 + 7120896 * 2 ^ 59
def prefixEnd_7120896 : Nat := 4983230072969 + 3 ^ 40 * 7120896 * 2
def baseEnd_7120896 : Nat := 1218814112892892231783867

theorem tailTrace_7120896 : CollatzResearch.WordTrace tailWord_7120896 prefixEnd_7120896 1218814112892892231783867 := by
  unfold tailWord_7120896
  simp only [CollatzResearch.WordTrace]
  refine ⟨129860207005108709529543271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173146942673478279372724361 129860207005108709529543271)
  ·
    refine ⟨194790310507663064294314907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129860207005108709529543271 194790310507663064294314907)
    ·
      refine ⟨292185465761494596441472361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194790310507663064294314907 292185465761494596441472361)
      ·
        refine ⟨219139099321120947331104271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292185465761494596441472361 219139099321120947331104271)
        ·
          refine ⟨328708648981681420996656407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219139099321120947331104271 328708648981681420996656407)
          ·
            refine ⟨493062973472522131494984611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328708648981681420996656407 493062973472522131494984611)
            ·
              refine ⟨739594460208783197242476917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493062973472522131494984611 739594460208783197242476917)
              ·
                refine ⟨69336980644573424741482211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 739594460208783197242476917 69336980644573424741482211)
                ·
                  refine ⟨104005470966860137112223317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69336980644573424741482211 104005470966860137112223317)
                  ·
                    refine ⟨1218814112892892231783867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104005470966860137112223317 1218814112892892231783867)
                    ·
                      rfl

theorem cell23_7120896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 1, 8].length) (baseStart_7120896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120896 prefixEnd_7120896 := by exact prefixLift 7120896
  have htrace : WordTrace (prefixWord ++ tailWord_7120896) baseStart_7120896 baseEnd_7120896 := by
    simpa [prefixWord, tailWord_7120896, baseEnd_7120896] using wordTrace_append hprefix tailTrace_7120896
  have hstable : (prefixWord ++ tailWord_7120896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120896).length < 2 ^ (prefixWord ++ tailWord_7120896).sum := by decide
  have hdescent : baseEnd_7120896 < baseStart_7120896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120907 : List Nat := [1, 1, 1, 1, 6, 1, 4, 2, 1, 3, 2]
def baseStart_7120907 : Nat := 118140960795 + 7120907 * 2 ^ 59
def prefixEnd_7120907 : Nat := 4983230072969 + 3 ^ 40 * 7120907 * 2
def baseEnd_7120907 : Nat := 3656447986965876152314051

theorem tailTrace_7120907 : CollatzResearch.WordTrace tailWord_7120907 prefixEnd_7120907 3656447986965876152314051 := by
  unfold tailWord_7120907
  simp only [CollatzResearch.WordTrace]
  refine ⟨259720815213177567937736975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173147210142118378625157983 259720815213177567937736975)
  ·
    refine ⟨389581222819766351906605463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259720815213177567937736975 389581222819766351906605463)
    ·
      refine ⟨584371834229649527859908195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389581222819766351906605463 584371834229649527859908195)
      ·
        refine ⟨876557751344474291789862293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584371834229649527859908195 876557751344474291789862293)
        ·
          refine ⟨41088644594272232427649795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 876557751344474291789862293 41088644594272232427649795)
          ·
            refine ⟨61632966891408348641474693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41088644594272232427649795 61632966891408348641474693)
            ·
              refine ⟨11556181292139065370276505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61632966891408348641474693 11556181292139065370276505)
              ·
                refine ⟨8667135969104299027707379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11556181292139065370276505 8667135969104299027707379)
                ·
                  refine ⟨13000703953656448541561069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8667135969104299027707379 13000703953656448541561069)
                  ·
                    refine ⟨4875263982621168203085401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13000703953656448541561069 4875263982621168203085401)
                    ·
                      refine ⟨3656447986965876152314051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4875263982621168203085401 3656447986965876152314051)
                      ·
                        rfl

theorem cell23_7120907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 3, 2].length) (baseStart_7120907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120907 prefixEnd_7120907 := by exact prefixLift 7120907
  have htrace : WordTrace (prefixWord ++ tailWord_7120907) baseStart_7120907 baseEnd_7120907 := by
    simpa [prefixWord, tailWord_7120907, baseEnd_7120907] using wordTrace_append hprefix tailTrace_7120907
  have hstable : (prefixWord ++ tailWord_7120907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120907).length < 2 ^ (prefixWord ++ tailWord_7120907).sum := by decide
  have hdescent : baseEnd_7120907 < baseStart_7120907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120920 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 3, 4, 2]
def baseStart_7120920 : Nat := 118140960795 + 7120920 * 2 ^ 59
def prefixEnd_7120920 : Nat := 4983230072969 + 3 ^ 40 * 7120920 * 2
def baseEnd_7120920 : Nat := 3656454662214384601451491

theorem tailTrace_7120920 : CollatzResearch.WordTrace tailWord_7120920 prefixEnd_7120920 3656454662214384601451491 := by
  unfold tailWord_7120920
  simp only [CollatzResearch.WordTrace]
  refine ⟨129860644681065235578980107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173147526241420314105306809 129860644681065235578980107)
  ·
    refine ⟨194790967021597853368470161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129860644681065235578980107 194790967021597853368470161)
    ·
      refine ⟨146093225266198390026352621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194790967021597853368470161 146093225266198390026352621)
      ·
        refine ⟨54784959474824396259882233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146093225266198390026352621 54784959474824396259882233)
        ·
          refine ⟨41088719606118297194911675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54784959474824396259882233 41088719606118297194911675)
          ·
            refine ⟨61633079409177445792367513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41088719606118297194911675 61633079409177445792367513)
            ·
              refine ⟨46224809556883084344275635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61633079409177445792367513 46224809556883084344275635)
              ·
                refine ⟨69337214335324626516413453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46224809556883084344275635 69337214335324626516413453)
                ·
                  refine ⟨26001455375746734943655045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69337214335324626516413453 26001455375746734943655045)
                  ·
                    refine ⟨4875272882952512801935321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26001455375746734943655045 4875272882952512801935321)
                    ·
                      refine ⟨3656454662214384601451491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4875272882952512801935321 3656454662214384601451491)
                      ·
                        rfl

theorem cell23_7120920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_7120920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120920 prefixEnd_7120920 := by exact prefixLift 7120920
  have htrace : WordTrace (prefixWord ++ tailWord_7120920) baseStart_7120920 baseEnd_7120920 := by
    simpa [prefixWord, tailWord_7120920, baseEnd_7120920] using wordTrace_append hprefix tailTrace_7120920
  have hstable : (prefixWord ++ tailWord_7120920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120920).length < 2 ^ (prefixWord ++ tailWord_7120920).sum := by decide
  have hdescent : baseEnd_7120920 < baseStart_7120920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120948 : List Nat := [2, 5, 1, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_7120948 : Nat := 118140960795 + 7120948 * 2 ^ 59
def prefixEnd_7120948 : Nat := 4983230072969 + 3 ^ 40 * 7120948 * 2
def baseEnd_7120948 : Nat := 3656469039672710491901363

theorem tailTrace_7120948 : CollatzResearch.WordTrace tailWord_7120948 prefixEnd_7120948 3656469039672710491901363 := by
  unfold tailWord_7120948
  simp only [CollatzResearch.WordTrace]
  refine ⟨129861155303014515969989749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173148207070686021293319665 129861155303014515969989749)
  ·
    refine ⟨12174483309657610872186539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129861155303014515969989749 12174483309657610872186539)
    ·
      refine ⟨18261724964486416308279809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12174483309657610872186539 18261724964486416308279809)
      ·
        refine ⟨13696293723364812231209857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18261724964486416308279809 13696293723364812231209857)
        ·
          refine ⟨10272220292523609173407393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13696293723364812231209857 10272220292523609173407393)
          ·
            refine ⟨7704165219392706880055545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10272220292523609173407393 7704165219392706880055545)
            ·
              refine ⟨5778123914544530160041659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7704165219392706880055545 5778123914544530160041659)
              ·
                refine ⟨8667185871816795240062489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5778123914544530160041659 8667185871816795240062489)
                ·
                  refine ⟨6500389403862596430046867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8667185871816795240062489 6500389403862596430046867)
                  ·
                    refine ⟨9750584105793894645070301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6500389403862596430046867 9750584105793894645070301)
                    ·
                      refine ⟨3656469039672710491901363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9750584105793894645070301 3656469039672710491901363)
                      ·
                        rfl

theorem cell23_7120948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_7120948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120948 prefixEnd_7120948 := by exact prefixLift 7120948
  have htrace : WordTrace (prefixWord ++ tailWord_7120948) baseStart_7120948 baseEnd_7120948 := by
    simpa [prefixWord, tailWord_7120948, baseEnd_7120948] using wordTrace_append hprefix tailTrace_7120948
  have hstable : (prefixWord ++ tailWord_7120948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120948).length < 2 ^ (prefixWord ++ tailWord_7120948).sum := by decide
  have hdescent : baseEnd_7120948 < baseStart_7120948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120950 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_7120950 : Nat := 118140960795 + 7120950 * 2 ^ 59
def prefixEnd_7120950 : Nat := 4983230072969 + 3 ^ 40 * 7120950 * 2
def baseEnd_7120950 : Nat := 3656470066634019484076353

theorem tailTrace_7120950 : CollatzResearch.WordTrace tailWord_7120950 prefixEnd_7120950 3656470066634019484076353 := by
  unfold tailWord_7120950
  simp only [CollatzResearch.WordTrace]
  refine ⟨16232648972001361642597019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173148255701347857521034869 16232648972001361642597019)
  ·
    refine ⟨24348973458002042463895529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16232648972001361642597019 24348973458002042463895529)
    ·
      refine ⟨18261730093501531847921647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24348973458002042463895529 18261730093501531847921647)
      ·
        refine ⟨27392595140252297771882471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18261730093501531847921647 27392595140252297771882471)
        ·
          refine ⟨41088892710378446657823707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27392595140252297771882471 41088892710378446657823707)
          ·
            refine ⟨61633339065567669986735561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41088892710378446657823707 61633339065567669986735561)
            ·
              refine ⟨46225004299175752490051671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61633339065567669986735561 46225004299175752490051671)
              ·
                refine ⟨69337506448763628735077507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46225004299175752490051671 69337506448763628735077507)
                ·
                  refine ⟨104006259673145443102616261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69337506448763628735077507 104006259673145443102616261)
                  ·
                    refine ⟨19501173688714770581740549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104006259673145443102616261 19501173688714770581740549)
                    ·
                      refine ⟨3656470066634019484076353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19501173688714770581740549 3656470066634019484076353)
                      ·
                        rfl

theorem cell23_7120950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_7120950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120950 prefixEnd_7120950 := by exact prefixLift 7120950
  have htrace : WordTrace (prefixWord ++ tailWord_7120950) baseStart_7120950 baseEnd_7120950 := by
    simpa [prefixWord, tailWord_7120950, baseEnd_7120950] using wordTrace_append hprefix tailTrace_7120950
  have hstable : (prefixWord ++ tailWord_7120950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120950).length < 2 ^ (prefixWord ++ tailWord_7120950).sum := by decide
  have hdescent : baseEnd_7120950 < baseStart_7120950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120958 : List Nat := [4, 2, 1, 3, 3, 1, 1, 2, 1, 3, 2]
def baseStart_7120958 : Nat := 118140960795 + 7120958 * 2 ^ 59
def prefixEnd_7120958 : Nat := 4983230072969 + 3 ^ 40 * 7120958 * 2
def baseEnd_7120958 : Nat := 3656474174479255452776317

theorem tailTrace_7120958 : CollatzResearch.WordTrace tailWord_7120958 prefixEnd_7120958 3656474174479255452776317 := by
  unfold tailWord_7120958
  simp only [CollatzResearch.WordTrace]
  refine ⟨32465334416999100455980441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173148450223995202431895685 32465334416999100455980441)
  ·
    refine ⟨24349000812749325341985331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32465334416999100455980441 24349000812749325341985331)
    ·
      refine ⟨36523501219123988012977997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24349000812749325341985331 36523501219123988012977997)
      ·
        refine ⟨13696312957171495504866749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36523501219123988012977997 13696312957171495504866749)
        ·
          refine ⟨5136117358939310814325031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13696312957171495504866749 5136117358939310814325031)
          ·
            refine ⟨7704176038408966221487547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5136117358939310814325031 7704176038408966221487547)
            ·
              refine ⟨11556264057613449332231321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7704176038408966221487547 11556264057613449332231321)
              ·
                refine ⟨8667198043210086999173491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11556264057613449332231321 8667198043210086999173491)
                ·
                  refine ⟨13000797064815130498760237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8667198043210086999173491 13000797064815130498760237)
                  ·
                    refine ⟨4875298899305673937035089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13000797064815130498760237 4875298899305673937035089)
                    ·
                      refine ⟨3656474174479255452776317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4875298899305673937035089 3656474174479255452776317)
                      ·
                        rfl

theorem cell23_7120958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_7120958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120958 prefixEnd_7120958 := by exact prefixLift 7120958
  have htrace : WordTrace (prefixWord ++ tailWord_7120958) baseStart_7120958 baseEnd_7120958 := by
    simpa [prefixWord, tailWord_7120958, baseEnd_7120958] using wordTrace_append hprefix tailTrace_7120958
  have hstable : (prefixWord ++ tailWord_7120958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120958).length < 2 ^ (prefixWord ++ tailWord_7120958).sum := by decide
  have hdescent : baseEnd_7120958 < baseStart_7120958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120983 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 5]
def baseStart_7120983 : Nat := 118140960795 + 7120983 * 2 ^ 59
def prefixEnd_7120983 : Nat := 4983230072969 + 3 ^ 40 * 7120983 * 2
def baseEnd_7120983 : Nat := 3656487011495617854963701

theorem tailTrace_7120983 : CollatzResearch.WordTrace tailWord_7120983 prefixEnd_7120983 3656487011495617854963701 := by
  unfold tailWord_7120983
  simp only [CollatzResearch.WordTrace]
  refine ⟨259723587160902232917503603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173149058107268155278335735 259723587160902232917503603)
  ·
    refine ⟨389585380741353349376255405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259723587160902232917503603 389585380741353349376255405)
    ·
      refine ⟨146094517778007506016095777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389585380741353349376255405 146094517778007506016095777)
      ·
        refine ⟨109570888333505629512071833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146094517778007506016095777 109570888333505629512071833)
        ·
          refine ⟨82178166250129222134053875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109570888333505629512071833 82178166250129222134053875)
          ·
            refine ⟨123267249375193833201080813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82178166250129222134053875 123267249375193833201080813)
            ·
              refine ⟨46225218515697687450405305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123267249375193833201080813 46225218515697687450405305)
              ·
                refine ⟨34668913886773265587803979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46225218515697687450405305 34668913886773265587803979)
                ·
                  refine ⟨52003370830159898381705969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34668913886773265587803979 52003370830159898381705969)
                  ·
                    refine ⟨39002528122619923786279477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52003370830159898381705969 39002528122619923786279477)
                    ·
                      refine ⟨3656487011495617854963701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39002528122619923786279477 3656487011495617854963701)
                      ·
                        rfl

theorem cell23_7120983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_7120983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120983 prefixEnd_7120983 := by exact prefixLift 7120983
  have htrace : WordTrace (prefixWord ++ tailWord_7120983) baseStart_7120983 baseEnd_7120983 := by
    simpa [prefixWord, tailWord_7120983, baseEnd_7120983] using wordTrace_append hprefix tailTrace_7120983
  have hstable : (prefixWord ++ tailWord_7120983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120983).length < 2 ^ (prefixWord ++ tailWord_7120983).sum := by decide
  have hdescent : baseEnd_7120983 < baseStart_7120983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120993 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_7120993 : Nat := 118140960795 + 7120993 * 2 ^ 59
def prefixEnd_7120993 : Nat := 4983230072969 + 3 ^ 40 * 7120993 * 2
def baseEnd_7120993 : Nat := 3656492146302162815838655

theorem tailTrace_7120993 : CollatzResearch.WordTrace tailWord_7120993 prefixEnd_7120993 3656492146302162815838655 := by
  unfold tailWord_7120993
  simp only [CollatzResearch.WordTrace]
  refine ⟨259723951890866004625367633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173149301260577336416911755 259723951890866004625367633)
  ·
    refine ⟨194792963918149503469025725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259723951890866004625367633 194792963918149503469025725)
    ·
      refine ⟨73047361469306063800884647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194792963918149503469025725 73047361469306063800884647)
      ·
        refine ⟨109571042203959095701326971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73047361469306063800884647 109571042203959095701326971)
        ·
          refine ⟨164356563305938643551990457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109571042203959095701326971 164356563305938643551990457)
          ·
            refine ⟨123267422479453982663992843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164356563305938643551990457 123267422479453982663992843)
            ·
              refine ⟨184901133719180973995989265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123267422479453982663992843 184901133719180973995989265)
              ·
                refine ⟨138675850289385730496991949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184901133719180973995989265 138675850289385730496991949)
                ·
                  refine ⟨52003443858519648936371981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138675850289385730496991949 52003443858519648936371981)
                  ·
                    refine ⟨19501291446944868351139493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52003443858519648936371981 19501291446944868351139493)
                    ·
                      refine ⟨3656492146302162815838655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19501291446944868351139493 3656492146302162815838655)
                      ·
                        rfl

theorem cell23_7120993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_7120993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120993 prefixEnd_7120993 := by exact prefixLift 7120993
  have htrace : WordTrace (prefixWord ++ tailWord_7120993) baseStart_7120993 baseEnd_7120993 := by
    simpa [prefixWord, tailWord_7120993, baseEnd_7120993] using wordTrace_append hprefix tailTrace_7120993
  have hstable : (prefixWord ++ tailWord_7120993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120993).length < 2 ^ (prefixWord ++ tailWord_7120993).sum := by decide
  have hdescent : baseEnd_7120993 < baseStart_7120993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120994 : List Nat := [3, 3, 2, 2, 2, 1, 1, 4, 5]
def baseStart_7120994 : Nat := 118140960795 + 7120994 * 2 ^ 59
def prefixEnd_7120994 : Nat := 4983230072969 + 3 ^ 40 * 7120994 * 2
def baseEnd_7120994 : Nat := 406276962198090812436239

theorem tailTrace_7120994 : CollatzResearch.WordTrace tailWord_7120994 prefixEnd_7120994 406276962198090812436239 := by
  unfold tailWord_7120994
  simp only [CollatzResearch.WordTrace]
  refine ⟨64930997090965595449038509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173149325575908254530769357 64930997090965595449038509)
  ·
    refine ⟨24349123909112098293389441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64930997090965595449038509 24349123909112098293389441)
    ·
      refine ⟨18261842931834073720042081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24349123909112098293389441 18261842931834073720042081)
      ·
        refine ⟨13696382198875555290031561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18261842931834073720042081 13696382198875555290031561)
        ·
          refine ⟨10272286649156666467523671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13696382198875555290031561 10272286649156666467523671)
          ·
            refine ⟨15408429973734999701285507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10272286649156666467523671 15408429973734999701285507)
            ·
              refine ⟨23112644960602499551928261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15408429973734999701285507 23112644960602499551928261)
              ·
                refine ⟨4333620930112968665986549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23112644960602499551928261 4333620930112968665986549)
                ·
                  refine ⟨406276962198090812436239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4333620930112968665986549 406276962198090812436239)
                  ·
                    rfl

theorem cell23_7120994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_7120994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120994 prefixEnd_7120994 := by exact prefixLift 7120994
  have htrace : WordTrace (prefixWord ++ tailWord_7120994) baseStart_7120994 baseEnd_7120994 := by
    simpa [prefixWord, tailWord_7120994, baseEnd_7120994] using wordTrace_append hprefix tailTrace_7120994
  have hstable : (prefixWord ++ tailWord_7120994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120994).length < 2 ^ (prefixWord ++ tailWord_7120994).sum := by decide
  have hdescent : baseEnd_7120994 < baseStart_7120994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121020 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 5, 4]
def baseStart_7121020 : Nat := 118140960795 + 7121020 * 2 ^ 59
def prefixEnd_7121020 : Nat := 4983230072969 + 3 ^ 40 * 7121020 * 2
def baseEnd_7121020 : Nat := 1218835336759944736733677

theorem tailTrace_7121020 : CollatzResearch.WordTrace tailWord_7121020 prefixEnd_7121020 1218835336759944736733677 := by
  unfold tailWord_7121020
  simp only [CollatzResearch.WordTrace]
  refine ⟨129862468330884094118300257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173149957774512125491067009 129862468330884094118300257)
  ·
    refine ⟨97396851248163070588725193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129862468330884094118300257 97396851248163070588725193)
    ·
      refine ⟨73047638436122302941543895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97396851248163070588725193 73047638436122302941543895)
      ·
        refine ⟨109571457654183454412315843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73047638436122302941543895 109571457654183454412315843)
        ·
          refine ⟨164357186481275181618473765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109571457654183454412315843 164357186481275181618473765)
          ·
            refine ⟨30816972465239096553463831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164357186481275181618473765 30816972465239096553463831)
            ·
              refine ⟨46225458697858644830195747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30816972465239096553463831 46225458697858644830195747)
              ·
                refine ⟨69338188046787967245293621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46225458697858644830195747 69338188046787967245293621)
                ·
                  refine ⟨6500455129386371929246277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69338188046787967245293621 6500455129386371929246277)
                  ·
                    refine ⟨1218835336759944736733677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6500455129386371929246277 1218835336759944736733677)
                    ·
                      rfl

theorem cell23_7121020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_7121020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121020 prefixEnd_7121020 := by exact prefixLift 7121020
  have htrace : WordTrace (prefixWord ++ tailWord_7121020) baseStart_7121020 baseEnd_7121020 := by
    simpa [prefixWord, tailWord_7121020, baseEnd_7121020] using wordTrace_append hprefix tailTrace_7121020
  have hstable : (prefixWord ++ tailWord_7121020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121020).length < 2 ^ (prefixWord ++ tailWord_7121020).sum := by decide
  have hdescent : baseEnd_7121020 < baseStart_7121020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121027 : List Nat := [1, 1, 1, 3, 3, 5, 1, 1, 2, 1, 4]
def baseStart_7121027 : Nat := 118140960795 + 7121027 * 2 ^ 59
def prefixEnd_7121027 : Nat := 4983230072969 + 3 ^ 40 * 7121027 * 2
def baseEnd_7121027 : Nat := 3656509604644415682813499

theorem tailTrace_7121027 : CollatzResearch.WordTrace tailWord_7121027 prefixEnd_7121027 3656509604644415682813499 := by
  unfold tailWord_7121027
  simp only [CollatzResearch.WordTrace]
  refine ⟨259725191972742828432105335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173150127981828552288070223 259725191972742828432105335)
  ·
    refine ⟨389587787959114242648158003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259725191972742828432105335 389587787959114242648158003)
    ·
      refine ⟨584381681938671363972237005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389587787959114242648158003 584381681938671363972237005)
      ·
        refine ⟨219143130727001761489588877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 584381681938671363972237005 219143130727001761489588877)
        ·
          refine ⟨82178674022625660558595829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219143130727001761489588877 82178674022625660558595829)
          ·
            refine ⟨7704250689621155677368359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82178674022625660558595829 7704250689621155677368359)
            ·
              refine ⟨11556376034431733516052539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7704250689621155677368359 11556376034431733516052539)
              ·
                refine ⟨17334564051647600274078809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11556376034431733516052539 17334564051647600274078809)
                ·
                  refine ⟨13000923038735700205559107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17334564051647600274078809 13000923038735700205559107)
                  ·
                    refine ⟨19501384558103550308338661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13000923038735700205559107 19501384558103550308338661)
                    ·
                      refine ⟨3656509604644415682813499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19501384558103550308338661 3656509604644415682813499)
                      ·
                        rfl

theorem cell23_7121027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 1, 4].length) (baseStart_7121027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121027 prefixEnd_7121027 := by exact prefixLift 7121027
  have htrace : WordTrace (prefixWord ++ tailWord_7121027) baseStart_7121027 baseEnd_7121027 := by
    simpa [prefixWord, tailWord_7121027, baseEnd_7121027] using wordTrace_append hprefix tailTrace_7121027
  have hstable : (prefixWord ++ tailWord_7121027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121027).length < 2 ^ (prefixWord ++ tailWord_7121027).sum := by decide
  have hdescent : baseEnd_7121027 < baseStart_7121027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121033 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 8]
def baseStart_7121033 : Nat := 118140960795 + 7121033 * 2 ^ 59
def prefixEnd_7121033 : Nat := 4983230072969 + 3 ^ 40 * 7121033 * 2
def baseEnd_7121033 : Nat := 406279187280926962148719

theorem tailTrace_7121033 : CollatzResearch.WordTrace tailWord_7121033 prefixEnd_7121033 406279187280926962148719 := by
  unfold tailWord_7121033
  simp only [CollatzResearch.WordTrace]
  refine ⟨259725410810721091456823753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173150273873814060971215835 259725410810721091456823753)
  ·
    refine ⟨194794058108040818592617815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259725410810721091456823753 194794058108040818592617815)
    ·
      refine ⟨292191087162061227888926723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194794058108040818592617815 292191087162061227888926723)
      ·
        refine ⟨438286630743091841833390085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292191087162061227888926723 438286630743091841833390085)
        ·
          refine ⟨82178743264329720343760641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 438286630743091841833390085 82178743264329720343760641)
          ·
            refine ⟨61634057448247290257820481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82178743264329720343760641 61634057448247290257820481)
            ·
              refine ⟨46225543086185467693365361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61634057448247290257820481 46225543086185467693365361)
              ·
                refine ⟨34669157314639100770024021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46225543086185467693365361 34669157314639100770024021)
                ·
                  refine ⟨406279187280926962148719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34669157314639100770024021 406279187280926962148719)
                  ·
                    rfl

theorem cell23_7121033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 8].length) (baseStart_7121033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121033 prefixEnd_7121033 := by exact prefixLift 7121033
  have htrace : WordTrace (prefixWord ++ tailWord_7121033) baseStart_7121033 baseEnd_7121033 := by
    simpa [prefixWord, tailWord_7121033, baseEnd_7121033] using wordTrace_append hprefix tailTrace_7121033
  have hstable : (prefixWord ++ tailWord_7121033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121033).length < 2 ^ (prefixWord ++ tailWord_7121033).sum := by decide
  have hdescent : baseEnd_7121033 < baseStart_7121033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121087 : List Nat := [1, 1, 2, 2, 2, 2, 1, 5, 2, 3, 2]
def baseStart_7121087 : Nat := 118140960795 + 7121087 * 2 ^ 59
def prefixEnd_7121087 : Nat := 4983230072969 + 3 ^ 40 * 7121087 * 2
def baseEnd_7121087 : Nat := 3656540413483685448063223

theorem tailTrace_7121087 : CollatzResearch.WordTrace tailWord_7121087 prefixEnd_7121087 3656540413483685448063223 := by
  unfold tailWord_7121087
  simp only [CollatzResearch.WordTrace]
  refine ⟨259727380352525458679289515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173151586901683639119526343 259727380352525458679289515)
  ·
    refine ⟨389591070528788188018934273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259727380352525458679289515 389591070528788188018934273)
    ·
      refine ⟨292193302896591141014200705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389591070528788188018934273 292193302896591141014200705)
      ·
        refine ⟨219144977172443355760650529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292193302896591141014200705 219144977172443355760650529)
        ·
          refine ⟨164358732879332516820487897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219144977172443355760650529 164358732879332516820487897)
          ·
            refine ⟨123269049659499387615365923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164358732879332516820487897 123269049659499387615365923)
            ·
              refine ⟨184903574489249081423048885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123269049659499387615365923 184903574489249081423048885)
              ·
                refine ⟨17334710108367101383410833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184903574489249081423048885 17334710108367101383410833)
                ·
                  refine ⟨13001032581275326037558125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17334710108367101383410833 13001032581275326037558125)
                  ·
                    refine ⟨4875387217978247264084297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13001032581275326037558125 4875387217978247264084297)
                    ·
                      refine ⟨3656540413483685448063223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4875387217978247264084297 3656540413483685448063223)
                      ·
                        rfl

theorem cell23_7121087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 3, 2].length) (baseStart_7121087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121087 prefixEnd_7121087 := by exact prefixLift 7121087
  have htrace : WordTrace (prefixWord ++ tailWord_7121087) baseStart_7121087 baseEnd_7121087 := by
    simpa [prefixWord, tailWord_7121087, baseEnd_7121087] using wordTrace_append hprefix tailTrace_7121087
  have hstable : (prefixWord ++ tailWord_7121087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121087).length < 2 ^ (prefixWord ++ tailWord_7121087).sum := by decide
  have hdescent : baseEnd_7121087 < baseStart_7121087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121120 : List Nat := [2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 5]
def baseStart_7121120 : Nat := 118140960795 + 7121120 * 2 ^ 59
def prefixEnd_7121120 : Nat := 4983230072969 + 3 ^ 40 * 7121120 * 2
def baseEnd_7121120 : Nat := 3656557358345283818950571

theorem tailTrace_7121120 : CollatzResearch.WordTrace tailWord_7121120 prefixEnd_7121120 3656557358345283818950571 := by
  unfold tailWord_7121120
  simp only [CollatzResearch.WordTrace]
  refine ⟨129864291980702952657620407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173152389307603936876827209 129864291980702952657620407)
  ·
    refine ⟨194796437971054428986430611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129864291980702952657620407 194796437971054428986430611)
    ·
      refine ⟨292194656956581643479645917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194796437971054428986430611 292194656956581643479645917)
      ·
        refine ⟨109572996358718116304867219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292194656956581643479645917 109572996358718116304867219)
        ·
          refine ⟨164359494538077174457300829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109572996358718116304867219 164359494538077174457300829)
          ·
            refine ⟨61634810451778940421487811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164359494538077174457300829 61634810451778940421487811)
            ·
              refine ⟨92452215677668410632231717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61634810451778940421487811 92452215677668410632231717)
              ·
                refine ⟨17334790439562826993543447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92452215677668410632231717 17334790439562826993543447)
                ·
                  refine ⟨26002185659344240490315171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17334790439562826993543447 26002185659344240490315171)
                  ·
                    refine ⟨39003278489016360735472757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26002185659344240490315171 39003278489016360735472757)
                    ·
                      refine ⟨3656557358345283818950571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39003278489016360735472757 3656557358345283818950571)
                      ·
                        rfl

theorem cell23_7121120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_7121120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121120 prefixEnd_7121120 := by exact prefixLift 7121120
  have htrace : WordTrace (prefixWord ++ tailWord_7121120) baseStart_7121120 baseEnd_7121120 := by
    simpa [prefixWord, tailWord_7121120, baseEnd_7121120] using wordTrace_append hprefix tailTrace_7121120
  have hstable : (prefixWord ++ tailWord_7121120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121120).length < 2 ^ (prefixWord ++ tailWord_7121120).sum := by decide
  have hdescent : baseEnd_7121120 < baseStart_7121120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121130 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_7121130 : Nat := 118140960795 + 7121130 * 2 ^ 59
def prefixEnd_7121130 : Nat := 4983230072969 + 3 ^ 40 * 7121130 * 2
def baseEnd_7121130 : Nat := 3656562493151828779825525

theorem tailTrace_7121130 : CollatzResearch.WordTrace tailWord_7121130 prefixEnd_7121130 3656562493151828779825525 := by
  unfold tailWord_7121130
  simp only [CollatzResearch.WordTrace]
  refine ⟨64932237172842419255776211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173152632460913118015403229 64932237172842419255776211)
  ·
    refine ⟨97398355759263628883664317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64932237172842419255776211 97398355759263628883664317)
    ·
      refine ⟨36524383409723860831374119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97398355759263628883664317 36524383409723860831374119)
      ·
        refine ⟨54786575114585791247061179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36524383409723860831374119 54786575114585791247061179)
        ·
          refine ⟨82179862671878686870591769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54786575114585791247061179 82179862671878686870591769)
          ·
            refine ⟨61634897003909015152943827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82179862671878686870591769 61634897003909015152943827)
            ·
              refine ⟨92452345505863522729415741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61634897003909015152943827 92452345505863522729415741)
              ·
                refine ⟨34669629564698821023530903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92452345505863522729415741 34669629564698821023530903)
                ·
                  refine ⟨52004444347048231535296355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34669629564698821023530903 52004444347048231535296355)
                  ·
                    refine ⟨78006666520572347302944533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52004444347048231535296355 78006666520572347302944533)
                    ·
                      refine ⟨3656562493151828779825525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78006666520572347302944533 3656562493151828779825525)
                      ·
                        rfl

theorem cell23_7121130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_7121130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121130 prefixEnd_7121130 := by exact prefixLift 7121130
  have htrace : WordTrace (prefixWord ++ tailWord_7121130) baseStart_7121130 baseEnd_7121130 := by
    simpa [prefixWord, tailWord_7121130, baseEnd_7121130] using wordTrace_append hprefix tailTrace_7121130
  have hstable : (prefixWord ++ tailWord_7121130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121130).length < 2 ^ (prefixWord ++ tailWord_7121130).sum := by decide
  have hdescent : baseEnd_7121130 < baseStart_7121130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121134 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 5, 2, 2]
def baseStart_7121134 : Nat := 118140960795 + 7121134 * 2 ^ 59
def prefixEnd_7121134 : Nat := 4983230072969 + 3 ^ 40 * 7121134 * 2
def baseEnd_7121134 : Nat := 3656564547074446764175507

theorem tailTrace_7121134 : CollatzResearch.WordTrace tailWord_7121134 prefixEnd_7121134 3656564547074446764175507 := by
  unfold tailWord_7121134
  simp only [CollatzResearch.WordTrace]
  refine ⟨32466136822919398213281307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173152729722236790470833637 32466136822919398213281307)
  ·
    refine ⟨48699205234379097319921961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32466136822919398213281307 48699205234379097319921961)
    ·
      refine ⟨36524403925784322989941471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48699205234379097319921961 36524403925784322989941471)
      ·
        refine ⟨54786605888676484484912207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36524403925784322989941471 54786605888676484484912207)
        ·
          refine ⟨82179908833014726727368311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54786605888676484484912207 82179908833014726727368311)
          ·
            refine ⟨123269863249522090091052467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82179908833014726727368311 123269863249522090091052467)
            ·
              refine ⟨184904794874283135136578701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123269863249522090091052467 184904794874283135136578701)
              ·
                refine ⟨69339298077856175676217013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184904794874283135136578701 69339298077856175676217013)
                ·
                  refine ⟨6500559194799016469645345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69339298077856175676217013 6500559194799016469645345)
                  ·
                    refine ⟨4875419396099262352234009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6500559194799016469645345 4875419396099262352234009)
                    ·
                      refine ⟨3656564547074446764175507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4875419396099262352234009 3656564547074446764175507)
                      ·
                        rfl

theorem cell23_7121134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_7121134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121134 prefixEnd_7121134 := by exact prefixLift 7121134
  have htrace : WordTrace (prefixWord ++ tailWord_7121134) baseStart_7121134 baseEnd_7121134 := by
    simpa [prefixWord, tailWord_7121134, baseEnd_7121134] using wordTrace_append hprefix tailTrace_7121134
  have hstable : (prefixWord ++ tailWord_7121134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121134).length < 2 ^ (prefixWord ++ tailWord_7121134).sum := by decide
  have hdescent : baseEnd_7121134 < baseStart_7121134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121151 : List Nat := [1, 1, 2, 2, 1, 4, 2, 5, 1, 2, 2]
def baseStart_7121151 : Nat := 118140960795 + 7121151 * 2 ^ 59
def prefixEnd_7121151 : Nat := 4983230072969 + 3 ^ 40 * 7121151 * 2
def baseEnd_7121151 : Nat := 3656573276245573197662929

theorem tailTrace_7121151 : CollatzResearch.WordTrace tailWord_7121151 prefixEnd_7121151 3656573276245573197662929 := by
  unfold tailWord_7121151
  simp only [CollatzResearch.WordTrace]
  refine ⟨259729714624293597609619307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173153143082862398406412871 259729714624293597609619307)
  ·
    refine ⟨389594571936440396414428961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259729714624293597609619307 389594571936440396414428961)
    ·
      refine ⟨292195928952330297310821721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389594571936440396414428961 292195928952330297310821721)
      ·
        refine ⟨219146946714247722983116291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292195928952330297310821721 219146946714247722983116291)
        ·
          refine ⟨328720420071371584474674437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219146946714247722983116291 328720420071371584474674437)
          ·
            refine ⟨61635078763382172089001457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 328720420071371584474674437 61635078763382172089001457)
            ·
              refine ⟨46226309072536629066751093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61635078763382172089001457 46226309072536629066751093)
              ·
                refine ⟨4333716475550308975007915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46226309072536629066751093 4333716475550308975007915)
                ·
                  refine ⟨6500574713325463462511873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4333716475550308975007915 6500574713325463462511873)
                  ·
                    refine ⟨4875431034994097596883905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6500574713325463462511873 4875431034994097596883905)
                    ·
                      refine ⟨3656573276245573197662929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4875431034994097596883905 3656573276245573197662929)
                      ·
                        rfl

theorem cell23_7121151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 1, 2, 2].length) (baseStart_7121151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121151 prefixEnd_7121151 := by exact prefixLift 7121151
  have htrace : WordTrace (prefixWord ++ tailWord_7121151) baseStart_7121151 baseEnd_7121151 := by
    simpa [prefixWord, tailWord_7121151, baseEnd_7121151] using wordTrace_append hprefix tailTrace_7121151
  have hstable : (prefixWord ++ tailWord_7121151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121151).length < 2 ^ (prefixWord ++ tailWord_7121151).sum := by decide
  have hdescent : baseEnd_7121151 < baseStart_7121151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121154 : List Nat := [3, 4, 1, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_7121154 : Nat := 118140960795 + 7121154 * 2 ^ 59
def prefixEnd_7121154 : Nat := 4983230072969 + 3 ^ 40 * 7121154 * 2
def baseEnd_7121154 : Nat := 3656574816687536685925415

theorem tailTrace_7121154 : CollatzResearch.WordTrace tailWord_7121154 prefixEnd_7121154 3656574816687536685925415 := by
  unfold tailWord_7121154
  simp only [CollatzResearch.WordTrace]
  refine ⟨64932456010820682280494629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173153216028855152747985677 64932456010820682280494629)
  ·
    refine ⟨12174835502028877927592743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64932456010820682280494629 12174835502028877927592743)
    ·
      refine ⟨18262253253043316891389115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12174835502028877927592743 18262253253043316891389115)
      ·
        refine ⟨27393379879564975337083673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18262253253043316891389115 27393379879564975337083673)
        ·
          refine ⟨20545034909673731502812755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27393379879564975337083673 20545034909673731502812755)
          ·
            refine ⟨30817552364510597254219133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20545034909673731502812755 30817552364510597254219133)
            ·
              refine ⟨11556582136691473970332175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30817552364510597254219133 11556582136691473970332175)
              ·
                refine ⟨17334873205037210955498263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11556582136691473970332175 17334873205037210955498263)
                ·
                  refine ⟨26002309807555816433247395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17334873205037210955498263 26002309807555816433247395)
                  ·
                    refine ⟨39003464711333724649871093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26002309807555816433247395 39003464711333724649871093)
                    ·
                      refine ⟨3656574816687536685925415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39003464711333724649871093 3656574816687536685925415)
                      ·
                        rfl

theorem cell23_7121154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_7121154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121154 prefixEnd_7121154 := by exact prefixLift 7121154
  have htrace : WordTrace (prefixWord ++ tailWord_7121154) baseStart_7121154 baseEnd_7121154 := by
    simpa [prefixWord, tailWord_7121154, baseEnd_7121154] using wordTrace_append hprefix tailTrace_7121154
  have hstable : (prefixWord ++ tailWord_7121154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121154).length < 2 ^ (prefixWord ++ tailWord_7121154).sum := by decide
  have hdescent : baseEnd_7121154 < baseStart_7121154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121167 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 4, 1, 3]
def baseStart_7121167 : Nat := 118140960795 + 7121167 * 2 ^ 59
def prefixEnd_7121167 : Nat := 4983230072969 + 3 ^ 40 * 7121167 * 2
def baseEnd_7121167 : Nat := 3656581491936045135062855

theorem tailTrace_7121167 : CollatzResearch.WordTrace tailWord_7121167 prefixEnd_7121167 3656581491936045135062855 := by
  unfold tailWord_7121167
  simp only [CollatzResearch.WordTrace]
  refine ⟨259730298192235632342201755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173153532128157088228134503 259730298192235632342201755)
  ·
    refine ⟨389595447288353448513302633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259730298192235632342201755 389595447288353448513302633)
    ·
      refine ⟨292196585466265086384976975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389595447288353448513302633 292196585466265086384976975)
      ·
        refine ⟨438294878199397629577465463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292196585466265086384976975 438294878199397629577465463)
        ·
          refine ⟨657442317299096444366198195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438294878199397629577465463 657442317299096444366198195)
          ·
            refine ⟨986163475948644666549297293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657442317299096444366198195 986163475948644666549297293)
            ·
              refine ⟨369811303480741749955986485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 986163475948644666549297293 369811303480741749955986485)
              ·
                refine ⟨34669809701319539058373733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 369811303480741749955986485 34669809701319539058373733)
                ·
                  refine ⟨6500589318997413573445075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34669809701319539058373733 6500589318997413573445075)
                  ·
                    refine ⟨9750883978496120360167613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6500589318997413573445075 9750883978496120360167613)
                    ·
                      refine ⟨3656581491936045135062855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9750883978496120360167613 3656581491936045135062855)
                      ·
                        rfl

theorem cell23_7121167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4, 1, 3].length) (baseStart_7121167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121167 prefixEnd_7121167 := by exact prefixLift 7121167
  have htrace : WordTrace (prefixWord ++ tailWord_7121167) baseStart_7121167 baseEnd_7121167 := by
    simpa [prefixWord, tailWord_7121167, baseEnd_7121167] using wordTrace_append hprefix tailTrace_7121167
  have hstable : (prefixWord ++ tailWord_7121167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121167).length < 2 ^ (prefixWord ++ tailWord_7121167).sum := by decide
  have hdescent : baseEnd_7121167 < baseStart_7121167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121180 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_7121180 : Nat := 118140960795 + 7121180 * 2 ^ 59
def prefixEnd_7121180 : Nat := 4983230072969 + 3 ^ 40 * 7121180 * 2
def baseEnd_7121180 : Nat := 3656588167184553584200295

theorem tailTrace_7121180 : CollatzResearch.WordTrace tailWord_7121180 prefixEnd_7121180 3656588167184553584200295 := by
  unfold tailWord_7121180
  simp only [CollatzResearch.WordTrace]
  refine ⟨129865386170594267781212497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173153848227459023708283329 129865386170594267781212497)
  ·
    refine ⟨97399039627945700835909373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129865386170594267781212497 97399039627945700835909373)
    ·
      refine ⟨36524639860479637813466015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97399039627945700835909373 36524639860479637813466015)
      ·
        refine ⟨54786959790719456720199023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36524639860479637813466015 54786959790719456720199023)
        ·
          refine ⟨82180439686079185080298535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54786959790719456720199023 82180439686079185080298535)
          ·
            refine ⟨123270659529118777620447803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82180439686079185080298535 123270659529118777620447803)
            ·
              refine ⟨184905989293678166430671705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123270659529118777620447803 184905989293678166430671705)
              ·
                refine ⟨138679491970258624823003779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184905989293678166430671705 138679491970258624823003779)
                ·
                  refine ⟨208019237955387937234505669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138679491970258624823003779 208019237955387937234505669)
                  ·
                    refine ⟨39003607116635238231469813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 208019237955387937234505669 39003607116635238231469813)
                    ·
                      refine ⟨3656588167184553584200295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39003607116635238231469813 3656588167184553584200295)
                      ·
                        rfl

theorem cell23_7121180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_7121180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121180 prefixEnd_7121180 := by exact prefixLift 7121180
  have htrace : WordTrace (prefixWord ++ tailWord_7121180) baseStart_7121180 baseEnd_7121180 := by
    simpa [prefixWord, tailWord_7121180, baseEnd_7121180] using wordTrace_append hprefix tailTrace_7121180
  have hstable : (prefixWord ++ tailWord_7121180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121180).length < 2 ^ (prefixWord ++ tailWord_7121180).sum := by decide
  have hdescent : baseEnd_7121180 < baseStart_7121180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121184 : List Nat := [2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 3]
def baseStart_7121184 : Nat := 118140960795 + 7121184 * 2 ^ 59
def prefixEnd_7121184 : Nat := 4983230072969 + 3 ^ 40 * 7121184 * 2
def baseEnd_7121184 : Nat := 3656590221107171568550277

theorem tailTrace_7121184 : CollatzResearch.WordTrace tailWord_7121184 prefixEnd_7121184 3656590221107171568550277 := by
  unfold tailWord_7121184
  simp only [CollatzResearch.WordTrace]
  refine ⟨129865459116587022122785303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173153945488782696163713737 129865459116587022122785303)
  ·
    refine ⟨194798188674880533184177955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129865459116587022122785303 194798188674880533184177955)
    ·
      refine ⟨292197283012320799776266933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194798188674880533184177955 292197283012320799776266933)
      ·
        refine ⟨27393495282405074979025025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 292197283012320799776266933 27393495282405074979025025)
        ·
          refine ⟨20545121461803806234268769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27393495282405074979025025 20545121461803806234268769)
          ·
            refine ⟨15408841096352854675701577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20545121461803806234268769 15408841096352854675701577)
            ·
              refine ⟨11556630822264641006776183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15408841096352854675701577 11556630822264641006776183)
              ·
                refine ⟨17334946233396961510164275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11556630822264641006776183 17334946233396961510164275)
                ·
                  refine ⟨26002419350095442265246413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17334946233396961510164275 26002419350095442265246413)
                  ·
                    refine ⟨9750907256285790849467405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26002419350095442265246413 9750907256285790849467405)
                    ·
                      refine ⟨3656590221107171568550277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9750907256285790849467405 3656590221107171568550277)
                      ·
                        rfl

theorem cell23_7121184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_7121184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121184 prefixEnd_7121184 := by exact prefixLift 7121184
  have htrace : WordTrace (prefixWord ++ tailWord_7121184) baseStart_7121184 baseEnd_7121184 := by
    simpa [prefixWord, tailWord_7121184, baseEnd_7121184] using wordTrace_append hprefix tailTrace_7121184
  have hstable : (prefixWord ++ tailWord_7121184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121184).length < 2 ^ (prefixWord ++ tailWord_7121184).sum := by decide
  have hdescent : baseEnd_7121184 < baseStart_7121184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121264 : List Nat := [2, 1, 1, 1, 4, 3, 3, 3, 5]
def baseStart_7121264 : Nat := 118140960795 + 7121264 * 2 ^ 59
def prefixEnd_7121264 : Nat := 4983230072969 + 3 ^ 40 * 7121264 * 2
def baseEnd_7121264 : Nat := 406292366617725695061101

theorem tailTrace_7121264 : CollatzResearch.WordTrace tailWord_7121264 prefixEnd_7121264 406292366617725695061101 := by
  unfold tailWord_7121264
  simp only [CollatzResearch.WordTrace]
  refine ⟨129866918036442108954241423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173155890715256145272321897 129866918036442108954241423)
  ·
    refine ⟨194800377054663163431362135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129866918036442108954241423 194800377054663163431362135)
    ·
      refine ⟨292200565581994745147043203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194800377054663163431362135 292200565581994745147043203)
      ·
        refine ⟨438300848372992117720564805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292200565581994745147043203 438300848372992117720564805)
        ·
          refine ⟨82181409069936022072605901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 438300848372992117720564805 82181409069936022072605901)
          ·
            refine ⟨30818028401226008277227213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82181409069936022072605901 30818028401226008277227213)
            ·
              refine ⟨11556760650459753103960205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30818028401226008277227213 11556760650459753103960205)
              ·
                refine ⟨4333785243922407413985077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11556760650459753103960205 4333785243922407413985077)
                ·
                  refine ⟨406292366617725695061101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4333785243922407413985077 406292366617725695061101)
                  ·
                    rfl

theorem cell23_7121264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 5].length) (baseStart_7121264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121264 prefixEnd_7121264 := by exact prefixLift 7121264
  have htrace : WordTrace (prefixWord ++ tailWord_7121264) baseStart_7121264 baseEnd_7121264 := by
    simpa [prefixWord, tailWord_7121264, baseEnd_7121264] using wordTrace_append hprefix tailTrace_7121264
  have hstable : (prefixWord ++ tailWord_7121264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121264).length < 2 ^ (prefixWord ++ tailWord_7121264).sum := by decide
  have hdescent : baseEnd_7121264 < baseStart_7121264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121277 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 4, 5]
def baseStart_7121277 : Nat := 118140960795 + 7121277 * 2 ^ 59
def prefixEnd_7121277 : Nat := 4983230072969 + 3 ^ 40 * 7121277 * 2
def baseEnd_7121277 : Nat := 1218879324936013234895783

theorem tailTrace_7121277 : CollatzResearch.WordTrace tailWord_7121277 prefixEnd_7121277 1218879324936013234895783 := by
  unfold tailWord_7121277
  simp only [CollatzResearch.WordTrace]
  refine ⟨259734310221837121128706085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173156206814558080752470723 259734310221837121128706085)
  ·
    refine ⟨48700183166594460211632391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259734310221837121128706085 48700183166594460211632391)
    ·
      refine ⟨73050274749891690317448587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48700183166594460211632391 73050274749891690317448587)
      ·
        refine ⟨109575412124837535476172881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73050274749891690317448587 109575412124837535476172881)
        ·
          refine ⟨82181559093628151607129661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109575412124837535476172881 82181559093628151607129661)
          ·
            refine ⟨30818084660110556852673623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82181559093628151607129661 30818084660110556852673623)
            ·
              refine ⟨46227126990165835279010435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30818084660110556852673623 46227126990165835279010435)
              ·
                refine ⟨69340690485248752918515653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46227126990165835279010435 69340690485248752918515653)
                ·
                  refine ⟨13001379465984141172221685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69340690485248752918515653 13001379465984141172221685)
                  ·
                    refine ⟨1218879324936013234895783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13001379465984141172221685 1218879324936013234895783)
                    ·
                      rfl

theorem cell23_7121277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_7121277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121277 prefixEnd_7121277 := by exact prefixLift 7121277
  have htrace : WordTrace (prefixWord ++ tailWord_7121277) baseStart_7121277 baseEnd_7121277 := by
    simpa [prefixWord, tailWord_7121277, baseEnd_7121277] using wordTrace_append hprefix tailTrace_7121277
  have hstable : (prefixWord ++ tailWord_7121277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121277).length < 2 ^ (prefixWord ++ tailWord_7121277).sum := by decide
  have hdescent : baseEnd_7121277 < baseStart_7121277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121280 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 8]
def baseStart_7121280 : Nat := 118140960795 + 7121280 * 2 ^ 59
def prefixEnd_7121280 : Nat := 4983230072969 + 3 ^ 40 * 7121280 * 2
def baseEnd_7121280 : Nat := 3656639515250003192949835

theorem tailTrace_7121280 : CollatzResearch.WordTrace tailWord_7121280 prefixEnd_7121280 3656639515250003192949835 := by
  unfold tailWord_7121280
  simp only [CollatzResearch.WordTrace]
  refine ⟨129867209820413126320532647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173156279760550835094043529 129867209820413126320532647)
  ·
    refine ⟨194800814730619689480798971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129867209820413126320532647 194800814730619689480798971)
    ·
      refine ⟨292201222095929534221198457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194800814730619689480798971 292201222095929534221198457)
      ·
        refine ⟨219150916571947150665898843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292201222095929534221198457 219150916571947150665898843)
        ·
          refine ⟨328726374857920725998848265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219150916571947150665898843 328726374857920725998848265)
          ·
            refine ⟨246544781143440544499136199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328726374857920725998848265 246544781143440544499136199)
            ·
              refine ⟨369817171715160816748704299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246544781143440544499136199 369817171715160816748704299)
              ·
                refine ⟨554725757572741225123056449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369817171715160816748704299 554725757572741225123056449)
                ·
                  refine ⟨416044318179555918842292337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 554725757572741225123056449 416044318179555918842292337)
                  ·
                    refine ⟨312033238634666939131719253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 416044318179555918842292337 312033238634666939131719253)
                    ·
                      refine ⟨3656639515250003192949835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 312033238634666939131719253 3656639515250003192949835)
                      ·
                        rfl

theorem cell23_7121280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_7121280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121280 prefixEnd_7121280 := by exact prefixLift 7121280
  have htrace : WordTrace (prefixWord ++ tailWord_7121280) baseStart_7121280 baseEnd_7121280 := by
    simpa [prefixWord, tailWord_7121280, baseEnd_7121280] using wordTrace_append hprefix tailTrace_7121280
  have hstable : (prefixWord ++ tailWord_7121280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121280).length < 2 ^ (prefixWord ++ tailWord_7121280).sum := by decide
  have hdescent : baseEnd_7121280 < baseStart_7121280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121284 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 2, 5, 2]
def baseStart_7121284 : Nat := 118140960795 + 7121284 * 2 ^ 59
def prefixEnd_7121284 : Nat := 4983230072969 + 3 ^ 40 * 7121284 * 2
def baseEnd_7121284 : Nat := 3656641569172621177299817

theorem tailTrace_7121284 : CollatzResearch.WordTrace tailWord_7121284 prefixEnd_7121284 3656641569172621177299817 := by
  unfold tailWord_7121284
  simp only [CollatzResearch.WordTrace]
  refine ⟨129867282766405880662105453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173156377021874507549473937 129867282766405880662105453)
  ·
    refine ⟨48700231037402205248289545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129867282766405880662105453 48700231037402205248289545)
    ·
      refine ⟨36525173278051653936217159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48700231037402205248289545 36525173278051653936217159)
      ·
        refine ⟨54787759917077480904325739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36525173278051653936217159 54787759917077480904325739)
        ·
          refine ⟨82181639875616221356488609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54787759917077480904325739 82181639875616221356488609)
          ·
            refine ⟨61636229906712166017366457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82181639875616221356488609 61636229906712166017366457)
            ·
              refine ⟨46227172430034124513024843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61636229906712166017366457 46227172430034124513024843)
              ·
                refine ⟨69340758645051186769537265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46227172430034124513024843 69340758645051186769537265)
                ·
                  refine ⟨52005568983788390077152949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69340758645051186769537265 52005568983788390077152949)
                  ·
                    refine ⟨4875522092230161569733089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52005568983788390077152949 4875522092230161569733089)
                    ·
                      refine ⟨3656641569172621177299817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4875522092230161569733089 3656641569172621177299817)
                      ·
                        rfl

theorem cell23_7121284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_7121284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121284 prefixEnd_7121284 := by exact prefixLift 7121284
  have htrace : WordTrace (prefixWord ++ tailWord_7121284) baseStart_7121284 baseEnd_7121284 := by
    simpa [prefixWord, tailWord_7121284, baseEnd_7121284] using wordTrace_append hprefix tailTrace_7121284
  have hstable : (prefixWord ++ tailWord_7121284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121284).length < 2 ^ (prefixWord ++ tailWord_7121284).sum := by decide
  have hdescent : baseEnd_7121284 < baseStart_7121284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121287 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_7121287 : Nat := 118140960795 + 7121287 * 2 ^ 59
def prefixEnd_7121287 : Nat := 4983230072969 + 3 ^ 40 * 7121287 * 2
def baseEnd_7121287 : Nat := 3656643109614584665562303

theorem tailTrace_7121287 : CollatzResearch.WordTrace tailWord_7121287 prefixEnd_7121287 3656643109614584665562303 := by
  unfold tailWord_7121287
  simp only [CollatzResearch.WordTrace]
  refine ⟨259734674951800892836570115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173156449967867261891046743 259734674951800892836570115)
  ·
    refine ⟨389602012427701339254855173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259734674951800892836570115 389602012427701339254855173)
    ·
      refine ⟨73050377330194001110285345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389602012427701339254855173 73050377330194001110285345)
      ·
        refine ⟨54787782997645500832714009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73050377330194001110285345 54787782997645500832714009)
        ·
          refine ⟨41090837248234125624535507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54787782997645500832714009 41090837248234125624535507)
          ·
            refine ⟨61636255872351188436803261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41090837248234125624535507 61636255872351188436803261)
            ·
              refine ⟨23113595952131695663801223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61636255872351188436803261 23113595952131695663801223)
              ·
                refine ⟨34670393928197543495701835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23113595952131695663801223 34670393928197543495701835)
                ·
                  refine ⟨52005590892296315243552753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34670393928197543495701835 52005590892296315243552753)
                  ·
                    refine ⟨39004193169222236432664565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52005590892296315243552753 39004193169222236432664565)
                    ·
                      refine ⟨3656643109614584665562303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39004193169222236432664565 3656643109614584665562303)
                      ·
                        rfl

theorem cell23_7121287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_7121287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121287 prefixEnd_7121287 := by exact prefixLift 7121287
  have htrace : WordTrace (prefixWord ++ tailWord_7121287) baseStart_7121287 baseEnd_7121287 := by
    simpa [prefixWord, tailWord_7121287, baseEnd_7121287] using wordTrace_append hprefix tailTrace_7121287
  have hstable : (prefixWord ++ tailWord_7121287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121287).length < 2 ^ (prefixWord ++ tailWord_7121287).sum := by decide
  have hdescent : baseEnd_7121287 < baseStart_7121287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121332 : List Nat := [2, 5, 2, 2, 1, 2, 2, 2, 5]
def baseStart_7121332 : Nat := 118140960795 + 7121332 * 2 ^ 59
def prefixEnd_7121332 : Nat := 4983230072969 + 3 ^ 40 * 7121332 * 2
def baseEnd_7121332 : Nat := 406296246249337443277733

theorem tailTrace_7121332 : CollatzResearch.WordTrace tailWord_7121332 prefixEnd_7121332 406296246249337443277733 := by
  unfold tailWord_7121332
  simp only [CollatzResearch.WordTrace]
  refine ⟨129868158118318932760979125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173157544157758577014638833 129868158118318932760979125)
  ·
    refine ⟨12175139823592399946341793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129868158118318932760979125 12175139823592399946341793)
    ·
      refine ⟨9131354867694299959756345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12175139823592399946341793 9131354867694299959756345)
      ·
        refine ⟨6848516150770724969817259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9131354867694299959756345 6848516150770724969817259)
        ·
          refine ⟨10272774226156087454725889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6848516150770724969817259 10272774226156087454725889)
          ·
            refine ⟨7704580669617065591044417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10272774226156087454725889 7704580669617065591044417)
            ·
              refine ⟨5778435502212799193283313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7704580669617065591044417 5778435502212799193283313)
              ·
                refine ⟨4333826626659599394962485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5778435502212799193283313 4333826626659599394962485)
                ·
                  refine ⟨406296246249337443277733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4333826626659599394962485 406296246249337443277733)
                  ·
                    rfl

theorem cell23_7121332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_7121332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121332 prefixEnd_7121332 := by exact prefixLift 7121332
  have htrace : WordTrace (prefixWord ++ tailWord_7121332) baseStart_7121332 baseEnd_7121332 := by
    simpa [prefixWord, tailWord_7121332, baseEnd_7121332] using wordTrace_append hprefix tailTrace_7121332
  have hstable : (prefixWord ++ tailWord_7121332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121332).length < 2 ^ (prefixWord ++ tailWord_7121332).sum := by decide
  have hdescent : baseEnd_7121332 < baseStart_7121332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121347 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 3]
def baseStart_7121347 : Nat := 118140960795 + 7121347 * 2 ^ 59
def prefixEnd_7121347 : Nat := 4983230072969 + 3 ^ 40 * 7121347 * 2
def baseEnd_7121347 : Nat := 3656673918453854430812027

theorem tailTrace_7121347 : CollatzResearch.WordTrace tailWord_7121347 prefixEnd_7121347 3656673918453854430812027 := by
  unfold tailWord_7121347
  simp only [CollatzResearch.WordTrace]
  refine ⟨259736863331583523083754295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173157908887722348722502863 259736863331583523083754295)
  ·
    refine ⟨389605294997375284625631443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259736863331583523083754295 389605294997375284625631443)
    ·
      refine ⟨584407942496062926938447165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389605294997375284625631443 584407942496062926938447165)
      ·
        refine ⟨219152978436023597601917687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 584407942496062926938447165 219152978436023597601917687)
        ·
          refine ⟨328729467654035396402876531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219152978436023597601917687 328729467654035396402876531)
          ·
            refine ⟨493094201481053094604314797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328729467654035396402876531 493094201481053094604314797)
            ·
              refine ⟨184910325555394910476618049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 493094201481053094604314797 184910325555394910476618049)
              ·
                refine ⟨138682744166546182857463537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184910325555394910476618049 138682744166546182857463537)
                ·
                  refine ⟨104012058124909637143097653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138682744166546182857463537 104012058124909637143097653)
                  ·
                    refine ⟨9751130449210278482165405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104012058124909637143097653 9751130449210278482165405)
                    ·
                      refine ⟨3656673918453854430812027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9751130449210278482165405 3656673918453854430812027)
                      ·
                        rfl

theorem cell23_7121347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_7121347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121347 prefixEnd_7121347 := by exact prefixLift 7121347
  have htrace : WordTrace (prefixWord ++ tailWord_7121347) baseStart_7121347 baseEnd_7121347 := by
    simpa [prefixWord, tailWord_7121347, baseEnd_7121347] using wordTrace_append hprefix tailTrace_7121347
  have hstable : (prefixWord ++ tailWord_7121347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121347).length < 2 ^ (prefixWord ++ tailWord_7121347).sum := by decide
  have hdescent : baseEnd_7121347 < baseStart_7121347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121348 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_7121348 : Nat := 118140960795 + 7121348 * 2 ^ 59
def prefixEnd_7121348 : Nat := 4983230072969 + 3 ^ 40 * 7121348 * 2
def baseEnd_7121348 : Nat := 3656674431934508926899523

theorem tailTrace_7121348 : CollatzResearch.WordTrace tailWord_7121348 prefixEnd_7121348 3656674431934508926899523 := by
  unfold tailWord_7121348
  simp only [CollatzResearch.WordTrace]
  refine ⟨129868449902289950127270349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173157933203053266836360465 129868449902289950127270349)
  ·
    refine ⟨48700668713358731297726381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129868449902289950127270349 48700668713358731297726381)
    ·
      refine ⟨18262750767509524236647393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48700668713358731297726381 18262750767509524236647393)
      ·
        refine ⟨13697063075632143177485545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18262750767509524236647393 13697063075632143177485545)
        ·
          refine ⟨10272797306724107383114159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13697063075632143177485545 10272797306724107383114159)
          ·
            refine ⟨15409195960086161074671239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10272797306724107383114159 15409195960086161074671239)
            ·
              refine ⟨23113793940129241612006859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15409195960086161074671239 23113793940129241612006859)
              ·
                refine ⟨34670690910193862418010289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23113793940129241612006859 34670690910193862418010289)
                ·
                  refine ⟨26003018182645396813507717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34670690910193862418010289 26003018182645396813507717)
                  ·
                    refine ⟨4875565909246011902532697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26003018182645396813507717 4875565909246011902532697)
                    ·
                      refine ⟨3656674431934508926899523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4875565909246011902532697 3656674431934508926899523)
                      ·
                        rfl

theorem cell23_7121348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_7121348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121348 prefixEnd_7121348 := by exact prefixLift 7121348
  have htrace : WordTrace (prefixWord ++ tailWord_7121348) baseStart_7121348 baseEnd_7121348 := by
    simpa [prefixWord, tailWord_7121348, baseEnd_7121348] using wordTrace_append hprefix tailTrace_7121348
  have hstable : (prefixWord ++ tailWord_7121348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121348).length < 2 ^ (prefixWord ++ tailWord_7121348).sum := by decide
  have hdescent : baseEnd_7121348 < baseStart_7121348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121398 : List Nat := [5, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_7121398 : Nat := 118140960795 + 7121398 * 2 ^ 59
def prefixEnd_7121398 : Nat := 4983230072969 + 3 ^ 40 * 7121398 * 2
def baseEnd_7121398 : Nat := 3656700105967233731274293

theorem tailTrace_7121398 : CollatzResearch.WordTrace tailWord_7121398 prefixEnd_7121398 3656700105967233731274293 := by
  unfold tailWord_7121398
  simp only [CollatzResearch.WordTrace]
  refine ⟨16233670215899922424616303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173159148969599172529240565 16233670215899922424616303)
  ·
    refine ⟨24350505323849883636924455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16233670215899922424616303 24350505323849883636924455)
    ·
      refine ⟨36525757985774825455386683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24350505323849883636924455 36525757985774825455386683)
      ·
        refine ⟨54788636978662238183080025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36525757985774825455386683 54788636978662238183080025)
        ·
          refine ⟨41091477733996678637310019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54788636978662238183080025 41091477733996678637310019)
          ·
            refine ⟨61637216600995017955965029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41091477733996678637310019 61637216600995017955965029)
            ·
              refine ⟨11556978112686565866743443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61637216600995017955965029 11556978112686565866743443)
              ·
                refine ⟨17335467169029848800115165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11556978112686565866743443 17335467169029848800115165)
                ·
                  refine ⟨6500800188386193300043187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17335467169029848800115165 6500800188386193300043187)
                  ·
                    refine ⟨9751200282579289950064781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6500800188386193300043187 9751200282579289950064781)
                    ·
                      refine ⟨3656700105967233731274293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9751200282579289950064781 3656700105967233731274293)
                      ·
                        rfl

theorem cell23_7121398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_7121398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121398 prefixEnd_7121398 := by exact prefixLift 7121398
  have htrace : WordTrace (prefixWord ++ tailWord_7121398) baseStart_7121398 baseEnd_7121398 := by
    simpa [prefixWord, tailWord_7121398, baseEnd_7121398] using wordTrace_append hprefix tailTrace_7121398
  have hstable : (prefixWord ++ tailWord_7121398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121398).length < 2 ^ (prefixWord ++ tailWord_7121398).sum := by decide
  have hdescent : baseEnd_7121398 < baseStart_7121398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121427 : List Nat := [1, 1, 1, 2, 1, 5, 3, 9]
def baseStart_7121427 : Nat := 118140960795 + 7121427 * 2 ^ 59
def prefixEnd_7121427 : Nat := 4983230072969 + 3 ^ 40 * 7121427 * 2
def baseEnd_7121427 : Nat := 135433888774304226585617

theorem tailTrace_7121427 : CollatzResearch.WordTrace tailWord_7121427 prefixEnd_7121427 135433888774304226585617 := by
  unfold tailWord_7121427
  simp only [CollatzResearch.WordTrace]
  refine ⟨259739781171293696746666535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173159854114195797831111023 259739781171293696746666535)
  ·
    refine ⟨389609671756940545119999803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259739781171293696746666535 389609671756940545119999803)
    ·
      refine ⟨584414507635410817679999705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389609671756940545119999803 584414507635410817679999705)
      ·
        refine ⟨438310880726558113259999779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 584414507635410817679999705 438310880726558113259999779)
        ·
          refine ⟨657466321089837169889999669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438310880726558113259999779 657466321089837169889999669)
          ·
            refine ⟨61637467602172234677187469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 657466321089837169889999669 61637467602172234677187469)
            ·
              refine ⟨23114050350814588003945301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61637467602172234677187469 23114050350814588003945301)
              ·
                refine ⟨135433888774304226585617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23114050350814588003945301 135433888774304226585617)
                ·
                  rfl

theorem cell23_7121427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 9].length) (baseStart_7121427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121427 prefixEnd_7121427 := by exact prefixLift 7121427
  have htrace : WordTrace (prefixWord ++ tailWord_7121427) baseStart_7121427 baseEnd_7121427 := by
    simpa [prefixWord, tailWord_7121427, baseEnd_7121427] using wordTrace_append hprefix tailTrace_7121427
  have hstable : (prefixWord ++ tailWord_7121427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121427).length < 2 ^ (prefixWord ++ tailWord_7121427).sum := by decide
  have hdescent : baseEnd_7121427 < baseStart_7121427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121434 : List Nat := [3, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4]
def baseStart_7121434 : Nat := 118140960795 + 7121434 * 2 ^ 59
def prefixEnd_7121434 : Nat := 4983230072969 + 3 ^ 40 * 7121434 * 2
def baseEnd_7121434 : Nat := 3656718591270795590424127

theorem tailTrace_7121434 : CollatzResearch.WordTrace tailWord_7121434 prefixEnd_7121434 3656718591270795590424127 := by
  unfold tailWord_7121434
  simp only [CollatzResearch.WordTrace]
  refine ⟨64935009120567084235542839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173160024321512224628114237 64935009120567084235542839)
  ·
    refine ⟨97402513680850626353314259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64935009120567084235542839 97402513680850626353314259)
    ·
      refine ⟨146103770521275939529971389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97402513680850626353314259 146103770521275939529971389)
      ·
        refine ⟨54788913945478477323739271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146103770521275939529971389 54788913945478477323739271)
        ·
          refine ⟨82183370918217715985608907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54788913945478477323739271 82183370918217715985608907)
          ·
            refine ⟨123275056377326573978413361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82183370918217715985608907 123275056377326573978413361)
            ·
              refine ⟨92456292282994930483810021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123275056377326573978413361 92456292282994930483810021)
              ·
                refine ⟨17335554803061549465714379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92456292282994930483810021 17335554803061549465714379)
                ·
                  refine ⟨26003332204592324198571569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17335554803061549465714379 26003332204592324198571569)
                  ·
                    refine ⟨19502499153444243148928677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26003332204592324198571569 19502499153444243148928677)
                    ·
                      refine ⟨3656718591270795590424127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19502499153444243148928677 3656718591270795590424127)
                      ·
                        rfl

theorem cell23_7121434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_7121434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121434 prefixEnd_7121434 := by exact prefixLift 7121434
  have htrace : WordTrace (prefixWord ++ tailWord_7121434) baseStart_7121434 baseEnd_7121434 := by
    simpa [prefixWord, tailWord_7121434, baseEnd_7121434] using wordTrace_append hprefix tailTrace_7121434
  have hstable : (prefixWord ++ tailWord_7121434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121434).length < 2 ^ (prefixWord ++ tailWord_7121434).sum := by decide
  have hdescent : baseEnd_7121434 < baseStart_7121434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121441 : List Nat := [1, 2, 3, 2, 2, 1, 1, 5, 1, 2, 3]
def baseStart_7121441 : Nat := 118140960795 + 7121441 * 2 ^ 59
def prefixEnd_7121441 : Nat := 4983230072969 + 3 ^ 40 * 7121441 * 2
def baseEnd_7121441 : Nat := 3656722185635377063036595

theorem tailTrace_7121441 : CollatzResearch.WordTrace tailWord_7121441 prefixEnd_7121441 3656722185635377063036595 := by
  unfold tailWord_7121441
  simp only [CollatzResearch.WordTrace]
  refine ⟨259740291793242977137676177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173160194528828651425117451 259740291793242977137676177)
  ·
    refine ⟨194805218844932232853257133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259740291793242977137676177 194805218844932232853257133)
    ·
      refine ⟨73051957066849587319971425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194805218844932232853257133 73051957066849587319971425)
      ·
        refine ⟨54788967800137190489978569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73051957066849587319971425 54788967800137190489978569)
        ·
          refine ⟨41091725850102892867483927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54788967800137190489978569 41091725850102892867483927)
          ·
            refine ⟨61637588775154339301225891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41091725850102892867483927 61637588775154339301225891)
            ·
              refine ⟨92456383162731508951838837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61637588775154339301225891 92456383162731508951838837)
              ·
                refine ⟨8667785921506078964234891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92456383162731508951838837 8667785921506078964234891)
                ·
                  refine ⟨13001678882259118446352337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8667785921506078964234891 13001678882259118446352337)
                  ·
                    refine ⟨9751259161694338834764253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13001678882259118446352337 9751259161694338834764253)
                    ·
                      refine ⟨3656722185635377063036595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9751259161694338834764253 3656722185635377063036595)
                      ·
                        rfl

theorem cell23_7121441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_7121441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121441 prefixEnd_7121441 := by exact prefixLift 7121441
  have htrace : WordTrace (prefixWord ++ tailWord_7121441) baseStart_7121441 baseEnd_7121441 := by
    simpa [prefixWord, tailWord_7121441, baseEnd_7121441] using wordTrace_append hprefix tailTrace_7121441
  have hstable : (prefixWord ++ tailWord_7121441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121441).length < 2 ^ (prefixWord ++ tailWord_7121441).sum := by decide
  have hdescent : baseEnd_7121441 < baseStart_7121441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121511 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 5, 4, 2]
def baseStart_7121511 : Nat := 118140960795 + 7121511 * 2 ^ 59
def prefixEnd_7121511 : Nat := 4983230072969 + 3 ^ 40 * 7121511 * 2
def baseEnd_7121511 : Nat := 3656758129281191789161273

theorem tailTrace_7121511 : CollatzResearch.WordTrace tailWord_7121511 prefixEnd_7121511 3656758129281191789161273 := by
  unfold tailWord_7121511
  simp only [CollatzResearch.WordTrace]
  refine ⟨259742844902989379092724387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173161896601992919395149591 259742844902989379092724387)
  ·
    refine ⟨389614267354484068639086581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259742844902989379092724387 389614267354484068639086581)
    ·
      refine ⟨36526337564482881434914367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 389614267354484068639086581 36526337564482881434914367)
      ·
        refine ⟨54789506346724322152371551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36526337564482881434914367 54789506346724322152371551)
        ·
          refine ⟨82184259520086483228557327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54789506346724322152371551 82184259520086483228557327)
          ·
            refine ⟨123276389280129724842835991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82184259520086483228557327 123276389280129724842835991)
            ·
              refine ⟨184914583920194587264253987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123276389280129724842835991 184914583920194587264253987)
              ·
                refine ⟨277371875880291880896380981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184914583920194587264253987 277371875880291880896380981)
                ·
                  refine ⟨26003613363777363834035717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 277371875880291880896380981 26003613363777363834035717)
                  ·
                    refine ⟨4875677505708255718881697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26003613363777363834035717 4875677505708255718881697)
                    ·
                      refine ⟨3656758129281191789161273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4875677505708255718881697 3656758129281191789161273)
                      ·
                        rfl

theorem cell23_7121511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_7121511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121511 prefixEnd_7121511 := by exact prefixLift 7121511
  have htrace : WordTrace (prefixWord ++ tailWord_7121511) baseStart_7121511 baseEnd_7121511 := by
    simpa [prefixWord, tailWord_7121511, baseEnd_7121511] using wordTrace_append hprefix tailTrace_7121511
  have hstable : (prefixWord ++ tailWord_7121511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121511).length < 2 ^ (prefixWord ++ tailWord_7121511).sum := by decide
  have hdescent : baseEnd_7121511 < baseStart_7121511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121562 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2]
def baseStart_7121562 : Nat := 118140960795 + 7121562 * 2 ^ 59
def prefixEnd_7121562 : Nat := 4983230072969 + 3 ^ 40 * 7121562 * 2
def baseEnd_7121562 : Nat := 3656784316794571089623539

theorem tailTrace_7121562 : CollatzResearch.WordTrace tailWord_7121562 prefixEnd_7121562 3656784316794571089623539 := by
  unfold tailWord_7121562
  simp only [CollatzResearch.WordTrace]
  refine ⟨64936176256451153700707735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173163136683869743201887293 64936176256451153700707735)
  ·
    refine ⟨97404264384676730551061603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64936176256451153700707735 97404264384676730551061603)
    ·
      refine ⟨146106396577015095826592405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97404264384676730551061603 146106396577015095826592405)
      ·
        refine ⟨6848737339547582616871519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146106396577015095826592405 6848737339547582616871519)
        ·
          refine ⟨10273106009321373925307279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6848737339547582616871519 10273106009321373925307279)
          ·
            refine ⟨15409659013982060887960919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10273106009321373925307279 15409659013982060887960919)
            ·
              refine ⟨23114488520973091331941379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15409659013982060887960919 23114488520973091331941379)
              ·
                refine ⟨34671732781459636997912069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23114488520973091331941379 34671732781459636997912069)
                ·
                  refine ⟨6500949896523681937108513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34671732781459636997912069 6500949896523681937108513)
                  ·
                    refine ⟨4875712422392761452831385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6500949896523681937108513 4875712422392761452831385)
                    ·
                      refine ⟨3656784316794571089623539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4875712422392761452831385 3656784316794571089623539)
                      ·
                        rfl

theorem cell23_7121562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_7121562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121562 prefixEnd_7121562 := by exact prefixLift 7121562
  have htrace : WordTrace (prefixWord ++ tailWord_7121562) baseStart_7121562 baseEnd_7121562 := by
    simpa [prefixWord, tailWord_7121562, baseEnd_7121562] using wordTrace_append hprefix tailTrace_7121562
  have hstable : (prefixWord ++ tailWord_7121562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121562).length < 2 ^ (prefixWord ++ tailWord_7121562).sum := by decide
  have hdescent : baseEnd_7121562 < baseStart_7121562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121571 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 2, 5, 2]
def baseStart_7121571 : Nat := 118140960795 + 7121571 * 2 ^ 59
def prefixEnd_7121571 : Nat := 4983230072969 + 3 ^ 40 * 7121571 * 2
def baseEnd_7121571 : Nat := 3656788938120461554410997

theorem tailTrace_7121571 : CollatzResearch.WordTrace tailWord_7121571 prefixEnd_7121571 3656788938120461554410997 := by
  unfold tailWord_7121571
  simp only [CollatzResearch.WordTrace]
  refine ⟨259745033282772009339908567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173163355521848006226605711 259745033282772009339908567)
  ·
    refine ⟨389617549924158014009862851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259745033282772009339908567 389617549924158014009862851)
    ·
      refine ⟨584426324886237021014794277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389617549924158014009862851 584426324886237021014794277)
      ·
        refine ⟨109579935916169441440273927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 584426324886237021014794277 109579935916169441440273927)
        ·
          refine ⟨164369903874254162160410891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109579935916169441440273927 164369903874254162160410891)
          ·
            refine ⟨246554855811381243240616337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164369903874254162160410891 246554855811381243240616337)
            ·
              refine ⟨184916141858535932430462253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246554855811381243240616337 184916141858535932430462253)
              ·
                refine ⟨69343553196950974661423345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184916141858535932430462253 69343553196950974661423345)
                ·
                  refine ⟨52007664897713230996067509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69343553196950974661423345 52007664897713230996067509)
                  ·
                    refine ⟨4875718584160615405881329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52007664897713230996067509 4875718584160615405881329)
                    ·
                      refine ⟨3656788938120461554410997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4875718584160615405881329 3656788938120461554410997)
                      ·
                        rfl

theorem cell23_7121571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_7121571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121571 prefixEnd_7121571 := by exact prefixLift 7121571
  have htrace : WordTrace (prefixWord ++ tailWord_7121571) baseStart_7121571 baseEnd_7121571 := by
    simpa [prefixWord, tailWord_7121571, baseEnd_7121571] using wordTrace_append hprefix tailTrace_7121571
  have hstable : (prefixWord ++ tailWord_7121571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121571).length < 2 ^ (prefixWord ++ tailWord_7121571).sum := by decide
  have hdescent : baseEnd_7121571 < baseStart_7121571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121581 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_7121581 : Nat := 118140960795 + 7121581 * 2 ^ 59
def prefixEnd_7121581 : Nat := 4983230072969 + 3 ^ 40 * 7121581 * 2
def baseEnd_7121581 : Nat := 1218931357642335505095317

theorem tailTrace_7121581 : CollatzResearch.WordTrace tailWord_7121581 prefixEnd_7121581 1218931357642335505095317 := by
  unfold tailWord_7121581
  simp only [CollatzResearch.WordTrace]
  refine ⟨259745398012735781047772597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173163598675157187365181731 259745398012735781047772597)
  ·
    refine ⟨24351131063693979473228681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 259745398012735781047772597 24351131063693979473228681)
    ·
      refine ⟨18263348297770484604921511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24351131063693979473228681 18263348297770484604921511)
      ·
        refine ⟨27395022446655726907382267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18263348297770484604921511 27395022446655726907382267)
        ·
          refine ⟨41092533669983590361073401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27395022446655726907382267 41092533669983590361073401)
          ·
            refine ⟨30819400252487692770805051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41092533669983590361073401 30819400252487692770805051)
            ·
              refine ⟨46229100378731539156207577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30819400252487692770805051 46229100378731539156207577)
              ·
                refine ⟨34671825284048654367155683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46229100378731539156207577 34671825284048654367155683)
                ·
                  refine ⟨52007737926072981550733525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34671825284048654367155683 52007737926072981550733525)
                  ·
                    refine ⟨1218931357642335505095317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52007737926072981550733525 1218931357642335505095317)
                    ·
                      rfl

theorem cell23_7121581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_7121581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121581 prefixEnd_7121581 := by exact prefixLift 7121581
  have htrace : WordTrace (prefixWord ++ tailWord_7121581) baseStart_7121581 baseEnd_7121581 := by
    simpa [prefixWord, tailWord_7121581, baseEnd_7121581] using wordTrace_append hprefix tailTrace_7121581
  have hstable : (prefixWord ++ tailWord_7121581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121581).length < 2 ^ (prefixWord ++ tailWord_7121581).sum := by decide
  have hdescent : baseEnd_7121581 < baseStart_7121581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121594 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 2, 8]
def baseStart_7121594 : Nat := 118140960795 + 7121594 * 2 ^ 59
def prefixEnd_7121594 : Nat := 4983230072969 + 3 ^ 40 * 7121594 * 2
def baseEnd_7121594 : Nat := 1218933582725171654807797

theorem tailTrace_7121594 : CollatzResearch.WordTrace tailWord_7121594 prefixEnd_7121594 1218933582725171654807797 := by
  unfold tailWord_7121594
  simp only [CollatzResearch.WordTrace]
  refine ⟨64936468040422171066998959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173163914774459122845330557 64936468040422171066998959)
  ·
    refine ⟨97404702060633256600498439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64936468040422171066998959 97404702060633256600498439)
    ·
      refine ⟨146107053090949884900747659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97404702060633256600498439 146107053090949884900747659)
      ·
        refine ⟨219160579636424827351121489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146107053090949884900747659 219160579636424827351121489)
        ·
          refine ⟨164370434727318620513341117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219160579636424827351121489 164370434727318620513341117)
          ·
            refine ⟨61638913022744482692502919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164370434727318620513341117 61638913022744482692502919)
            ·
              refine ⟨92458369534116724038754379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61638913022744482692502919 92458369534116724038754379)
              ·
                refine ⟨138687554301175086058131569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92458369534116724038754379 138687554301175086058131569)
                ·
                  refine ⟨104015665725881314543598677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138687554301175086058131569 104015665725881314543598677)
                  ·
                    refine ⟨1218933582725171654807797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104015665725881314543598677 1218933582725171654807797)
                    ·
                      rfl

theorem cell23_7121594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_7121594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121594 prefixEnd_7121594 := by exact prefixLift 7121594
  have htrace : WordTrace (prefixWord ++ tailWord_7121594) baseStart_7121594 baseEnd_7121594 := by
    simpa [prefixWord, tailWord_7121594, baseEnd_7121594] using wordTrace_append hprefix tailTrace_7121594
  have hstable : (prefixWord ++ tailWord_7121594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121594).length < 2 ^ (prefixWord ++ tailWord_7121594).sum := by decide
  have hdescent : baseEnd_7121594 < baseStart_7121594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121678 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2]
def baseStart_7121678 : Nat := 118140960795 + 7121678 * 2 ^ 59
def prefixEnd_7121678 : Nat := 4983230072969 + 3 ^ 40 * 7121678 * 2
def baseEnd_7121678 : Nat := 3656843880550492635773005

theorem tailTrace_7121678 : CollatzResearch.WordTrace tailWord_7121678 prefixEnd_7121678 3656843880550492635773005 := by
  unfold tailWord_7121678
  simp only [CollatzResearch.WordTrace]
  refine ⟨32468616986673045826756711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173165957262256244409369125 32468616986673045826756711)
  ·
    refine ⟨48702925480009568740135067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32468616986673045826756711 48702925480009568740135067)
    ·
      refine ⟨73054388220014353110202601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48702925480009568740135067 73054388220014353110202601)
      ·
        refine ⟨54790791165010764832651951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73054388220014353110202601 54790791165010764832651951)
        ·
          refine ⟨82186186747516147248977927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54790791165010764832651951 82186186747516147248977927)
          ·
            refine ⟨123279280121274220873466891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82186186747516147248977927 123279280121274220873466891)
            ·
              refine ⟨184918920181911331310200337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123279280121274220873466891 184918920181911331310200337)
              ·
                refine ⟨138689190136433498482650253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184918920181911331310200337 138689190136433498482650253)
                ·
                  refine ⟨52008446301162561930993845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138689190136433498482650253 52008446301162561930993845)
                  ·
                    refine ⟨4875791840733990181030673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52008446301162561930993845 4875791840733990181030673)
                    ·
                      refine ⟨3656843880550492635773005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4875791840733990181030673 3656843880550492635773005)
                      ·
                        rfl

theorem cell23_7121678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_7121678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121678 prefixEnd_7121678 := by exact prefixLift 7121678
  have htrace : WordTrace (prefixWord ++ tailWord_7121678) baseStart_7121678 baseEnd_7121678 := by
    simpa [prefixWord, tailWord_7121678, baseEnd_7121678] using wordTrace_append hprefix tailTrace_7121678
  have hstable : (prefixWord ++ tailWord_7121678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121678).length < 2 ^ (prefixWord ++ tailWord_7121678).sum := by decide
  have hdescent : baseEnd_7121678 < baseStart_7121678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121708 : List Nat := [2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 4]
def baseStart_7121708 : Nat := 118140960795 + 7121708 * 2 ^ 59
def prefixEnd_7121708 : Nat := 4983230072969 + 3 ^ 40 * 7121708 * 2
def baseEnd_7121708 : Nat := 3656859284970127518397867

theorem tailTrace_7121708 : CollatzResearch.WordTrace tailWord_7121708 prefixEnd_7121708 3656859284970127518397867 := by
  unfold tailWord_7121708
  simp only [CollatzResearch.WordTrace]
  refine ⟨129875015041637840868822889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173166686722183787825097185 129875015041637840868822889)
  ·
    refine ⟨97406261281228380651617167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129875015041637840868822889 97406261281228380651617167)
    ·
      refine ⟨146109391921842570977425751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97406261281228380651617167 146109391921842570977425751)
      ·
        refine ⟨219164087882763856466138627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146109391921842570977425751 219164087882763856466138627)
        ·
          refine ⟨328746131824145784699207941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219164087882763856466138627 328746131824145784699207941)
          ·
            refine ⟨61639899717027334631101489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 328746131824145784699207941 61639899717027334631101489)
            ·
              refine ⟨46229924787770500973326117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61639899717027334631101489 46229924787770500973326117)
              ·
                refine ⟨8668110897706968932498647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46229924787770500973326117 8668110897706968932498647)
                ·
                  refine ⟨13002166346560453398747971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8668110897706968932498647 13002166346560453398747971)
                  ·
                    refine ⟨19503249519840680098121957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13002166346560453398747971 19503249519840680098121957)
                    ·
                      refine ⟨3656859284970127518397867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19503249519840680098121957 3656859284970127518397867)
                      ·
                        rfl

theorem cell23_7121708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 4].length) (baseStart_7121708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121708 prefixEnd_7121708 := by exact prefixLift 7121708
  have htrace : WordTrace (prefixWord ++ tailWord_7121708) baseStart_7121708 baseEnd_7121708 := by
    simpa [prefixWord, tailWord_7121708, baseEnd_7121708] using wordTrace_append hprefix tailTrace_7121708
  have hstable : (prefixWord ++ tailWord_7121708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121708).length < 2 ^ (prefixWord ++ tailWord_7121708).sum := by decide
  have hdescent : baseEnd_7121708 < baseStart_7121708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121722 : List Nat := [3, 1, 1, 1, 6, 2, 2, 1, 1, 5]
def baseStart_7121722 : Nat := 118140960795 + 7121722 * 2 ^ 59
def prefixEnd_7121722 : Nat := 4983230072969 + 3 ^ 40 * 7121722 * 2
def baseEnd_7121722 : Nat := 1218955491233096821207601

theorem tailTrace_7121722 : CollatzResearch.WordTrace tailWord_7121722 prefixEnd_7121722 1218955491233096821207601 := by
  unfold tailWord_7121722
  simp only [CollatzResearch.WordTrace]
  refine ⟨64937635176306240532163855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173167027136816641419103613 64937635176306240532163855)
  ·
    refine ⟨97406452764459360798245783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64937635176306240532163855 97406452764459360798245783)
    ·
      refine ⟨146109679146689041197368675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97406452764459360798245783 146109679146689041197368675)
      ·
        refine ⟨219164518720033561796053013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146109679146689041197368675 219164518720033561796053013)
        ·
          refine ⟨10273336815001573209189985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 219164518720033561796053013 10273336815001573209189985)
          ·
            refine ⟨7705002611251179906892489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10273336815001573209189985 7705002611251179906892489)
            ·
              refine ⟨5778751958438384930169367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7705002611251179906892489 5778751958438384930169367)
              ·
                refine ⟨8668127937657577395254051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5778751958438384930169367 8668127937657577395254051)
                ·
                  refine ⟨13002191906486366092881077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8668127937657577395254051 13002191906486366092881077)
                  ·
                    refine ⟨1218955491233096821207601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13002191906486366092881077 1218955491233096821207601)
                    ·
                      rfl

theorem cell23_7121722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 1, 5].length) (baseStart_7121722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121722 prefixEnd_7121722 := by exact prefixLift 7121722
  have htrace : WordTrace (prefixWord ++ tailWord_7121722) baseStart_7121722 baseEnd_7121722 := by
    simpa [prefixWord, tailWord_7121722, baseEnd_7121722] using wordTrace_append hprefix tailTrace_7121722
  have hstable : (prefixWord ++ tailWord_7121722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121722).length < 2 ^ (prefixWord ++ tailWord_7121722).sum := by decide
  have hdescent : baseEnd_7121722 < baseStart_7121722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121771 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 5]
def baseStart_7121771 : Nat := 118140960795 + 7121771 * 2 ^ 59
def prefixEnd_7121771 : Nat := 4983230072969 + 3 ^ 40 * 7121771 * 2
def baseEnd_7121771 : Nat := 3656891634251360771910077

theorem tailTrace_7121771 : CollatzResearch.WordTrace tailWord_7121771 prefixEnd_7121771 3656891634251360771910077 := by
  unfold tailWord_7121771
  simp only [CollatzResearch.WordTrace]
  refine ⟨259752327882047443497189167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173168218588031628998126111 259752327882047443497189167)
  ·
    refine ⟨389628491823071165245783751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259752327882047443497189167 389628491823071165245783751)
    ·
      refine ⟨584442737734606747868675627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389628491823071165245783751 584442737734606747868675627)
      ·
        refine ⟨876664106601910121803013441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584442737734606747868675627 876664106601910121803013441)
        ·
          refine ⟨657498079951432591352260081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 876664106601910121803013441 657498079951432591352260081)
          ·
            refine ⟨493123559963574443514195061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657498079951432591352260081 493123559963574443514195061)
            ·
              refine ⟨46230333746585104079455787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 493123559963574443514195061 46230333746585104079455787)
              ·
                refine ⟨69345500619877656119183681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46230333746585104079455787 69345500619877656119183681)
                ·
                  refine ⟨52009125464908242089387761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69345500619877656119183681 52009125464908242089387761)
                  ·
                    refine ⟨39006844098681181567040821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52009125464908242089387761 39006844098681181567040821)
                    ·
                      refine ⟨3656891634251360771910077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39006844098681181567040821 3656891634251360771910077)
                      ·
                        rfl

theorem cell23_7121771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 5].length) (baseStart_7121771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121771 prefixEnd_7121771 := by exact prefixLift 7121771
  have htrace : WordTrace (prefixWord ++ tailWord_7121771) baseStart_7121771 baseEnd_7121771 := by
    simpa [prefixWord, tailWord_7121771, baseEnd_7121771] using wordTrace_append hprefix tailTrace_7121771
  have hstable : (prefixWord ++ tailWord_7121771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121771).length < 2 ^ (prefixWord ++ tailWord_7121771).sum := by decide
  have hdescent : baseEnd_7121771 < baseStart_7121771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121791 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 4, 6]
def baseStart_7121791 : Nat := 118140960795 + 7121791 * 2 ^ 59
def prefixEnd_7121791 : Nat := 4983230072969 + 3 ^ 40 * 7121791 * 2
def baseEnd_7121791 : Nat := 1218967301288150231219995

theorem tailTrace_7121791 : CollatzResearch.WordTrace tailWord_7121791 prefixEnd_7121791 1218967301288150231219995 := by
  unfold tailWord_7121791
  simp only [CollatzResearch.WordTrace]
  refine ⟨259753057341974986912917227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173168704894649991275278151 259753057341974986912917227)
  ·
    refine ⟨389629586012962480369375841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259753057341974986912917227 389629586012962480369375841)
    ·
      refine ⟨292222189509721860277031881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389629586012962480369375841 292222189509721860277031881)
      ·
        refine ⟨219166642132291395207773911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292222189509721860277031881 219166642132291395207773911)
        ·
          refine ⟨328749963198437092811660867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219166642132291395207773911 328749963198437092811660867)
          ·
            refine ⟨493124944797655639217491301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328749963198437092811660867 493124944797655639217491301)
            ·
              refine ⟨92460927149560432353279619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 493124944797655639217491301 92460927149560432353279619)
              ·
                refine ⟨138691390724340648529919429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92460927149560432353279619 138691390724340648529919429)
                ·
                  refine ⟨26004635760813871599359893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138691390724340648529919429 26004635760813871599359893)
                  ·
                    refine ⟨1218967301288150231219995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26004635760813871599359893 1218967301288150231219995)
                    ·
                      rfl

theorem cell23_7121791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 6].length) (baseStart_7121791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121791 prefixEnd_7121791 := by exact prefixLift 7121791
  have htrace : WordTrace (prefixWord ++ tailWord_7121791) baseStart_7121791 baseEnd_7121791 := by
    simpa [prefixWord, tailWord_7121791, baseEnd_7121791] using wordTrace_append hprefix tailTrace_7121791
  have hstable : (prefixWord ++ tailWord_7121791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121791).length < 2 ^ (prefixWord ++ tailWord_7121791).sum := by decide
  have hdescent : baseEnd_7121791 < baseStart_7121791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121815 : List Nat := [1, 1, 3, 3, 1, 2, 2, 3, 1, 4, 2]
def baseStart_7121815 : Nat := 118140960795 + 7121815 * 2 ^ 59
def prefixEnd_7121815 : Nat := 4983230072969 + 3 ^ 40 * 7121815 * 2
def baseEnd_7121815 : Nat := 3656914227400158599759875

theorem tailTrace_7121815 : CollatzResearch.WordTrace tailWord_7121815 prefixEnd_7121815 3656914227400158599759875 := by
  unfold tailWord_7121815
  simp only [CollatzResearch.WordTrace]
  refine ⟨259753932693888039011790899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173169288462592026007860599 259753932693888039011790899)
  ·
    refine ⟨389630899040832058517686349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259753932693888039011790899 389630899040832058517686349)
    ·
      refine ⟨146111587140312021944132381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389630899040832058517686349 146111587140312021944132381)
      ·
        refine ⟨54791845177617008229049643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146111587140312021944132381 54791845177617008229049643)
        ·
          refine ⟨82187767766425512343574465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54791845177617008229049643 82187767766425512343574465)
          ·
            refine ⟨61640825824819134257680849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82187767766425512343574465 61640825824819134257680849)
            ·
              refine ⟨46230619368614350693260637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61640825824819134257680849 46230619368614350693260637)
              ·
                refine ⟨17336482263230381509972739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46230619368614350693260637 17336482263230381509972739)
                ·
                  refine ⟨26004723394845572264959109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17336482263230381509972739 26004723394845572264959109)
                  ·
                    refine ⟨4875885636533544799679833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26004723394845572264959109 4875885636533544799679833)
                    ·
                      refine ⟨3656914227400158599759875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4875885636533544799679833 3656914227400158599759875)
                      ·
                        rfl

theorem cell23_7121815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_7121815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121815 prefixEnd_7121815 := by exact prefixLift 7121815
  have htrace : WordTrace (prefixWord ++ tailWord_7121815) baseStart_7121815 baseEnd_7121815 := by
    simpa [prefixWord, tailWord_7121815, baseEnd_7121815] using wordTrace_append hprefix tailTrace_7121815
  have hstable : (prefixWord ++ tailWord_7121815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121815).length < 2 ^ (prefixWord ++ tailWord_7121815).sum := by decide
  have hdescent : baseEnd_7121815 < baseStart_7121815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121849 : List Nat := [1, 2, 1, 4, 2, 3, 2, 2, 2, 2, 2]
def baseStart_7121849 : Nat := 118140960795 + 7121849 * 2 ^ 59
def prefixEnd_7121849 : Nat := 4983230072969 + 3 ^ 40 * 7121849 * 2
def baseEnd_7121849 : Nat := 3656931685742411466734719

theorem tailTrace_7121849 : CollatzResearch.WordTrace tailWord_7121849 prefixEnd_7121849 3656931685742411466734719 := by
  unfold tailWord_7121849
  simp only [CollatzResearch.WordTrace]
  refine ⟨259755172775764862818528601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173170115183843241879019067 259755172775764862818528601)
  ·
    refine ⟨194816379581823647113896451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259755172775764862818528601 194816379581823647113896451)
    ·
      refine ⟨292224569372735470670844677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194816379581823647113896451 292224569372735470670844677)
      ·
        refine ⟨54792106757387900750783377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292224569372735470670844677 54792106757387900750783377)
        ·
          refine ⟨41094080068040925563087533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54792106757387900750783377 41094080068040925563087533)
          ·
            refine ⟨15410280025515347086157825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41094080068040925563087533 15410280025515347086157825)
            ·
              refine ⟨11557710019136510314618369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15410280025515347086157825 11557710019136510314618369)
              ·
                refine ⟨8668282514352382735963777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11557710019136510314618369 8668282514352382735963777)
                ·
                  refine ⟨6501211885764287051972833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8668282514352382735963777 6501211885764287051972833)
                  ·
                    refine ⟨4875908914323215288979625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6501211885764287051972833 4875908914323215288979625)
                    ·
                      refine ⟨3656931685742411466734719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4875908914323215288979625 3656931685742411466734719)
                      ·
                        rfl

theorem cell23_7121849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_7121849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121849 prefixEnd_7121849 := by exact prefixLift 7121849
  have htrace : WordTrace (prefixWord ++ tailWord_7121849) baseStart_7121849 baseEnd_7121849 := by
    simpa [prefixWord, tailWord_7121849, baseEnd_7121849] using wordTrace_append hprefix tailTrace_7121849
  have hstable : (prefixWord ++ tailWord_7121849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121849).length < 2 ^ (prefixWord ++ tailWord_7121849).sum := by decide
  have hdescent : baseEnd_7121849 < baseStart_7121849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121868 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 1, 7]
def baseStart_7121868 : Nat := 118140960795 + 7121868 * 2 ^ 59
def prefixEnd_7121868 : Nat := 4983230072969 + 3 ^ 40 * 7121868 * 2
def baseEnd_7121868 : Nat := 1218980480624948964132377

theorem tailTrace_7121868 : CollatzResearch.WordTrace tailWord_7121868 prefixEnd_7121868 1218980480624948964132377 := by
  unfold tailWord_7121868
  simp only [CollatzResearch.WordTrace]
  refine ⟨129877932881348014531735129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173170577175130686042313505 129877932881348014531735129)
  ·
    refine ⟨97408449661011010898801347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129877932881348014531735129 97408449661011010898801347)
    ·
      refine ⟨146112674491516516348202021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97408449661011010898801347 146112674491516516348202021)
      ·
        refine ⟨27396126467159346815287879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146112674491516516348202021 27396126467159346815287879)
        ·
          refine ⟨41094189700739020222931819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27396126467159346815287879 41094189700739020222931819)
          ·
            refine ⟨61641284551108530334397729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41094189700739020222931819 61641284551108530334397729)
            ·
              refine ⟨46230963413331397750798297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61641284551108530334397729 46230963413331397750798297)
              ·
                refine ⟨34673222559998548313098723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46230963413331397750798297 34673222559998548313098723)
                ·
                  refine ⟨52009833839997822469648085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34673222559998548313098723 52009833839997822469648085)
                  ·
                    refine ⟨1218980480624948964132377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52009833839997822469648085 1218980480624948964132377)
                    ·
                      rfl

theorem cell23_7121868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_7121868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121868 prefixEnd_7121868 := by exact prefixLift 7121868
  have htrace : WordTrace (prefixWord ++ tailWord_7121868) baseStart_7121868 baseEnd_7121868 := by
    simpa [prefixWord, tailWord_7121868, baseEnd_7121868] using wordTrace_append hprefix tailTrace_7121868
  have hstable : (prefixWord ++ tailWord_7121868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121868).length < 2 ^ (prefixWord ++ tailWord_7121868).sum := by decide
  have hdescent : baseEnd_7121868 < baseStart_7121868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121885 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 1, 7]
def baseStart_7121885 : Nat := 118140960795 + 7121885 * 2 ^ 59
def prefixEnd_7121885 : Nat := 4983230072969 + 3 ^ 40 * 7121885 * 2
def baseEnd_7121885 : Nat := 1218983390348657775294851

theorem tailTrace_7121885 : CollatzResearch.WordTrace tailWord_7121885 prefixEnd_7121885 1218983390348657775294851 := by
  unfold tailWord_7121885
  simp only [CollatzResearch.WordTrace]
  refine ⟨259756485803634440966839109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173170990535756293977892739 259756485803634440966839109)
  ·
    refine ⟨48704341088181457681282333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259756485803634440966839109 48704341088181457681282333)
    ·
      refine ⟨18264127908068046630480875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48704341088181457681282333 18264127908068046630480875)
      ·
        refine ⟨27396191862102069945721313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18264127908068046630480875 27396191862102069945721313)
        ·
          refine ⟨20547143896576552459290985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27396191862102069945721313 20547143896576552459290985)
          ·
            refine ⟨15410357922432414344468239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20547143896576552459290985 15410357922432414344468239)
            ·
              refine ⟨23115536883648621516702359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15410357922432414344468239 23115536883648621516702359)
              ·
                refine ⟨34673305325472932275053539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23115536883648621516702359 34673305325472932275053539)
                ·
                  refine ⟨52009957988209398412580309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34673305325472932275053539 52009957988209398412580309)
                  ·
                    refine ⟨1218983390348657775294851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52009957988209398412580309 1218983390348657775294851)
                    ·
                      rfl

theorem cell23_7121885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_7121885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121885 prefixEnd_7121885 := by exact prefixLift 7121885
  have htrace : WordTrace (prefixWord ++ tailWord_7121885) baseStart_7121885 baseEnd_7121885 := by
    simpa [prefixWord, tailWord_7121885, baseEnd_7121885] using wordTrace_append hprefix tailTrace_7121885
  have hstable : (prefixWord ++ tailWord_7121885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121885).length < 2 ^ (prefixWord ++ tailWord_7121885).sum := by decide
  have hdescent : baseEnd_7121885 < baseStart_7121885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121959 : List Nat := [1, 1, 7, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_7121959 : Nat := 118140960795 + 7121959 * 2 ^ 59
def prefixEnd_7121959 : Nat := 4983230072969 + 3 ^ 40 * 7121959 * 2
def baseEnd_7121959 : Nat := 3656988168614406036359213

theorem tailTrace_7121959 : CollatzResearch.WordTrace tailWord_7121959 prefixEnd_7121959 3656988168614406036359213 := by
  unfold tailWord_7121959
  simp only [CollatzResearch.WordTrace]
  refine ⟨259759184805366351605032931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173172789870244234403355287 259759184805366351605032931)
  ·
    refine ⟨389638777208049527407549397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259759184805366351605032931 389638777208049527407549397)
    ·
      refine ⟨9132158840813660798614439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 389638777208049527407549397 9132158840813660798614439)
      ·
        refine ⟨13698238261220491197921659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9132158840813660798614439 13698238261220491197921659)
        ·
          refine ⟨20547357391830736796882489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13698238261220491197921659 20547357391830736796882489)
          ·
            refine ⟨15410518043873052597661867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20547357391830736796882489 15410518043873052597661867)
            ·
              refine ⟨23115777065809578896492801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15410518043873052597661867 23115777065809578896492801)
              ·
                refine ⟨17336832799357184172369601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23115777065809578896492801 17336832799357184172369601)
                ·
                  refine ⟨13002624599517888129277201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17336832799357184172369601 13002624599517888129277201)
                  ·
                    refine ⟨9751968449638416096957901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13002624599517888129277201 9751968449638416096957901)
                    ·
                      refine ⟨3656988168614406036359213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9751968449638416096957901 3656988168614406036359213)
                      ·
                        rfl

theorem cell23_7121959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_7121959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121959 prefixEnd_7121959 := by exact prefixLift 7121959
  have htrace : WordTrace (prefixWord ++ tailWord_7121959) baseStart_7121959 baseEnd_7121959 := by
    simpa [prefixWord, tailWord_7121959, baseEnd_7121959] using wordTrace_append hprefix tailTrace_7121959
  have hstable : (prefixWord ++ tailWord_7121959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121959).length < 2 ^ (prefixWord ++ tailWord_7121959).sum := by decide
  have hdescent : baseEnd_7121959 < baseStart_7121959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121966 : List Nat := [4, 1, 3, 1, 1, 1, 5, 2, 1, 4]
def baseStart_7121966 : Nat := 118140960795 + 7121966 * 2 ^ 59
def prefixEnd_7121966 : Nat := 4983230072969 + 3 ^ 40 * 7121966 * 2
def baseEnd_7121966 : Nat := 1218997254326329169657227

theorem tailTrace_7121966 : CollatzResearch.WordTrace tailWord_7121966 prefixEnd_7121966 1218997254326329169657227 := by
  unfold tailWord_7121966
  simp only [CollatzResearch.WordTrace]
  refine ⟨32469930014542623975067219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173172960077560661200358501 32469930014542623975067219)
  ·
    refine ⟨48704895021813935962600829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32469930014542623975067219 48704895021813935962600829)
    ·
      refine ⟨18264335633180225985975311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48704895021813935962600829 18264335633180225985975311)
      ·
        refine ⟨27396503449770338978962967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18264335633180225985975311 27396503449770338978962967)
        ·
          refine ⟨41094755174655508468444451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27396503449770338978962967 41094755174655508468444451)
          ·
            refine ⟨61642132761983262702666677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41094755174655508468444451 61642132761983262702666677)
            ·
              refine ⟨5778949946435930878375001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61642132761983262702666677 5778949946435930878375001)
              ·
                refine ⟨4334212459826948158781251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5778949946435930878375001 4334212459826948158781251)
                ·
                  refine ⟨6501318689740422238171877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4334212459826948158781251 6501318689740422238171877)
                  ·
                    refine ⟨1218997254326329169657227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6501318689740422238171877 1218997254326329169657227)
                    ·
                      rfl

theorem cell23_7121966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_7121966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7121966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7121966 prefixEnd_7121966 := by exact prefixLift 7121966
  have htrace : WordTrace (prefixWord ++ tailWord_7121966) baseStart_7121966 baseEnd_7121966 := by
    simpa [prefixWord, tailWord_7121966, baseEnd_7121966] using wordTrace_append hprefix tailTrace_7121966
  have hstable : (prefixWord ++ tailWord_7121966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121966).length < 2 ^ (prefixWord ++ tailWord_7121966).sum := by decide
  have hdescent : baseEnd_7121966 < baseStart_7121966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122005 : List Nat := [1, 3, 2, 2, 1, 2, 3, 2, 1, 6]
def baseStart_7122005 : Nat := 118140960795 + 7122005 * 2 ^ 59
def prefixEnd_7122005 : Nat := 4983230072969 + 3 ^ 40 * 7122005 * 2
def baseEnd_7122005 : Nat := 1219003929574837618794667

theorem tailTrace_7122005 : CollatzResearch.WordTrace tailWord_7122005 prefixEnd_7122005 1219003929574837618794667 := by
  unfold tailWord_7122005
  simp only [CollatzResearch.WordTrace]
  refine ⟨259760862563199701461207469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173173908375466467640804979 259760862563199701461207469)
  ·
    refine ⟨97410323461199888047952801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259760862563199701461207469 97410323461199888047952801)
    ·
      refine ⟨73057742595899916035964601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97410323461199888047952801 73057742595899916035964601)
      ·
        refine ⟨54793306946924937026973451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73057742595899916035964601 54793306946924937026973451)
        ·
          refine ⟨82189960420387405540460177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54793306946924937026973451 82189960420387405540460177)
          ·
            refine ⟨61642470315290554155345133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82189960420387405540460177 61642470315290554155345133)
            ·
              refine ⟨23115926368233957808254425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61642470315290554155345133 23115926368233957808254425)
              ·
                refine ⟨17336944776175468356190819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23115926368233957808254425 17336944776175468356190819)
                ·
                  refine ⟨26005417164263202534286229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17336944776175468356190819 26005417164263202534286229)
                  ·
                    refine ⟨1219003929574837618794667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26005417164263202534286229 1219003929574837618794667)
                    ·
                      rfl

theorem cell23_7122005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_7122005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122005 prefixEnd_7122005 := by exact prefixLift 7122005
  have htrace : WordTrace (prefixWord ++ tailWord_7122005) baseStart_7122005 baseEnd_7122005 := by
    simpa [prefixWord, tailWord_7122005, baseEnd_7122005] using wordTrace_append hprefix tailTrace_7122005
  have hstable : (prefixWord ++ tailWord_7122005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122005).length < 2 ^ (prefixWord ++ tailWord_7122005).sum := by decide
  have hdescent : baseEnd_7122005 < baseStart_7122005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122023 : List Nat := [1, 1, 5, 1, 1, 5, 2, 2, 1, 1, 3]
def baseStart_7122023 : Nat := 118140960795 + 7122023 * 2 ^ 59
def prefixEnd_7122023 : Nat := 4983230072969 + 3 ^ 40 * 7122023 * 2
def baseEnd_7122023 : Nat := 3657021031376293785958919

theorem tailTrace_7122023 : CollatzResearch.WordTrace tailWord_7122023 prefixEnd_7122023 3657021031376293785958919 := by
  unfold tailWord_7122023
  simp only [CollatzResearch.WordTrace]
  refine ⟨259761519077134490535362723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173174346051422993690241815 259761519077134490535362723)
  ·
    refine ⟨389642278615701735803044085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259761519077134490535362723 389642278615701735803044085)
    ·
      refine ⟨36528963620222037731535383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 389642278615701735803044085 36528963620222037731535383)
      ·
        refine ⟨54793445430333056597303075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36528963620222037731535383 54793445430333056597303075)
        ·
          refine ⟨82190168145499584895954613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54793445430333056597303075 82190168145499584895954613)
          ·
            refine ⟨7705328263640586083995745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82190168145499584895954613 7705328263640586083995745)
            ·
              refine ⟨5778996197730439562996809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7705328263640586083995745 5778996197730439562996809)
              ·
                refine ⟨4334247148297829672247607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5778996197730439562996809 4334247148297829672247607)
                ·
                  refine ⟨6501370722446744508371411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4334247148297829672247607 6501370722446744508371411)
                  ·
                    refine ⟨9752056083670116762557117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6501370722446744508371411 9752056083670116762557117)
                    ·
                      refine ⟨3657021031376293785958919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9752056083670116762557117 3657021031376293785958919)
                      ·
                        rfl

theorem cell23_7122023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_7122023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122023 prefixEnd_7122023 := by exact prefixLift 7122023
  have htrace : WordTrace (prefixWord ++ tailWord_7122023) baseStart_7122023 baseEnd_7122023 := by
    simpa [prefixWord, tailWord_7122023, baseEnd_7122023] using wordTrace_append hprefix tailTrace_7122023
  have hstable : (prefixWord ++ tailWord_7122023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122023).length < 2 ^ (prefixWord ++ tailWord_7122023).sum := by decide
  have hdescent : baseEnd_7122023 < baseStart_7122023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122052 : List Nat := [2, 3, 2, 1, 2, 3, 3, 7]
def baseStart_7122052 : Nat := 118140960795 + 7122052 * 2 ^ 59
def prefixEnd_7122052 : Nat := 4983230072969 + 3 ^ 40 * 7122052 * 2
def baseEnd_7122052 : Nat := 135445774900565710092455

theorem tailTrace_7122052 : CollatzResearch.WordTrace tailWord_7122052 prefixEnd_7122052 135445774900565710092455 := by
  unfold tailWord_7122052
  simp only [CollatzResearch.WordTrace]
  refine ⟨129881288397014714244084205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173175051196019618992112273 129881288397014714244084205)
  ·
    refine ⟨48705483148880517841531577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129881288397014714244084205 48705483148880517841531577)
    ·
      refine ⟨36529112361660388381148683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48705483148880517841531577 36529112361660388381148683)
      ·
        refine ⟨54793668542490582571723025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36529112361660388381148683 54793668542490582571723025)
        ·
          refine ⟨41095251406867936928792269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54793668542490582571723025 41095251406867936928792269)
          ·
            refine ⟨15410719277575476348297101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41095251406867936928792269 15410719277575476348297101)
            ·
              refine ⟨5779019729090803630611413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15410719277575476348297101 5779019729090803630611413)
              ·
                refine ⟨135445774900565710092455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5779019729090803630611413 135445774900565710092455)
                ·
                  rfl

theorem cell23_7122052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 7].length) (baseStart_7122052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122052 prefixEnd_7122052 := by exact prefixLift 7122052
  have htrace : WordTrace (prefixWord ++ tailWord_7122052) baseStart_7122052 baseEnd_7122052 := by
    simpa [prefixWord, tailWord_7122052, baseEnd_7122052] using wordTrace_append hprefix tailTrace_7122052
  have hstable : (prefixWord ++ tailWord_7122052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122052).length < 2 ^ (prefixWord ++ tailWord_7122052).sum := by decide
  have hdescent : baseEnd_7122052 < baseStart_7122052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122066 : List Nat := [3, 2, 3, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_7122066 : Nat := 118140960795 + 7122066 * 2 ^ 59
def prefixEnd_7122066 : Nat := 4983230072969 + 3 ^ 40 * 7122066 * 2
def baseEnd_7122066 : Nat := 3657043111044437117721221

theorem tailTrace_7122066 : CollatzResearch.WordTrace tailWord_7122066 prefixEnd_7122066 3657043111044437117721221 := by
  unfold tailWord_7122066
  simp only [CollatzResearch.WordTrace]
  refine ⟨64940771853994677219794513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173175391610652472586118701 64940771853994677219794513)
  ·
    refine ⟨48705578890496007914845885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64940771853994677219794513 48705578890496007914845885)
    ·
      refine ⟨18264592083936002968067207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48705578890496007914845885 18264592083936002968067207)
      ·
        refine ⟨27396888125904004452100811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18264592083936002968067207 27396888125904004452100811)
        ·
          refine ⟨41095332188856006678151217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27396888125904004452100811 41095332188856006678151217)
          ·
            refine ⟨30821499141642005008613413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41095332188856006678151217 30821499141642005008613413)
            ·
              refine ⟨5779031089057875939115015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30821499141642005008613413 5779031089057875939115015)
              ·
                refine ⟨8668546633586813908672523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5779031089057875939115015 8668546633586813908672523)
                ·
                  refine ⟨13002819950380220863008785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8668546633586813908672523 13002819950380220863008785)
                  ·
                    refine ⟨9752114962785165647256589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13002819950380220863008785 9752114962785165647256589)
                    ·
                      refine ⟨3657043111044437117721221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9752114962785165647256589 3657043111044437117721221)
                      ·
                        rfl

theorem cell23_7122066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_7122066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122066 prefixEnd_7122066 := by exact prefixLift 7122066
  have htrace : WordTrace (prefixWord ++ tailWord_7122066) baseStart_7122066 baseEnd_7122066 := by
    simpa [prefixWord, tailWord_7122066, baseEnd_7122066] using wordTrace_append hprefix tailTrace_7122066
  have hstable : (prefixWord ++ tailWord_7122066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122066).length < 2 ^ (prefixWord ++ tailWord_7122066).sum := by decide
  have hdescent : baseEnd_7122066 < baseStart_7122066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122095 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 2, 6]
def baseStart_7122095 : Nat := 118140960795 + 7122095 * 2 ^ 59
def prefixEnd_7122095 : Nat := 4983230072969 + 3 ^ 40 * 7122095 * 2
def baseEnd_7122095 : Nat := 1219019333994472501419529

theorem tailTrace_7122095 : CollatzResearch.WordTrace tailWord_7122095 prefixEnd_7122095 1219019333994472501419529 := by
  unfold tailWord_7122095
  simp only [CollatzResearch.WordTrace]
  refine ⟨259764145132873646831983739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173176096755249097887989159 259764145132873646831983739)
  ·
    refine ⟨389646217699310470247975609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259764145132873646831983739 389646217699310470247975609)
    ·
      refine ⟨292234663274482852685981707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389646217699310470247975609 292234663274482852685981707)
      ·
        refine ⟨438351994911724279028972561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292234663274482852685981707 438351994911724279028972561)
        ·
          refine ⟨328763996183793209271729421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438351994911724279028972561 328763996183793209271729421)
          ·
            refine ⟨123286498568922453476898533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328763996183793209271729421 123286498568922453476898533)
            ·
              refine ⟨23116218481672960026918475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123286498568922453476898533 23116218481672960026918475)
              ·
                refine ⟨34674327722509440040377713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23116218481672960026918475 34674327722509440040377713)
                ·
                  refine ⟨26005745791882080030283285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34674327722509440040377713 26005745791882080030283285)
                  ·
                    refine ⟨1219019333994472501419529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26005745791882080030283285 1219019333994472501419529)
                    ·
                      rfl

theorem cell23_7122095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 6].length) (baseStart_7122095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122095 prefixEnd_7122095 := by exact prefixLift 7122095
  have htrace : WordTrace (prefixWord ++ tailWord_7122095) baseStart_7122095 baseEnd_7122095 := by
    simpa [prefixWord, tailWord_7122095, baseEnd_7122095] using wordTrace_append hprefix tailTrace_7122095
  have hstable : (prefixWord ++ tailWord_7122095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122095).length < 2 ^ (prefixWord ++ tailWord_7122095).sum := by decide
  have hdescent : baseEnd_7122095 < baseStart_7122095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122114 : List Nat := [3, 5, 1, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_7122114 : Nat := 118140960795 + 7122114 * 2 ^ 59
def prefixEnd_7122114 : Nat := 4983230072969 + 3 ^ 40 * 7122114 * 2
def baseEnd_7122114 : Nat := 3657067758115852929921001

theorem tailTrace_7122114 : CollatzResearch.WordTrace tailWord_7122114 prefixEnd_7122114 3657067758115852929921001 := by
  unfold tailWord_7122114
  simp only [CollatzResearch.WordTrace]
  refine ⟨64941209529951203269231349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173176558746536542051283597 64941209529951203269231349)
  ·
    refine ⟨6088238393432925306490439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64941209529951203269231349 6088238393432925306490439)
    ·
      refine ⟨9132357590149387959735659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6088238393432925306490439 9132357590149387959735659)
      ·
        refine ⟨13698536385224081939603489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9132357590149387959735659 13698536385224081939603489)
        ·
          refine ⟨10273902288918061454702617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13698536385224081939603489 10273902288918061454702617)
          ·
            refine ⟨7705426716688546091026963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10273902288918061454702617 7705426716688546091026963)
            ·
              refine ⟨11558140075032819136540445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7705426716688546091026963 11558140075032819136540445)
              ·
                refine ⟨4334302528137307176202667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11558140075032819136540445 4334302528137307176202667)
                ·
                  refine ⟨6501453792205960764304001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4334302528137307176202667 6501453792205960764304001)
                  ·
                    refine ⟨4876090344154470573228001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6501453792205960764304001 4876090344154470573228001)
                    ·
                      refine ⟨3657067758115852929921001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4876090344154470573228001 3657067758115852929921001)
                      ·
                        rfl

theorem cell23_7122114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_7122114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122114 prefixEnd_7122114 := by exact prefixLift 7122114
  have htrace : WordTrace (prefixWord ++ tailWord_7122114) baseStart_7122114 baseEnd_7122114 := by
    simpa [prefixWord, tailWord_7122114, baseEnd_7122114] using wordTrace_append hprefix tailTrace_7122114
  have hstable : (prefixWord ++ tailWord_7122114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122114).length < 2 ^ (prefixWord ++ tailWord_7122114).sum := by decide
  have hdescent : baseEnd_7122114 < baseStart_7122114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122115 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 4]
def baseStart_7122115 : Nat := 118140960795 + 7122115 * 2 ^ 59
def prefixEnd_7122115 : Nat := 4983230072969 + 3 ^ 40 * 7122115 * 2
def baseEnd_7122115 : Nat := 3657068271596507426008495

theorem tailTrace_7122115 : CollatzResearch.WordTrace tailWord_7122115 prefixEnd_7122115 3657068271596507426008495 := by
  unfold tailWord_7122115
  simp only [CollatzResearch.WordTrace]
  refine ⟨259764874592801190247711799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173176583061867460165141199 259764874592801190247711799)
  ·
    refine ⟨389647311889201785371567699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259764874592801190247711799 389647311889201785371567699)
    ·
      refine ⟨584470967833802678057351549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389647311889201785371567699 584470967833802678057351549)
      ·
        refine ⟨219176612937676004271506831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 584470967833802678057351549 219176612937676004271506831)
        ·
          refine ⟨328764919406514006407260247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219176612937676004271506831 328764919406514006407260247)
          ·
            refine ⟨493147379109771009610890371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328764919406514006407260247 493147379109771009610890371)
            ·
              refine ⟨739721068664656514416335557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493147379109771009610890371 739721068664656514416335557)
              ·
                refine ⟨138697700374623096453062917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 739721068664656514416335557 138697700374623096453062917)
                ·
                  refine ⟨26005818820241830584949297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138697700374623096453062917 26005818820241830584949297)
                  ·
                    refine ⟨19504364115181372938711973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26005818820241830584949297 19504364115181372938711973)
                    ·
                      refine ⟨3657068271596507426008495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19504364115181372938711973 3657068271596507426008495)
                      ·
                        rfl

theorem cell23_7122115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_7122115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122115 prefixEnd_7122115 := by exact prefixLift 7122115
  have htrace : WordTrace (prefixWord ++ tailWord_7122115) baseStart_7122115 baseEnd_7122115 := by
    simpa [prefixWord, tailWord_7122115, baseEnd_7122115] using wordTrace_append hprefix tailTrace_7122115
  have hstable : (prefixWord ++ tailWord_7122115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122115).length < 2 ^ (prefixWord ++ tailWord_7122115).sum := by decide
  have hdescent : baseEnd_7122115 < baseStart_7122115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122122 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_7122122 : Nat := 118140960795 + 7122122 * 2 ^ 59
def prefixEnd_7122122 : Nat := 4983230072969 + 3 ^ 40 * 7122122 * 2
def baseEnd_7122122 : Nat := 3657071865961088898620963

theorem tailTrace_7122122 : CollatzResearch.WordTrace tailWord_7122122 prefixEnd_7122122 3657071865961088898620963 := by
  unfold tailWord_7122122
  simp only [CollatzResearch.WordTrace]
  refine ⟨64941282475943957610804155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173176753269183886962144413 64941282475943957610804155)
  ·
    refine ⟨97411923713915936416206233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64941282475943957610804155 97411923713915936416206233)
    ·
      refine ⟨73058942785436952312154675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97411923713915936416206233 73058942785436952312154675)
      ·
        refine ⟨109588414178155428468232013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73058942785436952312154675 109588414178155428468232013)
        ·
          refine ⟨41095655316808285675587005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109588414178155428468232013 41095655316808285675587005)
          ·
            refine ⟨15410870743803107128345127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41095655316808285675587005 15410870743803107128345127)
            ·
              refine ⟨23116306115704660692517691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15410870743803107128345127 23116306115704660692517691)
              ·
                refine ⟨34674459173556991038776537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23116306115704660692517691 34674459173556991038776537)
                ·
                  refine ⟨26005844380167743279082403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34674459173556991038776537 26005844380167743279082403)
                  ·
                    refine ⟨39008766570251614918623605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26005844380167743279082403 39008766570251614918623605)
                    ·
                      refine ⟨3657071865961088898620963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39008766570251614918623605 3657071865961088898620963)
                      ·
                        rfl

theorem cell23_7122122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_7122122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122122 prefixEnd_7122122 := by exact prefixLift 7122122
  have htrace : WordTrace (prefixWord ++ tailWord_7122122) baseStart_7122122 baseEnd_7122122 := by
    simpa [prefixWord, tailWord_7122122, baseEnd_7122122] using wordTrace_append hprefix tailTrace_7122122
  have hstable : (prefixWord ++ tailWord_7122122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122122).length < 2 ^ (prefixWord ++ tailWord_7122122).sum := by decide
  have hdescent : baseEnd_7122122 < baseStart_7122122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122152 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_7122152 : Nat := 118140960795 + 7122152 * 2 ^ 59
def prefixEnd_7122152 : Nat := 4983230072969 + 3 ^ 40 * 7122152 * 2
def baseEnd_7122152 : Nat := 3657087270380723781245825

theorem tailTrace_7122152 : CollatzResearch.WordTrace tailWord_7122152 prefixEnd_7122152 3657087270380723781245825 := by
  unfold tailWord_7122152
  simp only [CollatzResearch.WordTrace]
  refine ⟨129883112046833572783404355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173177482729111430377872473 129883112046833572783404355)
  ·
    refine ⟨194824668070250359175106533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129883112046833572783404355 194824668070250359175106533)
    ·
      refine ⟨36529625263171942345332475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194824668070250359175106533 36529625263171942345332475)
      ·
        refine ⟨54794437894757913517998713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36529625263171942345332475 54794437894757913517998713)
        ·
          refine ⟨41095828421068435138499035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54794437894757913517998713 41095828421068435138499035)
          ·
            refine ⟨61643742631602652707748553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41095828421068435138499035 61643742631602652707748553)
            ·
              refine ⟨46232806973701989530811415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61643742631602652707748553 46232806973701989530811415)
              ·
                refine ⟨69349210460552984296217123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46232806973701989530811415 69349210460552984296217123)
                ·
                  refine ⟨104023815690829476444325685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69349210460552984296217123 104023815690829476444325685)
                  ·
                    refine ⟨9752232721015263416655533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104023815690829476444325685 9752232721015263416655533)
                    ·
                      refine ⟨3657087270380723781245825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9752232721015263416655533 3657087270380723781245825)
                      ·
                        rfl

theorem cell23_7122152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_7122152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122152 prefixEnd_7122152 := by exact prefixLift 7122152
  have htrace : WordTrace (prefixWord ++ tailWord_7122152) baseStart_7122152 baseEnd_7122152 := by
    simpa [prefixWord, tailWord_7122152, baseEnd_7122152] using wordTrace_append hprefix tailTrace_7122152
  have hstable : (prefixWord ++ tailWord_7122152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122152).length < 2 ^ (prefixWord ++ tailWord_7122152).sum := by decide
  have hdescent : baseEnd_7122152 < baseStart_7122152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122226 : List Nat := [3, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4]
def baseStart_7122226 : Nat := 118140960795 + 7122226 * 2 ^ 59
def prefixEnd_7122226 : Nat := 4983230072969 + 3 ^ 40 * 7122226 * 2
def baseEnd_7122226 : Nat := 3657125267949156491720485

theorem tailTrace_7122226 : CollatzResearch.WordTrace tailWord_7122226 prefixEnd_7122226 3657125267949156491720485 := by
  unfold tailWord_7122226
  simp only [CollatzResearch.WordTrace]
  refine ⟨64942230773849764051250633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173179282063599370803335021 64942230773849764051250633)
  ·
    refine ⟨48706673080387323038437975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64942230773849764051250633 48706673080387323038437975)
    ·
      refine ⟨73060009620580984557656963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48706673080387323038437975 73060009620580984557656963)
      ·
        refine ⟨109590014430871476836485445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73060009620580984557656963 109590014430871476836485445)
        ·
          refine ⟨20548127705788401906841021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109590014430871476836485445 20548127705788401906841021)
          ·
            refine ⟨7705547889670650715065383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20548127705788401906841021 7705547889670650715065383)
            ·
              refine ⟨11558321834505976072598075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7705547889670650715065383 11558321834505976072598075)
              ·
                refine ⟨17337482751758964108897113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11558321834505976072598075 17337482751758964108897113)
                ·
                  refine ⟨13003112063819223081672835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17337482751758964108897113 13003112063819223081672835)
                  ·
                    refine ⟨19504668095728834622509253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13003112063819223081672835 19504668095728834622509253)
                    ·
                      refine ⟨3657125267949156491720485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19504668095728834622509253 3657125267949156491720485)
                      ·
                        rfl

theorem cell23_7122226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_7122226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122226 prefixEnd_7122226 := by exact prefixLift 7122226
  have htrace : WordTrace (prefixWord ++ tailWord_7122226) baseStart_7122226 baseEnd_7122226 := by
    simpa [prefixWord, tailWord_7122226, baseEnd_7122226] using wordTrace_append hprefix tailTrace_7122226
  have hstable : (prefixWord ++ tailWord_7122226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122226).length < 2 ^ (prefixWord ++ tailWord_7122226).sum := by decide
  have hdescent : baseEnd_7122226 < baseStart_7122226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122229 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_7122229 : Nat := 118140960795 + 7122229 * 2 ^ 59
def prefixEnd_7122229 : Nat := 4983230072969 + 3 ^ 40 * 7122229 * 2
def baseEnd_7122229 : Nat := 3657126808391119979982971

theorem tailTrace_7122229 : CollatzResearch.WordTrace tailWord_7122229 prefixEnd_7122229 3657126808391119979982971 := by
  unfold tailWord_7122229
  simp only [CollatzResearch.WordTrace]
  refine ⟨259769032514388187717361741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173179355009592125144907827 259769032514388187717361741)
  ·
    refine ⟨97413387192895570394010653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259769032514388187717361741 97413387192895570394010653)
    ·
      refine ⟨36530020197335838897753995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97413387192895570394010653 36530020197335838897753995)
      ·
        refine ⟨54795030296003758346630993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36530020197335838897753995 54795030296003758346630993)
        ·
          refine ⟨41096272722002818759973245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54795030296003758346630993 41096272722002818759973245)
          ·
            refine ⟨15411102270751057034989967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41096272722002818759973245 15411102270751057034989967)
            ·
              refine ⟨23116653406126585552484951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15411102270751057034989967 23116653406126585552484951)
              ·
                refine ⟨34674980109189878328727427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23116653406126585552484951 34674980109189878328727427)
                ·
                  refine ⟨52012470163784817493091141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34674980109189878328727427 52012470163784817493091141)
                  ·
                    refine ⟨9752338155709653279954589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52012470163784817493091141 9752338155709653279954589)
                    ·
                      refine ⟨3657126808391119979982971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9752338155709653279954589 3657126808391119979982971)
                      ·
                        rfl

theorem cell23_7122229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_7122229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122229 prefixEnd_7122229 := by exact prefixLift 7122229
  have htrace : WordTrace (prefixWord ++ tailWord_7122229) baseStart_7122229 baseEnd_7122229 := by
    simpa [prefixWord, tailWord_7122229, baseEnd_7122229] using wordTrace_append hprefix tailTrace_7122229
  have hstable : (prefixWord ++ tailWord_7122229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122229).length < 2 ^ (prefixWord ++ tailWord_7122229).sum := by decide
  have hdescent : baseEnd_7122229 < baseStart_7122229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122236 : List Nat := [2, 2, 2, 2, 1, 3, 1, 5, 1, 4]
def baseStart_7122236 : Nat := 118140960795 + 7122236 * 2 ^ 59
def prefixEnd_7122236 : Nat := 4983230072969 + 3 ^ 40 * 7122236 * 2
def baseEnd_7122236 : Nat := 1219043467585233817531813

theorem tailTrace_7122236 : CollatzResearch.WordTrace tailWord_7122236 prefixEnd_7122236 1219043467585233817531813 := by
  unfold tailWord_7122236
  simp only [CollatzResearch.WordTrace]
  refine ⟨129884643912681413956433281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173179525216908551941911041 129884643912681413956433281)
  ·
    refine ⟨97413482934511060467324961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129884643912681413956433281 97413482934511060467324961)
    ·
      refine ⟨73060112200883295350493721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97413482934511060467324961 73060112200883295350493721)
      ·
        refine ⟨54795084150662471512870291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73060112200883295350493721 54795084150662471512870291)
        ·
          refine ⟨82192626225993707269305437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54795084150662471512870291 82192626225993707269305437)
          ·
            refine ⟨30822234834747640225989539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82192626225993707269305437 30822234834747640225989539)
            ·
              refine ⟨46233352252121460338984309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30822234834747640225989539 46233352252121460338984309)
              ·
                refine ⟨4334376773636386906779779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46233352252121460338984309 4334376773636386906779779)
                ·
                  refine ⟨6501565160454580360169669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4334376773636386906779779 6501565160454580360169669)
                  ·
                    refine ⟨1219043467585233817531813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6501565160454580360169669 1219043467585233817531813)
                    ·
                      rfl

theorem cell23_7122236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_7122236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122236 prefixEnd_7122236 := by exact prefixLift 7122236
  have htrace : WordTrace (prefixWord ++ tailWord_7122236) baseStart_7122236 baseEnd_7122236 := by
    simpa [prefixWord, tailWord_7122236, baseEnd_7122236] using wordTrace_append hprefix tailTrace_7122236
  have hstable : (prefixWord ++ tailWord_7122236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122236).length < 2 ^ (prefixWord ++ tailWord_7122236).sum := by decide
  have hdescent : baseEnd_7122236 < baseStart_7122236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122252 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 1, 2, 6]
def baseStart_7122252 : Nat := 118140960795 + 7122252 * 2 ^ 59
def prefixEnd_7122252 : Nat := 4983230072969 + 3 ^ 40 * 7122252 * 2
def baseEnd_7122252 : Nat := 3657138618446173389995365

theorem tailTrace_7122252 : CollatzResearch.WordTrace tailWord_7122252 prefixEnd_7122252 3657138618446173389995365 := by
  unfold tailWord_7122252
  simp only [CollatzResearch.WordTrace]
  refine ⟨129884935696652431322724505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173179914262203241763632673 129884935696652431322724505)
  ·
    refine ⟨97413701772489323492043379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129884935696652431322724505 97413701772489323492043379)
    ·
      refine ⟨146120552658733985238065069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97413701772489323492043379 146120552658733985238065069)
      ·
        refine ⟨54795207247025244464274401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146120552658733985238065069 54795207247025244464274401)
        ·
          refine ⟨41096405435268933348205801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54795207247025244464274401 41096405435268933348205801)
          ·
            refine ⟨30822304076451700011154351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41096405435268933348205801 30822304076451700011154351)
            ·
              refine ⟨46233456114677550016731527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30822304076451700011154351 46233456114677550016731527)
              ·
                refine ⟨69350184172016325025097291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46233456114677550016731527 69350184172016325025097291)
                ·
                  refine ⟨104025276258024487537645937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69350184172016325025097291 104025276258024487537645937)
                  ·
                    refine ⟨78018957193518365653234453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104025276258024487537645937 78018957193518365653234453)
                    ·
                      refine ⟨3657138618446173389995365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78018957193518365653234453 3657138618446173389995365)
                      ·
                        rfl

theorem cell23_7122252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_7122252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122252 prefixEnd_7122252 := by exact prefixLift 7122252
  have htrace : WordTrace (prefixWord ++ tailWord_7122252) baseStart_7122252 baseEnd_7122252 := by
    simpa [prefixWord, tailWord_7122252, baseEnd_7122252] using wordTrace_append hprefix tailTrace_7122252
  have hstable : (prefixWord ++ tailWord_7122252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122252).length < 2 ^ (prefixWord ++ tailWord_7122252).sum := by decide
  have hdescent : baseEnd_7122252 < baseStart_7122252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122276 : List Nat := [2, 3, 1, 1, 3, 2, 2, 2, 3, 1, 3]
def baseStart_7122276 : Nat := 118140960795 + 7122276 * 2 ^ 59
def prefixEnd_7122276 : Nat := 4983230072969 + 3 ^ 40 * 7122276 * 2
def baseEnd_7122276 : Nat := 3657150941981881296095255

theorem tailTrace_7122276 : CollatzResearch.WordTrace tailWord_7122276 prefixEnd_7122276 3657150941981881296095255 := by
  unfold tailWord_7122276
  simp only [CollatzResearch.WordTrace]
  refine ⟨129885373372608957372161341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173180497830145276496215121 129885373372608957372161341)
  ·
    refine ⟨48707015014728359014560503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129885373372608957372161341 48707015014728359014560503)
    ·
      refine ⟨73060522522092538521840755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48707015014728359014560503 73060522522092538521840755)
      ·
        refine ⟨109590783783138807782761133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73060522522092538521840755 109590783783138807782761133)
        ·
          refine ⟨41096543918677052918535425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109590783783138807782761133 41096543918677052918535425)
          ·
            refine ⟨30822407939007789688901569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41096543918677052918535425 30822407939007789688901569)
            ·
              refine ⟨23116805954255842266676177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30822407939007789688901569 23116805954255842266676177)
              ·
                refine ⟨17337604465691881700007133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23116805954255842266676177 17337604465691881700007133)
                ·
                  refine ⟨6501601674634455637502675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17337604465691881700007133 6501601674634455637502675)
                  ·
                    refine ⟨9752402511951683456254013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6501601674634455637502675 9752402511951683456254013)
                    ·
                      refine ⟨3657150941981881296095255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9752402511951683456254013 3657150941981881296095255)
                      ·
                        rfl

theorem cell23_7122276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_7122276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122276 prefixEnd_7122276 := by exact prefixLift 7122276
  have htrace : WordTrace (prefixWord ++ tailWord_7122276) baseStart_7122276 baseEnd_7122276 := by
    simpa [prefixWord, tailWord_7122276, baseEnd_7122276] using wordTrace_append hprefix tailTrace_7122276
  have hstable : (prefixWord ++ tailWord_7122276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122276).length < 2 ^ (prefixWord ++ tailWord_7122276).sum := by decide
  have hdescent : baseEnd_7122276 < baseStart_7122276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122299 : List Nat := [1, 1, 1, 1, 1, 6, 1, 5, 1, 1, 4]
def baseStart_7122299 : Nat := 118140960795 + 7122299 * 2 ^ 59
def prefixEnd_7122299 : Nat := 4983230072969 + 3 ^ 40 * 7122299 * 2
def baseEnd_7122299 : Nat := 3657162752036934706107649

theorem tailTrace_7122299 : CollatzResearch.WordTrace tailWord_7122299 prefixEnd_7122299 3657162752036934706107649 := by
  unfold tailWord_7122299
  simp only [CollatzResearch.WordTrace]
  refine ⟨259771585624134589672409951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173181057082756393114939967 259771585624134589672409951)
  ·
    refine ⟨389657378436201884508614927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259771585624134589672409951 389657378436201884508614927)
    ·
      refine ⟨584486067654302826762922391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389657378436201884508614927 584486067654302826762922391)
      ·
        refine ⟨876729101481454240144383587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584486067654302826762922391 876729101481454240144383587)
        ·
          refine ⟨1315093652222181360216575381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876729101481454240144383587 1315093652222181360216575381)
          ·
            refine ⟨61645014947914751260151971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1315093652222181360216575381 61645014947914751260151971)
            ·
              refine ⟨92467522421872126890227957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61645014947914751260151971 92467522421872126890227957)
              ·
                refine ⟨8668830227050511895958871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92467522421872126890227957 8668830227050511895958871)
                ·
                  refine ⟨13003245340575767843938307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8668830227050511895958871 13003245340575767843938307)
                  ·
                    refine ⟨19504868010863651765907461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13003245340575767843938307 19504868010863651765907461)
                    ·
                      refine ⟨3657162752036934706107649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19504868010863651765907461 3657162752036934706107649)
                      ·
                        rfl

theorem cell23_7122299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 1, 4].length) (baseStart_7122299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122299 prefixEnd_7122299 := by exact prefixLift 7122299
  have htrace : WordTrace (prefixWord ++ tailWord_7122299) baseStart_7122299 baseEnd_7122299 := by
    simpa [prefixWord, tailWord_7122299, baseEnd_7122299] using wordTrace_append hprefix tailTrace_7122299
  have hstable : (prefixWord ++ tailWord_7122299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122299).length < 2 ^ (prefixWord ++ tailWord_7122299).sum := by decide
  have hdescent : baseEnd_7122299 < baseStart_7122299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122309 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 4, 4]
def baseStart_7122309 : Nat := 118140960795 + 7122309 * 2 ^ 59
def prefixEnd_7122309 : Nat := 4983230072969 + 3 ^ 40 * 7122309 * 2
def baseEnd_7122309 : Nat := 1219055962281159888994201

theorem tailTrace_7122309 : CollatzResearch.WordTrace tailWord_7122309 prefixEnd_7122309 1219055962281159888994201 := by
  unfold tailWord_7122309
  simp only [CollatzResearch.WordTrace]
  refine ⟨259771950354098361380273981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173181300236065574253515987 259771950354098361380273981)
  ·
    refine ⟨97414481382786885517602743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259771950354098361380273981 97414481382786885517602743)
    ·
      refine ⟨146121722074180328276404115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97414481382786885517602743 146121722074180328276404115)
      ·
        refine ⟨219182583111270492414606173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146121722074180328276404115 219182583111270492414606173)
        ·
          refine ⟨82193468666726434655477315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219182583111270492414606173 82193468666726434655477315)
          ·
            refine ⟨123290203000089651983215973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82193468666726434655477315 123290203000089651983215973)
            ·
              refine ⟨23116913062516809746852995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123290203000089651983215973 23116913062516809746852995)
              ·
                refine ⟨34675369593775214620279493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23116913062516809746852995 34675369593775214620279493)
                ·
                  refine ⟨6501631798832852741302405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34675369593775214620279493 6501631798832852741302405)
                  ·
                    refine ⟨1219055962281159888994201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6501631798832852741302405 1219055962281159888994201)
                    ·
                      rfl

theorem cell23_7122309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_7122309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122309 prefixEnd_7122309 := by exact prefixLift 7122309
  have htrace : WordTrace (prefixWord ++ tailWord_7122309) baseStart_7122309 baseEnd_7122309 := by
    simpa [prefixWord, tailWord_7122309, baseEnd_7122309] using wordTrace_append hprefix tailTrace_7122309
  have hstable : (prefixWord ++ tailWord_7122309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122309).length < 2 ^ (prefixWord ++ tailWord_7122309).sum := by decide
  have hdescent : baseEnd_7122309 < baseStart_7122309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122333 : List Nat := [1, 4, 2, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_7122333 : Nat := 118140960795 + 7122333 * 2 ^ 59
def prefixEnd_7122333 : Nat := 4983230072969 + 3 ^ 40 * 7122333 * 2
def baseEnd_7122333 : Nat := 3657180210379187573082493

theorem tailTrace_7122333 : CollatzResearch.WordTrace tailWord_7122333 prefixEnd_7122333 3657180210379187573082493 := by
  unfold tailWord_7122333
  simp only [CollatzResearch.WordTrace]
  refine ⟨259772825706011413479147653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173181883804007608986098435 259772825706011413479147653)
  ·
    refine ⟨48707404819877140027340185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259772825706011413479147653 48707404819877140027340185)
    ·
      refine ⟨36530553614907855020505139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48707404819877140027340185 36530553614907855020505139)
      ·
        refine ⟨54795830422361782530757709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36530553614907855020505139 54795830422361782530757709)
        ·
          refine ⟨20548436408385668449034141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54795830422361782530757709 20548436408385668449034141)
          ·
            refine ⟨7705663653144625668387803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20548436408385668449034141 7705663653144625668387803)
            ·
              refine ⟨11558495479716938502581705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7705663653144625668387803 11558495479716938502581705)
              ·
                refine ⟨8668871609787703876936279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11558495479716938502581705 8668871609787703876936279)
                ·
                  refine ⟨13003307414681555815404419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8668871609787703876936279 13003307414681555815404419)
                  ·
                    refine ⟨19504961122022333723106629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13003307414681555815404419 19504961122022333723106629)
                    ·
                      refine ⟨3657180210379187573082493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19504961122022333723106629 3657180210379187573082493)
                      ·
                        rfl

theorem cell23_7122333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_7122333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122333 prefixEnd_7122333 := by exact prefixLift 7122333
  have htrace : WordTrace (prefixWord ++ tailWord_7122333) baseStart_7122333 baseEnd_7122333 := by
    simpa [prefixWord, tailWord_7122333, baseEnd_7122333] using wordTrace_append hprefix tailTrace_7122333
  have hstable : (prefixWord ++ tailWord_7122333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122333).length < 2 ^ (prefixWord ++ tailWord_7122333).sum := by decide
  have hdescent : baseEnd_7122333 < baseStart_7122333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122353 : List Nat := [1, 2, 2, 4, 1, 1, 5, 1, 1, 2, 3]
def baseStart_7122353 : Nat := 118140960795 + 7122353 * 2 ^ 59
def prefixEnd_7122353 : Nat := 4983230072969 + 3 ^ 40 * 7122353 * 2
def baseEnd_7122353 : Nat := 3657190479992277494832401

theorem tailTrace_7122353 : CollatzResearch.WordTrace tailWord_7122353 prefixEnd_7122353 3657190479992277494832401 := by
  unfold tailWord_7122353
  simp only [CollatzResearch.WordTrace]
  refine ⟨259773555165938956894875713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173182370110625971263250475 259773555165938956894875713)
  ·
    refine ⟨194830166374454217671156785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259773555165938956894875713 194830166374454217671156785)
    ·
      refine ⟨146122624780840663253367589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194830166374454217671156785 146122624780840663253367589)
      ·
        refine ⟨27397992146407624360006423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146122624780840663253367589 27397992146407624360006423)
        ·
          refine ⟨41096988219611436540009635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27397992146407624360006423 41096988219611436540009635)
          ·
            refine ⟨61645482329417154810014453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41096988219611436540009635 61645482329417154810014453)
            ·
              refine ⟨5779263968382858263438855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61645482329417154810014453 5779263968382858263438855)
              ·
                refine ⟨8668895952574287395158283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5779263968382858263438855 8668895952574287395158283)
                ·
                  refine ⟨13003343928861431092737425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8668895952574287395158283 13003343928861431092737425)
                  ·
                    refine ⟨9752507946646073319553069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13003343928861431092737425 9752507946646073319553069)
                    ·
                      refine ⟨3657190479992277494832401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9752507946646073319553069 3657190479992277494832401)
                      ·
                        rfl

theorem cell23_7122353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_7122353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122353 prefixEnd_7122353 := by exact prefixLift 7122353
  have htrace : WordTrace (prefixWord ++ tailWord_7122353) baseStart_7122353 baseEnd_7122353 := by
    simpa [prefixWord, tailWord_7122353, baseEnd_7122353] using wordTrace_append hprefix tailTrace_7122353
  have hstable : (prefixWord ++ tailWord_7122353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122353).length < 2 ^ (prefixWord ++ tailWord_7122353).sum := by decide
  have hdescent : baseEnd_7122353 < baseStart_7122353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122362 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7]
def baseStart_7122362 : Nat := 118140960795 + 7122362 * 2 ^ 59
def prefixEnd_7122362 : Nat := 4983230072969 + 3 ^ 40 * 7122362 * 2
def baseEnd_7122362 : Nat := 3657195101318167959619859

theorem tailTrace_7122362 : CollatzResearch.WordTrace tailWord_7122362 prefixEnd_7122362 3657195101318167959619859 := by
  unfold tailWord_7122362
  simp only [CollatzResearch.WordTrace]
  refine ⟨64943470855726587857988335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173182588948604234287968893 64943470855726587857988335)
  ·
    refine ⟨97415206283589881786982503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64943470855726587857988335 97415206283589881786982503)
    ·
      refine ⟨146122809425384822680473755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97415206283589881786982503 146122809425384822680473755)
      ·
        refine ⟨219184214138077234020710633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146122809425384822680473755 219184214138077234020710633)
        ·
          refine ⟨164388160603557925515532975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219184214138077234020710633 164388160603557925515532975)
          ·
            refine ⟨246582240905336888273299463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164388160603557925515532975 246582240905336888273299463)
            ·
              refine ⟨369873361358005332409949195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246582240905336888273299463 369873361358005332409949195)
              ·
                refine ⟨554810042037007998614923793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369873361358005332409949195 554810042037007998614923793)
                ·
                  refine ⟨416107531527755998961192845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 554810042037007998614923793 416107531527755998961192845)
                  ·
                    refine ⟨156040324322908499610447317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 416107531527755998961192845 156040324322908499610447317)
                    ·
                      refine ⟨3657195101318167959619859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 156040324322908499610447317 3657195101318167959619859)
                      ·
                        rfl

theorem cell23_7122362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_7122362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122362 prefixEnd_7122362 := by exact prefixLift 7122362
  have htrace : WordTrace (prefixWord ++ tailWord_7122362) baseStart_7122362 baseEnd_7122362 := by
    simpa [prefixWord, tailWord_7122362, baseEnd_7122362] using wordTrace_append hprefix tailTrace_7122362
  have hstable : (prefixWord ++ tailWord_7122362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122362).length < 2 ^ (prefixWord ++ tailWord_7122362).sum := by decide
  have hdescent : baseEnd_7122362 < baseStart_7122362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122376 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 5, 3, 2]
def baseStart_7122376 : Nat := 118140960795 + 7122376 * 2 ^ 59
def prefixEnd_7122376 : Nat := 4983230072969 + 3 ^ 40 * 7122376 * 2
def baseEnd_7122376 : Nat := 3657202290047330904844795

theorem tailTrace_7122376 : CollatzResearch.WordTrace tailWord_7122376 prefixEnd_7122376 3657202290047330904844795 := by
  unfold tailWord_7122376
  simp only [CollatzResearch.WordTrace]
  refine ⟨129887197022427815911481491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173182929363237087881975321 129887197022427815911481491)
  ·
    refine ⟨194830795533641723867222237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129887197022427815911481491 194830795533641723867222237)
    ·
      refine ⟨73061548325115646450208339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194830795533641723867222237 73061548325115646450208339)
      ·
        refine ⟨109592322487673469675312509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73061548325115646450208339 109592322487673469675312509)
        ·
          refine ⟨41097120932877551128242191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109592322487673469675312509 41097120932877551128242191)
          ·
            refine ⟨61645681399316326692363287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41097120932877551128242191 61645681399316326692363287)
            ·
              refine ⟨92468522098974490038544931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61645681399316326692363287 92468522098974490038544931)
              ·
                refine ⟨138702783148461735057817397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92468522098974490038544931 138702783148461735057817397)
                ·
                  refine ⟨13003385920168287661670381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138702783148461735057817397 13003385920168287661670381)
                  ·
                    refine ⟨4876269720063107873126393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13003385920168287661670381 4876269720063107873126393)
                    ·
                      refine ⟨3657202290047330904844795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4876269720063107873126393 3657202290047330904844795)
                      ·
                        rfl

theorem cell23_7122376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_7122376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122376 prefixEnd_7122376 := by exact prefixLift 7122376
  have htrace : WordTrace (prefixWord ++ tailWord_7122376) baseStart_7122376 baseEnd_7122376 := by
    simpa [prefixWord, tailWord_7122376, baseEnd_7122376] using wordTrace_append hprefix tailTrace_7122376
  have hstable : (prefixWord ++ tailWord_7122376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122376).length < 2 ^ (prefixWord ++ tailWord_7122376).sum := by decide
  have hdescent : baseEnd_7122376 < baseStart_7122376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122389 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_7122389 : Nat := 118140960795 + 7122389 * 2 ^ 59
def prefixEnd_7122389 : Nat := 4983230072969 + 3 ^ 40 * 7122389 * 2
def baseEnd_7122389 : Nat := 3657208965295839353982235

theorem tailTrace_7122389 : CollatzResearch.WordTrace tailWord_7122389 prefixEnd_7122389 3657208965295839353982235 := by
  unfold tailWord_7122389
  simp only [CollatzResearch.WordTrace]
  refine ⟨259774868193808535043186221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173183245462539023362124147 259774868193808535043186221)
  ·
    refine ⟨97415575572678200641194833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259774868193808535043186221 97415575572678200641194833)
    ·
      refine ⟨73061681679508650480896125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97415575572678200641194833 73061681679508650480896125)
      ·
        refine ⟨27398130629815743930336047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73061681679508650480896125 27398130629815743930336047)
        ·
          refine ⟨41097195944723615895504071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27398130629815743930336047 41097195944723615895504071)
          ·
            refine ⟨61645793917085423843256107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41097195944723615895504071 61645793917085423843256107)
            ·
              refine ⟨92468690875628135764884161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61645793917085423843256107 92468690875628135764884161)
              ·
                refine ⟨69351518156721101823663121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92468690875628135764884161 69351518156721101823663121)
                ·
                  refine ⟨52013638617540826367747341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69351518156721101823663121 52013638617540826367747341)
                  ·
                    refine ⟨19505114481577809887905253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52013638617540826367747341 19505114481577809887905253)
                    ·
                      refine ⟨3657208965295839353982235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19505114481577809887905253 3657208965295839353982235)
                      ·
                        rfl

theorem cell23_7122389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_7122389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122389 prefixEnd_7122389 := by exact prefixLift 7122389
  have htrace : WordTrace (prefixWord ++ tailWord_7122389) baseStart_7122389 baseEnd_7122389 := by
    simpa [prefixWord, tailWord_7122389, baseEnd_7122389] using wordTrace_append hprefix tailTrace_7122389
  have hstable : (prefixWord ++ tailWord_7122389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122389).length < 2 ^ (prefixWord ++ tailWord_7122389).sum := by decide
  have hdescent : baseEnd_7122389 < baseStart_7122389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122410 : List Nat := [3, 1, 3, 1, 4, 1, 1, 3, 1, 3, 2]
def baseStart_7122410 : Nat := 118140960795 + 7122410 * 2 ^ 59
def prefixEnd_7122410 : Nat := 4983230072969 + 3 ^ 40 * 7122410 * 2
def baseEnd_7122410 : Nat := 3657219748389583771819639

theorem tailTrace_7122410 : CollatzResearch.WordTrace tailWord_7122410 prefixEnd_7122410 3657219748389583771819639 := by
  unfold tailWord_7122410
  simp only [CollatzResearch.WordTrace]
  refine ⟨64943908531683113907425171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173183756084488303753133789 64943908531683113907425171)
  ·
    refine ⟨97415862797524670861137757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64943908531683113907425171 97415862797524670861137757)
    ·
      refine ⟨36530948549071751572926659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97415862797524670861137757 36530948549071751572926659)
      ·
        refine ⟨54796422823607627359389989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36530948549071751572926659 54796422823607627359389989)
        ·
          refine ⟨10274329279426430129885623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54796422823607627359389989 10274329279426430129885623)
          ·
            refine ⟨15411493919139645194828435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10274329279426430129885623 15411493919139645194828435)
            ·
              refine ⟨23117240878709467792242653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15411493919139645194828435 23117240878709467792242653)
              ·
                refine ⟨8668965329516050422090995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23117240878709467792242653 8668965329516050422090995)
                ·
                  refine ⟨13003447994274075633136493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8668965329516050422090995 13003447994274075633136493)
                  ·
                    refine ⟨4876292997852778362426185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13003447994274075633136493 4876292997852778362426185)
                    ·
                      refine ⟨3657219748389583771819639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4876292997852778362426185 3657219748389583771819639)
                      ·
                        rfl

theorem cell23_7122410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_7122410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122410 prefixEnd_7122410 := by exact prefixLift 7122410
  have htrace : WordTrace (prefixWord ++ tailWord_7122410) baseStart_7122410 baseEnd_7122410 := by
    simpa [prefixWord, tailWord_7122410, baseEnd_7122410] using wordTrace_append hprefix tailTrace_7122410
  have hstable : (prefixWord ++ tailWord_7122410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122410).length < 2 ^ (prefixWord ++ tailWord_7122410).sum := by decide
  have hdescent : baseEnd_7122410 < baseStart_7122410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122423 : List Nat := [1, 1, 3, 1, 1, 1, 1, 8, 2, 2, 2]
def baseStart_7122423 : Nat := 118140960795 + 7122423 * 2 ^ 59
def prefixEnd_7122423 : Nat := 4983230072969 + 3 ^ 40 * 7122423 * 2
def baseEnd_7122423 : Nat := 3657226423638092220957079

theorem tailTrace_7122423 : CollatzResearch.WordTrace tailWord_7122423 prefixEnd_7122423 3657226423638092220957079 := by
  unfold tailWord_7122423
  simp only [CollatzResearch.WordTrace]
  refine ⟨259776108275685358849923923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173184072183790239233282615 259776108275685358849923923)
  ·
    refine ⟨389664162413528038274885885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259776108275685358849923923 389664162413528038274885885)
    ·
      refine ⟨146124060905073014353082207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389664162413528038274885885 146124060905073014353082207)
      ·
        refine ⟨219186091357609521529623311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146124060905073014353082207 219186091357609521529623311)
        ·
          refine ⟨328779137036414282294434967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219186091357609521529623311 328779137036414282294434967)
          ·
            refine ⟨493168705554621423441652451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328779137036414282294434967 493168705554621423441652451)
            ·
              refine ⟨739753058331932135162478677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493168705554621423441652451 739753058331932135162478677)
              ·
                refine ⟨8668981152327329708935297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 739753058331932135162478677 8668981152327329708935297)
                ·
                  refine ⟨6501735864245497281701473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8668981152327329708935297 6501735864245497281701473)
                  ·
                    refine ⟨4876301898184122961276105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6501735864245497281701473 4876301898184122961276105)
                    ·
                      refine ⟨3657226423638092220957079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4876301898184122961276105 3657226423638092220957079)
                      ·
                        rfl

theorem cell23_7122423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 2, 2].length) (baseStart_7122423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122423 prefixEnd_7122423 := by exact prefixLift 7122423
  have htrace : WordTrace (prefixWord ++ tailWord_7122423) baseStart_7122423 baseEnd_7122423 := by
    simpa [prefixWord, tailWord_7122423, baseEnd_7122423] using wordTrace_append hprefix tailTrace_7122423
  have hstable : (prefixWord ++ tailWord_7122423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122423).length < 2 ^ (prefixWord ++ tailWord_7122423).sum := by decide
  have hdescent : baseEnd_7122423 < baseStart_7122423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122429 : List Nat := [1, 4, 1, 1, 1, 4, 1, 3, 7]
def baseStart_7122429 : Nat := 118140960795 + 7122429 * 2 ^ 59
def prefixEnd_7122429 : Nat := 4983230072969 + 3 ^ 40 * 7122429 * 2
def baseEnd_7122429 : Nat := 406358833835779910831339

theorem tailTrace_7122429 : CollatzResearch.WordTrace tailWord_7122429 prefixEnd_7122429 406358833835779910831339 := by
  unfold tailWord_7122429
  simp only [CollatzResearch.WordTrace]
  refine ⟨259776327113663621874642341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173184218075775747916428227 259776327113663621874642341)
  ·
    refine ⟨48708061333811929101495439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259776327113663621874642341 48708061333811929101495439)
    ·
      refine ⟨73062092000717893652243159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48708061333811929101495439 73062092000717893652243159)
      ·
        refine ⟨109593138001076840478364739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73062092000717893652243159 109593138001076840478364739)
        ·
          refine ⟨164389707001615260717547109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109593138001076840478364739 164389707001615260717547109)
          ·
            refine ⟨30823070062802861384540083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164389707001615260717547109 30823070062802861384540083)
            ·
              refine ⟨46234605094204292076810125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30823070062802861384540083 46234605094204292076810125)
              ·
                refine ⟨17337976910326609528803797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46234605094204292076810125 17337976910326609528803797)
                ·
                  refine ⟨406358833835779910831339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17337976910326609528803797 406358833835779910831339)
                  ·
                    rfl

theorem cell23_7122429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_7122429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122429 prefixEnd_7122429 := by exact prefixLift 7122429
  have htrace : WordTrace (prefixWord ++ tailWord_7122429) baseStart_7122429 baseEnd_7122429 := by
    simpa [prefixWord, tailWord_7122429, baseEnd_7122429] using wordTrace_append hprefix tailTrace_7122429
  have hstable : (prefixWord ++ tailWord_7122429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122429).length < 2 ^ (prefixWord ++ tailWord_7122429).sum := by decide
  have hdescent : baseEnd_7122429 < baseStart_7122429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122469 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 1, 2, 5]
def baseStart_7122469 : Nat := 118140960795 + 7122469 * 2 ^ 59
def prefixEnd_7122469 : Nat := 4983230072969 + 3 ^ 40 * 7122469 * 2
def baseEnd_7122469 : Nat := 3657250043748199040981867

theorem tailTrace_7122469 : CollatzResearch.WordTrace tailWord_7122469 prefixEnd_7122469 3657250043748199040981867 := by
  unfold tailWord_7122469
  simp only [CollatzResearch.WordTrace]
  refine ⟨259777786033518708706098461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173185190689012472470732307 259777786033518708706098461)
  ·
    refine ⟨97416669762569515764786923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259777786033518708706098461 97416669762569515764786923)
    ·
      refine ⟨146125004643854273647180385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97416669762569515764786923 146125004643854273647180385)
      ·
        refine ⟨109593753482890705235385289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146125004643854273647180385 109593753482890705235385289)
        ·
          refine ⟨82195315112168028926538967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109593753482890705235385289 82195315112168028926538967)
          ·
            refine ⟨123292972668252043389808451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82195315112168028926538967 123292972668252043389808451)
            ·
              refine ⟨184939459002378065084712677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123292972668252043389808451 184939459002378065084712677)
              ·
                refine ⟨34676148562945887203383627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184939459002378065084712677 34676148562945887203383627)
                ·
                  refine ⟨52014222844418830805075441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34676148562945887203383627 52014222844418830805075441)
                  ·
                    refine ⟨39010667133314123103806581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52014222844418830805075441 39010667133314123103806581)
                    ·
                      refine ⟨3657250043748199040981867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39010667133314123103806581 3657250043748199040981867)
                      ·
                        rfl

theorem cell23_7122469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_7122469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122469 prefixEnd_7122469 := by exact prefixLift 7122469
  have htrace : WordTrace (prefixWord ++ tailWord_7122469) baseStart_7122469 baseEnd_7122469 := by
    simpa [prefixWord, tailWord_7122469, baseEnd_7122469] using wordTrace_append hprefix tailTrace_7122469
  have hstable : (prefixWord ++ tailWord_7122469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122469).length < 2 ^ (prefixWord ++ tailWord_7122469).sum := by decide
  have hdescent : baseEnd_7122469 < baseStart_7122469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122496 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 1, 6, 2]
def baseStart_7122496 : Nat := 118140960795 + 7122496 * 2 ^ 59
def prefixEnd_7122496 : Nat := 4983230072969 + 3 ^ 40 * 7122496 * 2
def baseEnd_7122496 : Nat := 3657263907725870435344243

theorem tailTrace_7122496 : CollatzResearch.WordTrace tailWord_7122496 prefixEnd_7122496 3657263907725870435344243 := by
  unfold tailWord_7122496
  simp only [CollatzResearch.WordTrace]
  refine ⟨129889385402210446158665671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173185847202947261544887561 129889385402210446158665671)
  ·
    refine ⟨194834078103315669237998507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129889385402210446158665671 194834078103315669237998507)
    ·
      refine ⟨292251117154973503856997761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194834078103315669237998507 292251117154973503856997761)
      ·
        refine ⟨219188337866230127892748321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292251117154973503856997761 219188337866230127892748321)
        ·
          refine ⟨164391253399672595919561241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219188337866230127892748321 164391253399672595919561241)
          ·
            refine ⟨123293440049754446939670931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164391253399672595919561241 123293440049754446939670931)
            ·
              refine ⟨184940160074631670409506397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123293440049754446939670931 184940160074631670409506397)
              ·
                refine ⟨69352560027986876403564899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184940160074631670409506397 69352560027986876403564899)
                ·
                  refine ⟨104028840041980314605347349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69352560027986876403564899 104028840041980314605347349)
                  ·
                    refine ⟨4876351876967827247125657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104028840041980314605347349 4876351876967827247125657)
                    ·
                      refine ⟨3657263907725870435344243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4876351876967827247125657 3657263907725870435344243)
                      ·
                        rfl

theorem cell23_7122496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 1, 6, 2].length) (baseStart_7122496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122496 prefixEnd_7122496 := by exact prefixLift 7122496
  have htrace : WordTrace (prefixWord ++ tailWord_7122496) baseStart_7122496 baseEnd_7122496 := by
    simpa [prefixWord, tailWord_7122496, baseEnd_7122496] using wordTrace_append hprefix tailTrace_7122496
  have hstable : (prefixWord ++ tailWord_7122496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122496).length < 2 ^ (prefixWord ++ tailWord_7122496).sum := by decide
  have hdescent : baseEnd_7122496 < baseStart_7122496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122506 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 5, 4]
def baseStart_7122506 : Nat := 118140960795 + 7122506 * 2 ^ 59
def prefixEnd_7122506 : Nat := 4983230072969 + 3 ^ 40 * 7122506 * 2
def baseEnd_7122506 : Nat := 1219089680844138465406399

theorem tailTrace_7122506 : CollatzResearch.WordTrace tailWord_7122506 prefixEnd_7122506 1219089680844138465406399 := by
  unfold tailWord_7122506
  simp only [CollatzResearch.WordTrace]
  refine ⟨64944783883596166006298843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173186090356256442683463581 64944783883596166006298843)
  ·
    refine ⟨97417175825394249009448265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64944783883596166006298843 97417175825394249009448265)
    ·
      refine ⟨73062881869045686757086199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97417175825394249009448265 73062881869045686757086199)
      ·
        refine ⟨109594322803568530135629299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73062881869045686757086199 109594322803568530135629299)
        ·
          refine ⟨164391484205352795203443949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109594322803568530135629299 164391484205352795203443949)
          ·
            refine ⟨61646806577007298201291481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164391484205352795203443949 61646806577007298201291481)
            ·
              refine ⟨46235104932755473650968611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61646806577007298201291481 46235104932755473650968611)
              ·
                refine ⟨69352657399133210476452917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46235104932755473650968611 69352657399133210476452917)
                ·
                  refine ⟨6501811631168738482167461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69352657399133210476452917 6501811631168738482167461)
                  ·
                    refine ⟨1219089680844138465406399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6501811631168738482167461 1219089680844138465406399)
                    ·
                      rfl

theorem cell23_7122506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_7122506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122506 prefixEnd_7122506 := by exact prefixLift 7122506
  have htrace : WordTrace (prefixWord ++ tailWord_7122506) baseStart_7122506 baseEnd_7122506 := by
    simpa [prefixWord, tailWord_7122506, baseEnd_7122506] using wordTrace_append hprefix tailTrace_7122506
  have hstable : (prefixWord ++ tailWord_7122506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122506).length < 2 ^ (prefixWord ++ tailWord_7122506).sum := by decide
  have hdescent : baseEnd_7122506 < baseStart_7122506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122533 : List Nat := [1, 3, 1, 3, 3, 1, 2, 2, 2, 2, 3]
def baseStart_7122533 : Nat := 118140960795 + 7122533 * 2 ^ 59
def prefixEnd_7122533 : Nat := 4983230072969 + 3 ^ 40 * 7122533 * 2
def baseEnd_7122533 : Nat := 3657282906510086790581573

theorem tailTrace_7122533 : CollatzResearch.WordTrace tailWord_7122533 prefixEnd_7122533 3657282906510086790581573 := by
  unfold tailWord_7122533
  simp only [CollatzResearch.WordTrace]
  refine ⟨259780120305286847636428253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173186746870191231757618835 259780120305286847636428253)
  ·
    refine ⟨97417545114482567863660595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259780120305286847636428253 97417545114482567863660595)
    ·
      refine ⟨146126317671723851795490893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97417545114482567863660595 146126317671723851795490893)
      ·
        refine ⟨54797369126896444423309085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146126317671723851795490893 54797369126896444423309085)
        ·
          refine ⟨20549013422586166658740907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54797369126896444423309085 20549013422586166658740907)
          ·
            refine ⟨30823520133879249988111361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20549013422586166658740907 30823520133879249988111361)
            ·
              refine ⟨23117640100409437491083521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30823520133879249988111361 23117640100409437491083521)
              ·
                refine ⟨17338230075307078118312641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23117640100409437491083521 17338230075307078118312641)
                ·
                  refine ⟨13003672556480308588734481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17338230075307078118312641 13003672556480308588734481)
                  ·
                    refine ⟨9752754417360231441550861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13003672556480308588734481 9752754417360231441550861)
                    ·
                      refine ⟨3657282906510086790581573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9752754417360231441550861 3657282906510086790581573)
                      ·
                        rfl

theorem cell23_7122533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_7122533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122533 prefixEnd_7122533 := by exact prefixLift 7122533
  have htrace : WordTrace (prefixWord ++ tailWord_7122533) baseStart_7122533 baseEnd_7122533 := by
    simpa [prefixWord, tailWord_7122533, baseEnd_7122533] using wordTrace_append hprefix tailTrace_7122533
  have hstable : (prefixWord ++ tailWord_7122533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122533).length < 2 ^ (prefixWord ++ tailWord_7122533).sum := by decide
  have hdescent : baseEnd_7122533 < baseStart_7122533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122559 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 5]
def baseStart_7122559 : Nat := 118140960795 + 7122559 * 2 ^ 59
def prefixEnd_7122559 : Nat := 4983230072969 + 3 ^ 40 * 7122559 * 2
def baseEnd_7122559 : Nat := 3657296257007103688856453

theorem tailTrace_7122559 : CollatzResearch.WordTrace tailWord_7122559 prefixEnd_7122559 3657296257007103688856453 := by
  unfold tailWord_7122559
  simp only [CollatzResearch.WordTrace]
  refine ⟨259781068603192654076874731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173187379068795102717916487 259781068603192654076874731)
  ·
    refine ⟨389671602904788981115312097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259781068603192654076874731 389671602904788981115312097)
    ·
      refine ⟨292253702178591735836484073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389671602904788981115312097 292253702178591735836484073)
      ·
        refine ⟨219190276633943801877363055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292253702178591735836484073 219190276633943801877363055)
        ·
          refine ⟨328785414950915702816044583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219190276633943801877363055 328785414950915702816044583)
          ·
            refine ⟨493178122426373554224066875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328785414950915702816044583 493178122426373554224066875)
            ·
              refine ⟨739767183639560331336100313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493178122426373554224066875 739767183639560331336100313)
              ·
                refine ⟨554825387729670248502075235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 739767183639560331336100313 554825387729670248502075235)
                ·
                  refine ⟨832238081594505372753112853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 554825387729670248502075235 832238081594505372753112853)
                  ·
                    refine ⟨39011160074742439347802165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 832238081594505372753112853 39011160074742439347802165)
                    ·
                      refine ⟨3657296257007103688856453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39011160074742439347802165 3657296257007103688856453)
                      ·
                        rfl

theorem cell23_7122559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_7122559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122559 prefixEnd_7122559 := by exact prefixLift 7122559
  have htrace : WordTrace (prefixWord ++ tailWord_7122559) baseStart_7122559 baseEnd_7122559 := by
    simpa [prefixWord, tailWord_7122559, baseEnd_7122559] using wordTrace_append hprefix tailTrace_7122559
  have hstable : (prefixWord ++ tailWord_7122559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122559).length < 2 ^ (prefixWord ++ tailWord_7122559).sum := by decide
  have hdescent : baseEnd_7122559 < baseStart_7122559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122583 : List Nat := [1, 1, 3, 3, 2, 3, 1, 3, 1, 5]
def baseStart_7122583 : Nat := 118140960795 + 7122583 * 2 ^ 59
def prefixEnd_7122583 : Nat := 4983230072969 + 3 ^ 40 * 7122583 * 2
def baseEnd_7122583 : Nat := 1219102860180937198318781

theorem tailTrace_7122583 : CollatzResearch.WordTrace tailWord_7122583 prefixEnd_7122583 1219102860180937198318781 := by
  unfold tailWord_7122583
  simp only [CollatzResearch.WordTrace]
  refine ⟨259781943955105706175748403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173187962636737137450498935 259781943955105706175748403)
  ·
    refine ⟨389672915932658559263622605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259781943955105706175748403 389672915932658559263622605)
    ·
      refine ⟨146127343474746959723858477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389672915932658559263622605 146127343474746959723858477)
      ·
        refine ⟨54797753803030109896446929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146127343474746959723858477 54797753803030109896446929)
        ·
          refine ⟨41098315352272582422335197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54797753803030109896446929 41098315352272582422335197)
          ·
            refine ⟨15411868257102218408375699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41098315352272582422335197 15411868257102218408375699)
            ·
              refine ⟨23117802385653327612563549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15411868257102218408375699 23117802385653327612563549)
              ·
                refine ⟨8669175894619997854711331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23117802385653327612563549 8669175894619997854711331)
                ·
                  refine ⟨13003763841929996782066997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8669175894619997854711331 13003763841929996782066997)
                  ·
                    refine ⟨1219102860180937198318781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13003763841929996782066997 1219102860180937198318781)
                    ·
                      rfl

theorem cell23_7122583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_7122583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122583 prefixEnd_7122583 := by exact prefixLift 7122583
  have htrace : WordTrace (prefixWord ++ tailWord_7122583) baseStart_7122583 baseEnd_7122583 := by
    simpa [prefixWord, tailWord_7122583, baseEnd_7122583] using wordTrace_append hprefix tailTrace_7122583
  have hstable : (prefixWord ++ tailWord_7122583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122583).length < 2 ^ (prefixWord ++ tailWord_7122583).sum := by decide
  have hdescent : baseEnd_7122583 < baseStart_7122583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122620 : List Nat := [2, 2, 2, 3, 1, 3, 2, 2, 1, 1, 4]
def baseStart_7122620 : Nat := 118140960795 + 7122620 * 2 ^ 59
def prefixEnd_7122620 : Nat := 4983230072969 + 3 ^ 40 * 7122620 * 2
def baseEnd_7122620 : Nat := 3657327579327027950193673

theorem tailTrace_7122620 : CollatzResearch.WordTrace tailWord_7122620 prefixEnd_7122620 3657327579327027950193673 := by
  unfold tailWord_7122620
  simp only [CollatzResearch.WordTrace]
  refine ⟨129891646727985830747422657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173188862303981107663230209 129891646727985830747422657)
  ·
    refine ⟨97418735045989373060566993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129891646727985830747422657 97418735045989373060566993)
    ·
      refine ⟨73064051284492029795425245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97418735045989373060566993 73064051284492029795425245)
      ·
        refine ⟨27399019231684511173284467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73064051284492029795425245 27399019231684511173284467)
        ·
          refine ⟨41098528847526766759926701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27399019231684511173284467 41098528847526766759926701)
          ·
            refine ⟨15411948317822537534972513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41098528847526766759926701 15411948317822537534972513)
            ·
              refine ⟨11558961238366903151229385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15411948317822537534972513 11558961238366903151229385)
              ·
                refine ⟨8669220928775177363422039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11558961238366903151229385 8669220928775177363422039)
                ·
                  refine ⟨13003831393162766045133059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8669220928775177363422039 13003831393162766045133059)
                  ·
                    refine ⟨19505747089744149067699589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13003831393162766045133059 19505747089744149067699589)
                    ·
                      refine ⟨3657327579327027950193673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19505747089744149067699589 3657327579327027950193673)
                      ·
                        rfl

theorem cell23_7122620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_7122620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122620 prefixEnd_7122620 := by exact prefixLift 7122620
  have htrace : WordTrace (prefixWord ++ tailWord_7122620) baseStart_7122620 baseEnd_7122620 := by
    simpa [prefixWord, tailWord_7122620, baseEnd_7122620] using wordTrace_append hprefix tailTrace_7122620
  have hstable : (prefixWord ++ tailWord_7122620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122620).length < 2 ^ (prefixWord ++ tailWord_7122620).sum := by decide
  have hdescent : baseEnd_7122620 < baseStart_7122620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122637 : List Nat := [1, 6, 2, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_7122637 : Nat := 118140960795 + 7122637 * 2 ^ 59
def prefixEnd_7122637 : Nat := 4983230072969 + 3 ^ 40 * 7122637 * 2
def baseEnd_7122637 : Nat := 3657336308498154383681095

theorem tailTrace_7122637 : CollatzResearch.WordTrace tailWord_7122637 prefixEnd_7122637 3657336308498154383681095 := by
  unfold tailWord_7122637
  simp only [CollatzResearch.WordTrace]
  refine ⟨259783913496910073398214165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173189275664606715598809443 259783913496910073398214165)
  ·
    refine ⟨12177370945167659690541289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 259783913496910073398214165 12177370945167659690541289)
    ·
      refine ⟨9133028208875744767905967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12177370945167659690541289 9133028208875744767905967)
      ·
        refine ⟨13699542313313617151858951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9133028208875744767905967 13699542313313617151858951)
        ·
          refine ⟨20549313469970425727788427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13699542313313617151858951 20549313469970425727788427)
          ·
            refine ⟨30823970204955638591682641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20549313469970425727788427 30823970204955638591682641)
            ·
              refine ⟨23117977653716728943761981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30823970204955638591682641 23117977653716728943761981)
              ·
                refine ⟨8669241620143773353910743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23117977653716728943761981 8669241620143773353910743)
                ·
                  refine ⟨13003862430215660030866115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8669241620143773353910743 13003862430215660030866115)
                  ·
                    refine ⟨19505793645323490046299173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13003862430215660030866115 19505793645323490046299173)
                    ·
                      refine ⟨3657336308498154383681095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19505793645323490046299173 3657336308498154383681095)
                      ·
                        rfl

theorem cell23_7122637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_7122637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122637 prefixEnd_7122637 := by exact prefixLift 7122637
  have htrace : WordTrace (prefixWord ++ tailWord_7122637) baseStart_7122637 baseEnd_7122637 := by
    simpa [prefixWord, tailWord_7122637, baseEnd_7122637] using wordTrace_append hprefix tailTrace_7122637
  have hstable : (prefixWord ++ tailWord_7122637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122637).length < 2 ^ (prefixWord ++ tailWord_7122637).sum := by decide
  have hdescent : baseEnd_7122637 < baseStart_7122637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122680 : List Nat := [2, 1, 2, 1, 1, 2, 2, 6, 1, 3, 2]
def baseStart_7122680 : Nat := 118140960795 + 7122680 * 2 ^ 59
def prefixEnd_7122680 : Nat := 4983230072969 + 3 ^ 40 * 7122680 * 2
def baseEnd_7122680 : Nat := 3657358388166297715443397

theorem tailTrace_7122680 : CollatzResearch.WordTrace tailWord_7122680 prefixEnd_7122680 3657358388166297715443397 := by
  unfold tailWord_7122680
  simp only [CollatzResearch.WordTrace]
  refine ⟨129892740917877145871014747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173190321223836194494686329 129892740917877145871014747)
  ·
    refine ⟨194839111376815718806522121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129892740917877145871014747 194839111376815718806522121)
    ·
      refine ⟨146129333532611789104891591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194839111376815718806522121 146129333532611789104891591)
      ·
        refine ⟨219194000298917683657337387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146129333532611789104891591 219194000298917683657337387)
        ·
          refine ⟨328791000448376525486006081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219194000298917683657337387 328791000448376525486006081)
          ·
            refine ⟨246593250336282394114504561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328791000448376525486006081 246593250336282394114504561)
            ·
              refine ⟨184944937752211795585878421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246593250336282394114504561 184944937752211795585878421)
              ·
                refine ⟨8669293957134927918088051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 184944937752211795585878421 8669293957134927918088051)
                ·
                  refine ⟨13003940935702391877132077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8669293957134927918088051 13003940935702391877132077)
                  ·
                    refine ⟨4876477850888396953924529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13003940935702391877132077 4876477850888396953924529)
                    ·
                      refine ⟨3657358388166297715443397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4876477850888396953924529 3657358388166297715443397)
                      ·
                        rfl

theorem cell23_7122680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 1, 3, 2].length) (baseStart_7122680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122680 prefixEnd_7122680 := by exact prefixLift 7122680
  have htrace : WordTrace (prefixWord ++ tailWord_7122680) baseStart_7122680 baseEnd_7122680 := by
    simpa [prefixWord, tailWord_7122680, baseEnd_7122680] using wordTrace_append hprefix tailTrace_7122680
  have hstable : (prefixWord ++ tailWord_7122680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122680).length < 2 ^ (prefixWord ++ tailWord_7122680).sum := by decide
  have hdescent : baseEnd_7122680 < baseStart_7122680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122694 : List Nat := [6, 2, 2, 1, 1, 11]
def baseStart_7122694 : Nat := 118140960795 + 7122694 * 2 ^ 59
def prefixEnd_7122694 : Nat := 4983230072969 + 3 ^ 40 * 7122694 * 2
def baseEnd_7122694 : Nat := 15050887147717945105631

theorem tailTrace_7122694 : CollatzResearch.WordTrace tailWord_7122694 prefixEnd_7122694 15050887147717945105631 := by
  unfold tailWord_7122694
  simp only [CollatzResearch.WordTrace]
  refine ⟨8118312264303236629157473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 173190661638469048088692757 8118312264303236629157473)
  ·
    refine ⟨6088734198227427471868105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8118312264303236629157473 6088734198227427471868105)
    ·
      refine ⟨4566550648670570603901079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6088734198227427471868105 4566550648670570603901079)
      ·
        refine ⟨6849825973005855905851619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4566550648670570603901079 6849825973005855905851619)
        ·
          refine ⟨10274738959508783858777429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6849825973005855905851619 10274738959508783858777429)
          ·
            refine ⟨15050887147717945105631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10274738959508783858777429 15050887147717945105631)
            ·
              rfl

theorem cell23_7122694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 11].length) (baseStart_7122694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122694 prefixEnd_7122694 := by exact prefixLift 7122694
  have htrace : WordTrace (prefixWord ++ tailWord_7122694) baseStart_7122694 baseEnd_7122694 := by
    simpa [prefixWord, tailWord_7122694, baseEnd_7122694] using wordTrace_append hprefix tailTrace_7122694
  have hstable : (prefixWord ++ tailWord_7122694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122694).length < 2 ^ (prefixWord ++ tailWord_7122694).sum := by decide
  have hdescent : baseEnd_7122694 < baseStart_7122694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122783 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 4]
def baseStart_7122783 : Nat := 118140960795 + 7122783 * 2 ^ 59
def prefixEnd_7122783 : Nat := 4983230072969 + 3 ^ 40 * 7122783 * 2
def baseEnd_7122783 : Nat := 3657411276673710812455423

theorem tailTrace_7122783 : CollatzResearch.WordTrace tailWord_7122783 prefixEnd_7122783 3657411276673710812455423 := by
  unfold tailWord_7122783
  simp only [CollatzResearch.WordTrace]
  refine ⟨259789238554381140333029003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173192825702920760222019335 259789238554381140333029003)
  ·
    refine ⟨389683857831571710499543505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259789238554381140333029003 389683857831571710499543505)
    ·
      refine ⟨292262893373678782874657629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389683857831571710499543505 292262893373678782874657629)
      ·
        refine ⟨109598585015129543577996611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292262893373678782874657629 109598585015129543577996611)
        ·
          refine ⟨164397877522694315366994917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109598585015129543577996611 164397877522694315366994917)
          ·
            refine ⟨30824602035505184131311547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164397877522694315366994917 30824602035505184131311547)
            ·
              refine ⟨46236903053257776196967321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30824602035505184131311547 46236903053257776196967321)
              ·
                refine ⟨34677677289943332147725491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46236903053257776196967321 34677677289943332147725491)
                ·
                  refine ⟨52016515934914998221588237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34677677289943332147725491 52016515934914998221588237)
                  ·
                    refine ⟨19506193475593124333095589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52016515934914998221588237 19506193475593124333095589)
                    ·
                      refine ⟨3657411276673710812455423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19506193475593124333095589 3657411276673710812455423)
                      ·
                        rfl

theorem cell23_7122783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_7122783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122783 prefixEnd_7122783 := by exact prefixLift 7122783
  have htrace : WordTrace (prefixWord ++ tailWord_7122783) baseStart_7122783 baseEnd_7122783 := by
    simpa [prefixWord, tailWord_7122783, baseEnd_7122783] using wordTrace_append hprefix tailTrace_7122783
  have hstable : (prefixWord ++ tailWord_7122783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122783).length < 2 ^ (prefixWord ++ tailWord_7122783).sum := by decide
  have hdescent : baseEnd_7122783 < baseStart_7122783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122820 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_7122820 : Nat := 118140960795 + 7122820 * 2 ^ 59
def prefixEnd_7122820 : Nat := 4983230072969 + 3 ^ 40 * 7122820 * 2
def baseEnd_7122820 : Nat := 3657430275457927167692753

theorem tailTrace_7122820 : CollatzResearch.WordTrace tailWord_7122820 prefixEnd_7122820 3657430275457927167692753 := by
  unfold tailWord_7122820
  simp only [CollatzResearch.WordTrace]
  refine ⟨129895294027623547826062957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173193725370164730434750609 129895294027623547826062957)
  ·
    refine ⟨48710735260358830434773609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129895294027623547826062957 48710735260358830434773609)
    ·
      refine ⟨36533051445269122826080207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48710735260358830434773609 36533051445269122826080207)
      ·
        refine ⟨54799577167903684239120311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36533051445269122826080207 54799577167903684239120311)
        ·
          refine ⟨82199365751855526358680467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54799577167903684239120311 82199365751855526358680467)
          ·
            refine ⟨123299048627783289538020701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82199365751855526358680467 123299048627783289538020701)
            ·
              refine ⟨46237143235418733576757763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123299048627783289538020701 46237143235418733576757763)
              ·
                refine ⟨69355714853128100365136645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46237143235418733576757763 69355714853128100365136645)
                ·
                  refine ⟨13004196534961518818463121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69355714853128100365136645 13004196534961518818463121)
                  ·
                    refine ⟨9753147401221139113847341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13004196534961518818463121 9753147401221139113847341)
                    ·
                      refine ⟨3657430275457927167692753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9753147401221139113847341 3657430275457927167692753)
                      ·
                        rfl

theorem cell23_7122820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_7122820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122820 prefixEnd_7122820 := by exact prefixLift 7122820
  have htrace : WordTrace (prefixWord ++ tailWord_7122820) baseStart_7122820 baseEnd_7122820 := by
    simpa [prefixWord, tailWord_7122820, baseEnd_7122820] using wordTrace_append hprefix tailTrace_7122820
  have hstable : (prefixWord ++ tailWord_7122820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122820).length < 2 ^ (prefixWord ++ tailWord_7122820).sum := by decide
  have hdescent : baseEnd_7122820 < baseStart_7122820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122890 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_7122890 : Nat := 118140960795 + 7122890 * 2 ^ 59
def prefixEnd_7122890 : Nat := 4983230072969 + 3 ^ 40 * 7122890 * 2
def baseEnd_7122890 : Nat := 3657466219103741893817431

theorem tailTrace_7122890 : CollatzResearch.WordTrace tailWord_7122890 prefixEnd_7122890 3657466219103741893817431 := by
  unfold tailWord_7122890
  simp only [CollatzResearch.WordTrace]
  refine ⟨64948285291248374401793531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173195427443328998404782749 64948285291248374401793531)
  ·
    refine ⟨97422427936872561602690297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64948285291248374401793531 97422427936872561602690297)
    ·
      refine ⟨73066820952654421202017723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97422427936872561602690297 73066820952654421202017723)
      ·
        refine ⟨109600231428981631803026585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73066820952654421202017723 109600231428981631803026585)
        ·
          refine ⟨82200173571736223852269939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109600231428981631803026585 82200173571736223852269939)
          ·
            refine ⟨123300260357604335778404909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82200173571736223852269939 123300260357604335778404909)
            ·
              refine ⟨46237597634101625916901841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123300260357604335778404909 46237597634101625916901841)
              ·
                refine ⟨34678198225576219437676381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46237597634101625916901841 34678198225576219437676381)
                ·
                  refine ⟨13004324334591082289128643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34678198225576219437676381 13004324334591082289128643)
                  ·
                    refine ⟨19506486501886623433692965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13004324334591082289128643 19506486501886623433692965)
                    ·
                      refine ⟨3657466219103741893817431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19506486501886623433692965 3657466219103741893817431)
                      ·
                        rfl

theorem cell23_7122890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_7122890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122890 prefixEnd_7122890 := by exact prefixLift 7122890
  have htrace : WordTrace (prefixWord ++ tailWord_7122890) baseStart_7122890 baseEnd_7122890 := by
    simpa [prefixWord, tailWord_7122890, baseEnd_7122890] using wordTrace_append hprefix tailTrace_7122890
  have hstable : (prefixWord ++ tailWord_7122890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122890).length < 2 ^ (prefixWord ++ tailWord_7122890).sum := by decide
  have hdescent : baseEnd_7122890 < baseStart_7122890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122913 : List Nat := [1, 2, 3, 1, 2, 1, 2, 11]
def baseStart_7122913 : Nat := 118140960795 + 7122913 * 2 ^ 59
def prefixEnd_7122913 : Nat := 4983230072969 + 3 ^ 40 * 7122913 * 2
def baseEnd_7122913 : Nat := 135462149228103529771475

theorem tailTrace_7122913 : CollatzResearch.WordTrace tailWord_7122913 prefixEnd_7122913 135462149228103529771475 := by
  unfold tailWord_7122913
  simp only [CollatzResearch.WordTrace]
  refine ⟨259793980043910172535261393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173195986695940115023507595 259793980043910172535261393)
  ·
    refine ⟨194845485032932629401446045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259793980043910172535261393 194845485032932629401446045)
    ·
      refine ⟨73067056887349736025542267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194845485032932629401446045 73067056887349736025542267)
      ·
        refine ⟨109600585331024604038313401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73067056887349736025542267 109600585331024604038313401)
        ·
          refine ⟨82200438998268453028735051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109600585331024604038313401 82200438998268453028735051)
          ·
            refine ⟨123300658497402679543102577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82200438998268453028735051 123300658497402679543102577)
            ·
              refine ⟨92475493873052009657326933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123300658497402679543102577 92475493873052009657326933)
              ·
                refine ⟨135462149228103529771475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 92475493873052009657326933 135462149228103529771475)
                ·
                  rfl

theorem cell23_7122913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 11].length) (baseStart_7122913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122913 prefixEnd_7122913 := by exact prefixLift 7122913
  have htrace : WordTrace (prefixWord ++ tailWord_7122913) baseStart_7122913 baseEnd_7122913 := by
    simpa [prefixWord, tailWord_7122913, baseEnd_7122913] using wordTrace_append hprefix tailTrace_7122913
  have hstable : (prefixWord ++ tailWord_7122913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122913).length < 2 ^ (prefixWord ++ tailWord_7122913).sum := by decide
  have hdescent : baseEnd_7122913 < baseStart_7122913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122927 : List Nat := [1, 1, 2, 1, 4, 2, 3, 3, 1, 2, 3]
def baseStart_7122927 : Nat := 118140960795 + 7122927 * 2 ^ 59
def prefixEnd_7122927 : Nat := 4983230072969 + 3 ^ 40 * 7122927 * 2
def baseEnd_7122927 : Nat := 3657485217887958249054761

theorem tailTrace_7122927 : CollatzResearch.WordTrace tailWord_7122927 prefixEnd_7122927 3657485217887958249054761 := by
  unfold tailWord_7122927
  simp only [CollatzResearch.WordTrace]
  refine ⟨259794490665859452926271035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173196327110572968617514023 259794490665859452926271035)
  ·
    refine ⟨389691735998789179389406553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259794490665859452926271035 389691735998789179389406553)
    ·
      refine ⟨292268801999091884542054915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389691735998789179389406553 292268801999091884542054915)
      ·
        refine ⟨438403202998637826813082373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292268801999091884542054915 438403202998637826813082373)
        ·
          refine ⟨82200600562244592527452945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 438403202998637826813082373 82200600562244592527452945)
          ·
            refine ⟨61650450421683444395589709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82200600562244592527452945 61650450421683444395589709)
            ·
              refine ⟨23118918908131291648346141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61650450421683444395589709 23118918908131291648346141)
              ·
                refine ⟨8669594590549234368129803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23118918908131291648346141 8669594590549234368129803)
                ·
                  refine ⟨13004391885823851552194705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8669594590549234368129803 13004391885823851552194705)
                  ·
                    refine ⟨9753293914367888664146029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13004391885823851552194705 9753293914367888664146029)
                    ·
                      refine ⟨3657485217887958249054761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9753293914367888664146029 3657485217887958249054761)
                      ·
                        rfl

theorem cell23_7122927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 2, 3].length) (baseStart_7122927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122927 prefixEnd_7122927 := by exact prefixLift 7122927
  have htrace : WordTrace (prefixWord ++ tailWord_7122927) baseStart_7122927 baseEnd_7122927 := by
    simpa [prefixWord, tailWord_7122927, baseEnd_7122927] using wordTrace_append hprefix tailTrace_7122927
  have hstable : (prefixWord ++ tailWord_7122927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122927).length < 2 ^ (prefixWord ++ tailWord_7122927).sum := by decide
  have hdescent : baseEnd_7122927 < baseStart_7122927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122934 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_7122934 : Nat := 118140960795 + 7122934 * 2 ^ 59
def prefixEnd_7122934 : Nat := 4983230072969 + 3 ^ 40 * 7122934 * 2
def baseEnd_7122934 : Nat := 1219162937417513240555743

theorem tailTrace_7122934 : CollatzResearch.WordTrace tailWord_7122934 prefixEnd_7122934 1219162937417513240555743 := by
  unfold tailWord_7122934
  simp only [CollatzResearch.WordTrace]
  refine ⟨16237171623552130820110991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173196497317889395414517237 16237171623552130820110991)
  ·
    refine ⟨24355757435328196230166487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16237171623552130820110991 24355757435328196230166487)
    ·
      refine ⟨36533636152992294345249731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24355757435328196230166487 36533636152992294345249731)
      ·
        refine ⟨54800454229488441517874597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36533636152992294345249731 54800454229488441517874597)
        ·
          refine ⟨10275085168029082784601487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54800454229488441517874597 10275085168029082784601487)
          ·
            refine ⟨15412627752043624176902231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10275085168029082784601487 15412627752043624176902231)
            ·
              refine ⟨23118941628065436265353347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15412627752043624176902231 23118941628065436265353347)
              ·
                refine ⟨34678412442098154398030021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23118941628065436265353347 34678412442098154398030021)
                ·
                  refine ⟨6502202332893403949630629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34678412442098154398030021 6502202332893403949630629)
                  ·
                    refine ⟨1219162937417513240555743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6502202332893403949630629 1219162937417513240555743)
                    ·
                      rfl

theorem cell23_7122934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_7122934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122934 prefixEnd_7122934 := by exact prefixLift 7122934
  have htrace : WordTrace (prefixWord ++ tailWord_7122934) baseStart_7122934 baseEnd_7122934 := by
    simpa [prefixWord, tailWord_7122934, baseEnd_7122934] using wordTrace_append hprefix tailTrace_7122934
  have hstable : (prefixWord ++ tailWord_7122934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122934).length < 2 ^ (prefixWord ++ tailWord_7122934).sum := by decide
  have hdescent : baseEnd_7122934 < baseStart_7122934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122941 : List Nat := [1, 4, 1, 1, 1, 2, 4, 4, 1, 2, 2]
def baseStart_7122941 : Nat := 118140960795 + 7122941 * 2 ^ 59
def prefixEnd_7122941 : Nat := 4983230072969 + 3 ^ 40 * 7122941 * 2
def baseEnd_7122941 : Nat := 3657492406617121194279697

theorem tailTrace_7122941 : CollatzResearch.WordTrace tailWord_7122941 prefixEnd_7122941 3657492406617121194279697 := by
  unfold tailWord_7122941
  simp only [CollatzResearch.WordTrace]
  refine ⟨259795001287808733317280677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173196667525205822211520451 259795001287808733317280677)
  ·
    refine ⟨48711562741464137496990127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259795001287808733317280677 48711562741464137496990127)
    ·
      refine ⟨73067344112196206245485191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48711562741464137496990127 73067344112196206245485191)
      ·
        refine ⟨109601016168294309368227787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73067344112196206245485191 109601016168294309368227787)
        ·
          refine ⟨164401524252441464052341681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109601016168294309368227787 164401524252441464052341681)
          ·
            refine ⟨123301143189331098039256261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164401524252441464052341681 123301143189331098039256261)
            ·
              refine ⟨23118964347999580882360549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123301143189331098039256261 23118964347999580882360549)
              ·
                refine ⟨4334805815249921415442603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23118964347999580882360549 4334805815249921415442603)
                ·
                  refine ⟨6502208722874882123163905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4334805815249921415442603 6502208722874882123163905)
                  ·
                    refine ⟨4876656542156161592372929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6502208722874882123163905 4876656542156161592372929)
                    ·
                      refine ⟨3657492406617121194279697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4876656542156161592372929 3657492406617121194279697)
                      ·
                        rfl

theorem cell23_7122941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 1, 2, 2].length) (baseStart_7122941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122941 prefixEnd_7122941 := by exact prefixLift 7122941
  have htrace : WordTrace (prefixWord ++ tailWord_7122941) baseStart_7122941 baseEnd_7122941 := by
    simpa [prefixWord, tailWord_7122941, baseEnd_7122941] using wordTrace_append hprefix tailTrace_7122941
  have hstable : (prefixWord ++ tailWord_7122941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122941).length < 2 ^ (prefixWord ++ tailWord_7122941).sum := by decide
  have hdescent : baseEnd_7122941 < baseStart_7122941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122943 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 1, 9]
def baseStart_7122943 : Nat := 118140960795 + 7122943 * 2 ^ 59
def prefixEnd_7122943 : Nat := 4983230072969 + 3 ^ 40 * 7122943 * 2
def baseEnd_7122943 : Nat := 1219164477859476728818229

theorem tailTrace_7122943 : CollatzResearch.WordTrace tailWord_7122943 prefixEnd_7122943 1219164477859476728818229 := by
  unfold tailWord_7122943
  simp only [CollatzResearch.WordTrace]
  refine ⟨259795074233801487658853483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173196716155867658439235655 259795074233801487658853483)
  ·
    refine ⟨389692611350702231488280225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259795074233801487658853483 389692611350702231488280225)
    ·
      refine ⟨292269458513026673616210169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389692611350702231488280225 292269458513026673616210169)
      ·
        refine ⟨219202093884770005212157627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292269458513026673616210169 219202093884770005212157627)
        ·
          refine ⟨328803140827155007818236441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219202093884770005212157627 328803140827155007818236441)
          ·
            refine ⟨246602355620366255863677331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328803140827155007818236441 246602355620366255863677331)
            ·
              refine ⟨369903533430549383795515997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246602355620366255863677331 369903533430549383795515997)
              ·
                refine ⟨138713825036456018923318499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369903533430549383795515997 138713825036456018923318499)
                ·
                  refine ⟨208070737554684028384977749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138713825036456018923318499 208070737554684028384977749)
                  ·
                    refine ⟨1219164477859476728818229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 208070737554684028384977749 1219164477859476728818229)
                    ·
                      rfl

theorem cell23_7122943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 9].length) (baseStart_7122943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122943 prefixEnd_7122943 := by exact prefixLift 7122943
  have htrace : WordTrace (prefixWord ++ tailWord_7122943) baseStart_7122943 baseEnd_7122943 := by
    simpa [prefixWord, tailWord_7122943, baseEnd_7122943] using wordTrace_append hprefix tailTrace_7122943
  have hstable : (prefixWord ++ tailWord_7122943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122943).length < 2 ^ (prefixWord ++ tailWord_7122943).sum := by decide
  have hdescent : baseEnd_7122943 < baseStart_7122943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122954 : List Nat := [3, 1, 2, 2, 4, 2, 1, 1, 1, 2, 4]
def baseStart_7122954 : Nat := 118140960795 + 7122954 * 2 ^ 59
def prefixEnd_7122954 : Nat := 4983230072969 + 3 ^ 40 * 7122954 * 2
def baseEnd_7122954 : Nat := 3657499081865629643417137

theorem tailTrace_7122954 : CollatzResearch.WordTrace tailWord_7122954 prefixEnd_7122954 3657499081865629643417137 := by
  unfold tailWord_7122954
  simp only [CollatzResearch.WordTrace]
  refine ⟨64948868859190409134375979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173196983624507757691669277 64948868859190409134375979)
  ·
    refine ⟨97423303288785613701563969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64948868859190409134375979 97423303288785613701563969)
    ·
      refine ⟨73067477466589210276172977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97423303288785613701563969 73067477466589210276172977)
      ·
        refine ⟨54800608099941907707129733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73067477466589210276172977 54800608099941907707129733)
        ·
          refine ⟨10275114018739107695086825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54800608099941907707129733 10275114018739107695086825)
          ·
            refine ⟨7706335514054330771315119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10275114018739107695086825 7706335514054330771315119)
            ·
              refine ⟨11559503271081496156972679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7706335514054330771315119 11559503271081496156972679)
              ·
                refine ⟨17339254906622244235459019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11559503271081496156972679 17339254906622244235459019)
                ·
                  refine ⟨26008882359933366353188529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17339254906622244235459019 26008882359933366353188529)
                  ·
                    refine ⟨19506661769950024764891397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26008882359933366353188529 19506661769950024764891397)
                    ·
                      refine ⟨3657499081865629643417137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19506661769950024764891397 3657499081865629643417137)
                      ·
                        rfl

theorem cell23_7122954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_7122954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122954 prefixEnd_7122954 := by exact prefixLift 7122954
  have htrace : WordTrace (prefixWord ++ tailWord_7122954) baseStart_7122954 baseEnd_7122954 := by
    simpa [prefixWord, tailWord_7122954, baseEnd_7122954] using wordTrace_append hprefix tailTrace_7122954
  have hstable : (prefixWord ++ tailWord_7122954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122954).length < 2 ^ (prefixWord ++ tailWord_7122954).sum := by decide
  have hdescent : baseEnd_7122954 < baseStart_7122954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122964 : List Nat := [2, 4, 3, 2, 1, 1, 1, 9]
def baseStart_7122964 : Nat := 118140960795 + 7122964 * 2 ^ 59
def prefixEnd_7122964 : Nat := 4983230072969 + 3 ^ 40 * 7122964 * 2
def baseEnd_7122964 : Nat := 135463119136006466825633

theorem tailTrace_7122964 : CollatzResearch.WordTrace tailWord_7122964 prefixEnd_7122964 135463119136006466825633 := by
  unfold tailWord_7122964
  simp only [CollatzResearch.WordTrace]
  refine ⟨129897920083362704122683973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173197226777816938830245297 129897920083362704122683973)
  ·
    refine ⟨24355860015630507023003245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129897920083362704122683973 24355860015630507023003245)
    ·
      refine ⟨9133447505861440133626217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24355860015630507023003245 9133447505861440133626217)
      ·
        refine ⟨6850085629396080100219663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9133447505861440133626217 6850085629396080100219663)
        ·
          refine ⟨10275128444094120150329495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6850085629396080100219663 10275128444094120150329495)
          ·
            refine ⟨15412692666141180225494243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10275128444094120150329495 15412692666141180225494243)
            ·
              refine ⟨23119038999211770338241365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15412692666141180225494243 23119038999211770338241365)
              ·
                refine ⟨135463119136006466825633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23119038999211770338241365 135463119136006466825633)
                ·
                  rfl

theorem cell23_7122964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 9].length) (baseStart_7122964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122964 prefixEnd_7122964 := by exact prefixLift 7122964
  have htrace : WordTrace (prefixWord ++ tailWord_7122964) baseStart_7122964 baseEnd_7122964 := by
    simpa [prefixWord, tailWord_7122964, baseEnd_7122964] using wordTrace_append hprefix tailTrace_7122964
  have hstable : (prefixWord ++ tailWord_7122964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122964).length < 2 ^ (prefixWord ++ tailWord_7122964).sum := by decide
  have hdescent : baseEnd_7122964 < baseStart_7122964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7122970 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5]
def baseStart_7122970 : Nat := 118140960795 + 7122970 * 2 ^ 59
def prefixEnd_7122970 : Nat := 4983230072969 + 3 ^ 40 * 7122970 * 2
def baseEnd_7122970 : Nat := 3657507297556101580817063

theorem tailTrace_7122970 : CollatzResearch.WordTrace tailWord_7122970 prefixEnd_7122970 3657507297556101580817063 := by
  unfold tailWord_7122970
  simp only [CollatzResearch.WordTrace]
  refine ⟨64949014751175917817521591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173197372669802447513390909 64949014751175917817521591)
  ·
    refine ⟨97423522126763876726282387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64949014751175917817521591 97423522126763876726282387)
    ·
      refine ⟨146135283190145815089423581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97423522126763876726282387 146135283190145815089423581)
      ·
        refine ⟨54800731196304680658533843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146135283190145815089423581 54800731196304680658533843)
        ·
          refine ⟨82201096794457020987800765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54800731196304680658533843 82201096794457020987800765)
          ·
            refine ⟨30825411297921382870425287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82201096794457020987800765 30825411297921382870425287)
            ·
              refine ⟨46238116946882074305637931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30825411297921382870425287 46238116946882074305637931)
              ·
                refine ⟨69357175420323111458456897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46238116946882074305637931 69357175420323111458456897)
                ·
                  refine ⟨52017881565242333593842673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69357175420323111458456897 52017881565242333593842673)
                  ·
                    refine ⟨39013411173931750195382005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52017881565242333593842673 39013411173931750195382005)
                    ·
                      refine ⟨3657507297556101580817063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39013411173931750195382005 3657507297556101580817063)
                      ·
                        rfl

theorem cell23_7122970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_7122970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7122970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7122970 prefixEnd_7122970 := by exact prefixLift 7122970
  have htrace : WordTrace (prefixWord ++ tailWord_7122970) baseStart_7122970 baseEnd_7122970 := by
    simpa [prefixWord, tailWord_7122970, baseEnd_7122970] using wordTrace_append hprefix tailTrace_7122970
  have hstable : (prefixWord ++ tailWord_7122970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7122970).length < 2 ^ (prefixWord ++ tailWord_7122970).sum := by decide
  have hdescent : baseEnd_7122970 < baseStart_7122970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7122970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123020 : List Nat := [2, 2, 1, 3, 1, 1, 2, 4, 7]
def baseStart_7123020 : Nat := 118140960795 + 7123020 * 2 ^ 59
def prefixEnd_7123020 : Nat := 4983230072969 + 3 ^ 40 * 7123020 * 2
def baseEnd_7123020 : Nat := 406392552398758487243537

theorem tailTrace_7123020 : CollatzResearch.WordTrace tailWord_7123020 prefixEnd_7123020 406392552398758487243537 := by
  unfold tailWord_7123020
  simp only [CollatzResearch.WordTrace]
  refine ⟨129898941327261264904703257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173198588436348353206271009 129898941327261264904703257)
  ·
    refine ⟨97424205995445948678527443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129898941327261264904703257 97424205995445948678527443)
    ·
      refine ⟨146136308993168923017791165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97424205995445948678527443 146136308993168923017791165)
      ·
        refine ⟨54801115872438346131671687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146136308993168923017791165 54801115872438346131671687)
        ·
          refine ⟨82201673808657519197507531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54801115872438346131671687 82201673808657519197507531)
          ·
            refine ⟨123302510712986278796261297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82201673808657519197507531 123302510712986278796261297)
            ·
              refine ⟨92476883034739709097195973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123302510712986278796261297 92476883034739709097195973)
              ·
                refine ⟨17339415569013695455724245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92476883034739709097195973 17339415569013695455724245)
                ·
                  refine ⟨406392552398758487243537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17339415569013695455724245 406392552398758487243537)
                  ·
                    rfl

theorem cell23_7123020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 7].length) (baseStart_7123020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123020 prefixEnd_7123020 := by exact prefixLift 7123020
  have htrace : WordTrace (prefixWord ++ tailWord_7123020) baseStart_7123020 baseEnd_7123020 := by
    simpa [prefixWord, tailWord_7123020, baseEnd_7123020] using wordTrace_append hprefix tailTrace_7123020
  have hstable : (prefixWord ++ tailWord_7123020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123020).length < 2 ^ (prefixWord ++ tailWord_7123020).sum := by decide
  have hdescent : baseEnd_7123020 < baseStart_7123020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123047 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_7123047 : Nat := 118140960795 + 7123047 * 2 ^ 59
def prefixEnd_7123047 : Nat := 4983230072969 + 3 ^ 40 * 7123047 * 2
def baseEnd_7123047 : Nat := 3657546835566497779554209

theorem tailTrace_7123047 : CollatzResearch.WordTrace tailWord_7123047 prefixEnd_7123047 3657546835566497779554209 := by
  unfold tailWord_7123047
  simp only [CollatzResearch.WordTrace]
  refine ⟨259798867425424713420639395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173199244950283142280426263 259798867425424713420639395)
  ·
    refine ⟨389698301138137070130959093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259798867425424713420639395 389698301138137070130959093)
    ·
      refine ⟨36534215731700350324777415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 389698301138137070130959093 36534215731700350324777415)
      ·
        refine ⟨54801323597550525487166123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36534215731700350324777415 54801323597550525487166123)
        ·
          refine ⟨82201985396325788230749185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54801323597550525487166123 82201985396325788230749185)
          ·
            refine ⟨61651489047244341173061889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82201985396325788230749185 61651489047244341173061889)
            ·
              refine ⟨46238616785433255879796417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61651489047244341173061889 46238616785433255879796417)
              ·
                refine ⟨34678962589074941909847313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46238616785433255879796417 34678962589074941909847313)
                ·
                  refine ⟨26009221941806206432385485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34678962589074941909847313 26009221941806206432385485)
                  ·
                    refine ⟨9753458228177327412144557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26009221941806206432385485 9753458228177327412144557)
                    ·
                      refine ⟨3657546835566497779554209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9753458228177327412144557 3657546835566497779554209)
                      ·
                        rfl

theorem cell23_7123047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_7123047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123047 prefixEnd_7123047 := by exact prefixLift 7123047
  have htrace : WordTrace (prefixWord ++ tailWord_7123047) baseStart_7123047 baseEnd_7123047 := by
    simpa [prefixWord, tailWord_7123047, baseEnd_7123047] using wordTrace_append hprefix tailTrace_7123047
  have hstable : (prefixWord ++ tailWord_7123047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123047).length < 2 ^ (prefixWord ++ tailWord_7123047).sum := by decide
  have hdescent : baseEnd_7123047 < baseStart_7123047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123054 : List Nat := [4, 1, 2, 2, 1, 1, 3, 4, 5]
def baseStart_7123054 : Nat := 118140960795 + 7123054 * 2 ^ 59
def prefixEnd_7123054 : Nat := 4983230072969 + 3 ^ 40 * 7123054 * 2
def baseEnd_7123054 : Nat := 406394492214564361351853

theorem tailTrace_7123054 : CollatzResearch.WordTrace tailWord_7123054 prefixEnd_7123054 406394492214564361351853 := by
  unfold tailWord_7123054
  simp only [CollatzResearch.WordTrace]
  refine ⟨32474890342049919202018027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173199415157599569077429477 32474890342049919202018027)
  ·
    refine ⟨48712335513074878803027041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32474890342049919202018027 48712335513074878803027041)
    ·
      refine ⟨36534251634806159102270281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48712335513074878803027041 36534251634806159102270281)
      ·
        refine ⟨27400688726104619326702711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36534251634806159102270281 27400688726104619326702711)
        ·
          refine ⟨41101033089156928990054067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27400688726104619326702711 41101033089156928990054067)
          ·
            refine ⟨61651549633735393485081101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41101033089156928990054067 61651549633735393485081101)
            ·
              refine ⟨23119331112650772556905413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61651549633735393485081101 23119331112650772556905413)
              ·
                refine ⟨4334874583622019854419765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23119331112650772556905413 4334874583622019854419765)
                ·
                  refine ⟨406394492214564361351853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4334874583622019854419765 406394492214564361351853)
                  ·
                    rfl

theorem cell23_7123054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_7123054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123054 prefixEnd_7123054 := by exact prefixLift 7123054
  have htrace : WordTrace (prefixWord ++ tailWord_7123054) baseStart_7123054 baseEnd_7123054 := by
    simpa [prefixWord, tailWord_7123054, baseEnd_7123054] using wordTrace_append hprefix tailTrace_7123054
  have hstable : (prefixWord ++ tailWord_7123054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123054).length < 2 ^ (prefixWord ++ tailWord_7123054).sum := by decide
  have hdescent : baseEnd_7123054 < baseStart_7123054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123057 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 1, 7, 2]
def baseStart_7123057 : Nat := 118140960795 + 7123057 * 2 ^ 59
def prefixEnd_7123057 : Nat := 4983230072969 + 3 ^ 40 * 7123057 * 2
def baseEnd_7123057 : Nat := 3657551970373042740429163

theorem tailTrace_7123057 : CollatzResearch.WordTrace tailWord_7123057 prefixEnd_7123057 3657551970373042740429163 := by
  unfold tailWord_7123057
  simp only [CollatzResearch.WordTrace]
  refine ⟨259799232155388485128503425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173199488103592323419002283 259799232155388485128503425)
  ·
    refine ⟨194849424116541363846377569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259799232155388485128503425 194849424116541363846377569)
    ·
      refine ⟨146137068087406022884783177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194849424116541363846377569 146137068087406022884783177)
      ·
        refine ⟨109602801065554517163587383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146137068087406022884783177 109602801065554517163587383)
        ·
          refine ⟨164404201598331775745381075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109602801065554517163587383 164404201598331775745381075)
          ·
            refine ⟨246606302397497663618071613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164404201598331775745381075 246606302397497663618071613)
            ·
              refine ⟨92477363399061623856776855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246606302397497663618071613 92477363399061623856776855)
              ·
                refine ⟨138716045098592435785165283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92477363399061623856776855 138716045098592435785165283)
                ·
                  refine ⟨208074067647888653677747925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138716045098592435785165283 208074067647888653677747925)
                  ·
                    refine ⟨4876735960497390320572217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 208074067647888653677747925 4876735960497390320572217)
                    ·
                      refine ⟨3657551970373042740429163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4876735960497390320572217 3657551970373042740429163)
                      ·
                        rfl

theorem cell23_7123057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_7123057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123057 prefixEnd_7123057 := by exact prefixLift 7123057
  have htrace : WordTrace (prefixWord ++ tailWord_7123057) baseStart_7123057 baseEnd_7123057 := by
    simpa [prefixWord, tailWord_7123057, baseEnd_7123057] using wordTrace_append hprefix tailTrace_7123057
  have hstable : (prefixWord ++ tailWord_7123057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123057).length < 2 ^ (prefixWord ++ tailWord_7123057).sum := by decide
  have hdescent : baseEnd_7123057 < baseStart_7123057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123104 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 2, 4, 2]
def baseStart_7123104 : Nat := 118140960795 + 7123104 * 2 ^ 59
def prefixEnd_7123104 : Nat := 4983230072969 + 3 ^ 40 * 7123104 * 2
def baseEnd_7123104 : Nat := 3657576103963804056541447

theorem tailTrace_7123104 : CollatzResearch.WordTrace tailWord_7123104 prefixEnd_7123104 3657576103963804056541447 := by
  unfold tailWord_7123104
  simp only [CollatzResearch.WordTrace]
  refine ⟨129900473193109106077732183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173200630924145474770309577 129900473193109106077732183)
  ·
    refine ⟨194850709789663659116598275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129900473193109106077732183 194850709789663659116598275)
    ·
      refine ⟨292276064684495488674897413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194850709789663659116598275 292276064684495488674897413)
      ·
        refine ⟨54801762128342904126543265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292276064684495488674897413 54801762128342904126543265)
        ·
          refine ⟨41101321596257178094907449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54801762128342904126543265 41101321596257178094907449)
          ·
            refine ⟨30825991197192883571180587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41101321596257178094907449 30825991197192883571180587)
            ·
              refine ⟨46238986795789325356770881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30825991197192883571180587 46238986795789325356770881)
              ·
                refine ⟨34679240096841994017578161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46238986795789325356770881 34679240096841994017578161)
                ·
                  refine ⟨26009430072631495513183621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34679240096841994017578161 26009430072631495513183621)
                  ·
                    refine ⟨4876768138618405408721929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26009430072631495513183621 4876768138618405408721929)
                    ·
                      refine ⟨3657576103963804056541447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4876768138618405408721929 3657576103963804056541447)
                      ·
                        rfl

theorem cell23_7123104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_7123104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123104 prefixEnd_7123104 := by exact prefixLift 7123104
  have htrace : WordTrace (prefixWord ++ tailWord_7123104) baseStart_7123104 baseEnd_7123104 := by
    simpa [prefixWord, tailWord_7123104, baseEnd_7123104] using wordTrace_append hprefix tailTrace_7123104
  have hstable : (prefixWord ++ tailWord_7123104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123104).length < 2 ^ (prefixWord ++ tailWord_7123104).sum := by decide
  have hdescent : baseEnd_7123104 < baseStart_7123104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123158 : List Nat := [5, 2, 1, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_7123158 : Nat := 118140960795 + 7123158 * 2 ^ 59
def prefixEnd_7123158 : Nat := 4983230072969 + 3 ^ 40 * 7123158 * 2
def baseEnd_7123158 : Nat := 3657603831919146845266199

theorem tailTrace_7123158 : CollatzResearch.WordTrace tailWord_7123158 prefixEnd_7123158 3657603831919146845266199 := by
  unfold tailWord_7123158
  simp only [CollatzResearch.WordTrace]
  refine ⟨16237682245501411211120633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173201943952015052918620085 16237682245501411211120633)
  ·
    refine ⟨12178261684126058408340475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16237682245501411211120633 12178261684126058408340475)
    ·
      refine ⟨18267392526189087612510713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12178261684126058408340475 18267392526189087612510713)
      ·
        refine ⟨13700544394641815709383035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18267392526189087612510713 13700544394641815709383035)
        ·
          refine ⟨20550816591962723564074553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13700544394641815709383035 20550816591962723564074553)
          ·
            refine ⟨15413112443972042673055915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20550816591962723564074553 15413112443972042673055915)
            ·
              refine ⟨23119668665958064009583873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15413112443972042673055915 23119668665958064009583873)
              ·
                refine ⟨17339751499468548007187905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23119668665958064009583873 17339751499468548007187905)
                ·
                  refine ⟨13004813624601411005390929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17339751499468548007187905 13004813624601411005390929)
                  ·
                    refine ⟨9753610218451058254043197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13004813624601411005390929 9753610218451058254043197)
                    ·
                      refine ⟨3657603831919146845266199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9753610218451058254043197 3657603831919146845266199)
                      ·
                        rfl

theorem cell23_7123158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_7123158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123158 prefixEnd_7123158 := by exact prefixLift 7123158
  have htrace : WordTrace (prefixWord ++ tailWord_7123158) baseStart_7123158 baseEnd_7123158 := by
    simpa [prefixWord, tailWord_7123158, baseEnd_7123158] using wordTrace_append hprefix tailTrace_7123158
  have hstable : (prefixWord ++ tailWord_7123158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123158).length < 2 ^ (prefixWord ++ tailWord_7123158).sum := by decide
  have hdescent : baseEnd_7123158 < baseStart_7123158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123165 : List Nat := [1, 4, 3, 2, 1, 2, 3, 2, 1, 4]
def baseStart_7123165 : Nat := 118140960795 + 7123165 * 2 ^ 59
def prefixEnd_7123165 : Nat := 4983230072969 + 3 ^ 40 * 7123165 * 2
def baseEnd_7123165 : Nat := 1219202475427909439292889

theorem tailTrace_7123165 : CollatzResearch.WordTrace tailWord_7123165 prefixEnd_7123165 1219202475427909439292889 := by
  unfold tailWord_7123165
  simp only [CollatzResearch.WordTrace]
  refine ⟨259803171238997219573434949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173202114159331479715623299 259803171238997219573434949)
  ·
    refine ⟨48713094607311978670019053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259803171238997219573434949 48713094607311978670019053)
    ·
      refine ⟨18267410477741992001257145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48713094607311978670019053 18267410477741992001257145)
      ·
        refine ⟨13700557858306494000942859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18267410477741992001257145 13700557858306494000942859)
        ·
          refine ⟨20550836787459741001414289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13700557858306494000942859 20550836787459741001414289)
          ·
            refine ⟨15413127590594805751060717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20550836787459741001414289 15413127590594805751060717)
            ·
              refine ⟨5779922846473052156647769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15413127590594805751060717 5779922846473052156647769)
              ·
                refine ⟨4334942134854789117485827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5779922846473052156647769 4334942134854789117485827)
                ·
                  refine ⟨6502413202282183676228741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4334942134854789117485827 6502413202282183676228741)
                  ·
                    refine ⟨1219202475427909439292889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6502413202282183676228741 1219202475427909439292889)
                    ·
                      rfl

theorem cell23_7123165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_7123165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123165 prefixEnd_7123165 := by exact prefixLift 7123165
  have htrace : WordTrace (prefixWord ++ tailWord_7123165) baseStart_7123165 baseEnd_7123165 := by
    simpa [prefixWord, tailWord_7123165, baseEnd_7123165] using wordTrace_append hprefix tailTrace_7123165
  have hstable : (prefixWord ++ tailWord_7123165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123165).length < 2 ^ (prefixWord ++ tailWord_7123165).sum := by decide
  have hdescent : baseEnd_7123165 < baseStart_7123165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123177 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 5, 1, 4]
def baseStart_7123177 : Nat := 118140960795 + 7123177 * 2 ^ 59
def prefixEnd_7123177 : Nat := 4983230072969 + 3 ^ 40 * 7123177 * 2
def baseEnd_7123177 : Nat := 3657613588051582270928611

theorem tailTrace_7123177 : CollatzResearch.WordTrace tailWord_7123177 prefixEnd_7123177 3657613588051582270928611 := by
  unfold tailWord_7123177
  simp only [CollatzResearch.WordTrace]
  refine ⟨259803608914953745622871785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173202405943302497081914523 259803608914953745622871785)
  ·
    refine ⟨194852706686215309217153839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259803608914953745622871785 194852706686215309217153839)
    ·
      refine ⟨292279060029322963825730759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194852706686215309217153839 292279060029322963825730759)
      ·
        refine ⟨438418590043984445738596139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292279060029322963825730759 438418590043984445738596139)
        ·
          refine ⟨657627885065976668607894209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438418590043984445738596139 657627885065976668607894209)
          ·
            refine ⟨493220913799482501455920657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657627885065976668607894209 493220913799482501455920657)
            ·
              refine ⟨369915685349611876091940493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493220913799482501455920657 369915685349611876091940493)
              ·
                refine ⟨138718382006104453534477685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369915685349611876091940493 138718382006104453534477685)
                ·
                  refine ⟨13004848313072292518857283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138718382006104453534477685 13004848313072292518857283)
                  ·
                    refine ⟨19507272469608438778285925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13004848313072292518857283 19507272469608438778285925)
                    ·
                      refine ⟨3657613588051582270928611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19507272469608438778285925 3657613588051582270928611)
                      ·
                        rfl

theorem cell23_7123177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 1, 4].length) (baseStart_7123177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123177 prefixEnd_7123177 := by exact prefixLift 7123177
  have htrace : WordTrace (prefixWord ++ tailWord_7123177) baseStart_7123177 baseEnd_7123177 := by
    simpa [prefixWord, tailWord_7123177, baseEnd_7123177] using wordTrace_append hprefix tailTrace_7123177
  have hstable : (prefixWord ++ tailWord_7123177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123177).length < 2 ^ (prefixWord ++ tailWord_7123177).sum := by decide
  have hdescent : baseEnd_7123177 < baseStart_7123177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123187 : List Nat := [1, 1, 1, 2, 2, 4, 2, 3, 1, 6]
def baseStart_7123187 : Nat := 118140960795 + 7123187 * 2 ^ 59
def prefixEnd_7123187 : Nat := 4983230072969 + 3 ^ 40 * 7123187 * 2
def baseEnd_7123187 : Nat := 1219206240952709077267855

theorem tailTrace_7123187 : CollatzResearch.WordTrace tailWord_7123187 prefixEnd_7123187 1219206240952709077267855 := by
  unfold tailWord_7123187
  simp only [CollatzResearch.WordTrace]
  refine ⟨259803973644917517330735815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173202649096611678220490543 259803973644917517330735815)
  ·
    refine ⟨389705960467376275996103723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259803973644917517330735815 389705960467376275996103723)
    ·
      refine ⟨584558940701064413994155585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389705960467376275996103723 584558940701064413994155585)
      ·
        refine ⟨438419205525798310495616689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 584558940701064413994155585 438419205525798310495616689)
        ·
          refine ⟨328814404144348732871712517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438419205525798310495616689 328814404144348732871712517)
          ·
            refine ⟨61652700777065387413446097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 328814404144348732871712517 61652700777065387413446097)
            ·
              refine ⟨46239525582799040560084573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61652700777065387413446097 46239525582799040560084573)
              ·
                refine ⟨17339822093549640210031715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46239525582799040560084573 17339822093549640210031715)
                ·
                  refine ⟨26009733140324460315047573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17339822093549640210031715 26009733140324460315047573)
                  ·
                    refine ⟨1219206240952709077267855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26009733140324460315047573 1219206240952709077267855)
                    ·
                      rfl

theorem cell23_7123187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 6].length) (baseStart_7123187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123187 prefixEnd_7123187 := by exact prefixLift 7123187
  have htrace : WordTrace (prefixWord ++ tailWord_7123187) baseStart_7123187 baseEnd_7123187 := by
    simpa [prefixWord, tailWord_7123187, baseEnd_7123187] using wordTrace_append hprefix tailTrace_7123187
  have hstable : (prefixWord ++ tailWord_7123187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123187).length < 2 ^ (prefixWord ++ tailWord_7123187).sum := by decide
  have hdescent : baseEnd_7123187 < baseStart_7123187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123194 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4]
def baseStart_7123194 : Nat := 118140960795 + 7123194 * 2 ^ 59
def prefixEnd_7123194 : Nat := 4983230072969 + 3 ^ 40 * 7123194 * 2
def baseEnd_7123194 : Nat := 3657622317222708704416033

theorem tailTrace_7123194 : CollatzResearch.WordTrace tailWord_7123194 prefixEnd_7123194 3657622317222708704416033 := by
  unfold tailWord_7123194
  simp only [CollatzResearch.WordTrace]
  refine ⟨64951057238973039381560159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173202819303928105017493757 64951057238973039381560159)
  ·
    refine ⟨97426585858459559072340239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64951057238973039381560159 97426585858459559072340239)
    ·
      refine ⟨146139878787689338608510359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97426585858459559072340239 146139878787689338608510359)
      ·
        refine ⟨219209818181534007912765539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146139878787689338608510359 219209818181534007912765539)
        ·
          refine ⟨328814727272301011869148309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219209818181534007912765539 328814727272301011869148309)
          ·
            refine ⟨15413190340889109931366327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 328814727272301011869148309 15413190340889109931366327)
            ·
              refine ⟨23119785511333664897049491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15413190340889109931366327 23119785511333664897049491)
              ·
                refine ⟨34679678267000497345574237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23119785511333664897049491 34679678267000497345574237)
                ·
                  refine ⟨13004879350125186504590339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34679678267000497345574237 13004879350125186504590339)
                  ·
                    refine ⟨19507319025187779756885509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13004879350125186504590339 19507319025187779756885509)
                    ·
                      refine ⟨3657622317222708704416033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19507319025187779756885509 3657622317222708704416033)
                      ·
                        rfl

theorem cell23_7123194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_7123194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123194 prefixEnd_7123194 := by exact prefixLift 7123194
  have htrace : WordTrace (prefixWord ++ tailWord_7123194) baseStart_7123194 baseEnd_7123194 := by
    simpa [prefixWord, tailWord_7123194, baseEnd_7123194] using wordTrace_append hprefix tailTrace_7123194
  have hstable : (prefixWord ++ tailWord_7123194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123194).length < 2 ^ (prefixWord ++ tailWord_7123194).sum := by decide
  have hdescent : baseEnd_7123194 < baseStart_7123194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123197 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_7123197 : Nat := 118140960795 + 7123197 * 2 ^ 59
def prefixEnd_7123197 : Nat := 4983230072969 + 3 ^ 40 * 7123197 * 2
def baseEnd_7123197 : Nat := 3657623857664672192678519

theorem tailTrace_7123197 : CollatzResearch.WordTrace tailWord_7123197 prefixEnd_7123197 3657623857664672192678519 := by
  unfold tailWord_7123197
  simp only [CollatzResearch.WordTrace]
  refine ⟨259804338374881289038599845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173202892249920859359066563 259804338374881289038599845)
  ·
    refine ⟨48713313445290241694737471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259804338374881289038599845 48713313445290241694737471)
    ·
      refine ⟨73069970167935362542106207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48713313445290241694737471 73069970167935362542106207)
      ·
        refine ⟨109604955251903043813159311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73069970167935362542106207 109604955251903043813159311)
        ·
          refine ⟨164407432877854565719738967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109604955251903043813159311 164407432877854565719738967)
          ·
            refine ⟨246611149316781848579608451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164407432877854565719738967 246611149316781848579608451)
            ·
              refine ⟨369916723975172772869412677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246611149316781848579608451 369916723975172772869412677)
              ·
                refine ⟨69359385745344894913014877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 369916723975172772869412677 69359385745344894913014877)
                ·
                  refine ⟨26009769654504335592380579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69359385745344894913014877 26009769654504335592380579)
                  ·
                    refine ⟨39014654481756503388570869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26009769654504335592380579 39014654481756503388570869)
                    ·
                      refine ⟨3657623857664672192678519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39014654481756503388570869 3657623857664672192678519)
                      ·
                        rfl

theorem cell23_7123197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_7123197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123197 prefixEnd_7123197 := by exact prefixLift 7123197
  have htrace : WordTrace (prefixWord ++ tailWord_7123197) baseStart_7123197 baseEnd_7123197 := by
    simpa [prefixWord, tailWord_7123197, baseEnd_7123197] using wordTrace_append hprefix tailTrace_7123197
  have hstable : (prefixWord ++ tailWord_7123197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123197).length < 2 ^ (prefixWord ++ tailWord_7123197).sum := by decide
  have hdescent : baseEnd_7123197 < baseStart_7123197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123198 : List Nat := [4, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_7123198 : Nat := 118140960795 + 7123198 * 2 ^ 59
def prefixEnd_7123198 : Nat := 4983230072969 + 3 ^ 40 * 7123198 * 2
def baseEnd_7123198 : Nat := 3657624371145326688766015

theorem tailTrace_7123198 : CollatzResearch.WordTrace tailWord_7123198 prefixEnd_7123198 3657624371145326688766015 := by
  unfold tailWord_7123198
  simp only [CollatzResearch.WordTrace]
  refine ⟨32475546855984708276173281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173202916565251777472924165 32475546855984708276173281)
  ·
    refine ⟨24356660141988531207129961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32475546855984708276173281 24356660141988531207129961)
    ·
      refine ⟨18267495106491398405347471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24356660141988531207129961 18267495106491398405347471)
      ·
        refine ⟨27401242659737097608021207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18267495106491398405347471 27401242659737097608021207)
        ·
          refine ⟨41101863989605646412031811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27401242659737097608021207 41101863989605646412031811)
          ·
            refine ⟨61652795984408469618047717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41101863989605646412031811 61652795984408469618047717)
            ·
              refine ⟨11559899247076588053383947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61652795984408469618047717 11559899247076588053383947)
              ·
                refine ⟨17339848870614882080075921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11559899247076588053383947 17339848870614882080075921)
                ·
                  refine ⟨13004886652961161560056941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17339848870614882080075921 13004886652961161560056941)
                  ·
                    refine ⟨4876832494860435585021353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13004886652961161560056941 4876832494860435585021353)
                    ·
                      refine ⟨3657624371145326688766015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4876832494860435585021353 3657624371145326688766015)
                      ·
                        rfl

theorem cell23_7123198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_7123198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123198 prefixEnd_7123198 := by exact prefixLift 7123198
  have htrace : WordTrace (prefixWord ++ tailWord_7123198) baseStart_7123198 baseEnd_7123198 := by
    simpa [prefixWord, tailWord_7123198, baseEnd_7123198] using wordTrace_append hprefix tailTrace_7123198
  have hstable : (prefixWord ++ tailWord_7123198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123198).length < 2 ^ (prefixWord ++ tailWord_7123198).sum := by decide
  have hdescent : baseEnd_7123198 < baseStart_7123198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123211 : List Nat := [1, 1, 1, 1, 5, 2, 5, 1, 1, 1, 4]
def baseStart_7123211 : Nat := 118140960795 + 7123211 * 2 ^ 59
def prefixEnd_7123211 : Nat := 4983230072969 + 3 ^ 40 * 7123211 * 2
def baseEnd_7123211 : Nat := 3657631046393835137903455

theorem tailTrace_7123211 : CollatzResearch.WordTrace tailWord_7123211 prefixEnd_7123211 3657631046393835137903455 := by
  unfold tailWord_7123211
  simp only [CollatzResearch.WordTrace]
  refine ⟨259804848996830569429609487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173203232664553712953072991 259804848996830569429609487)
  ·
    refine ⟨389707273495245854144414231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259804848996830569429609487 389707273495245854144414231)
    ·
      refine ⟨584560910242868781216621347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389707273495245854144414231 584560910242868781216621347)
      ·
        refine ⟨876841365364303171824932021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584560910242868781216621347 876841365364303171824932021)
        ·
          refine ⟨82203878002903422358587377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 876841365364303171824932021 82203878002903422358587377)
          ·
            refine ⟨61652908502177566768940533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82203878002903422358587377 61652908502177566768940533)
            ·
              refine ⟨5779960172079146884588175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61652908502177566768940533 5779960172079146884588175)
              ·
                refine ⟨8669940258118720326882263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5779960172079146884588175 8669940258118720326882263)
                ·
                  refine ⟨13004910387178080490323395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8669940258118720326882263 13004910387178080490323395)
                  ·
                    refine ⟨19507365580767120735485093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13004910387178080490323395 19507365580767120735485093)
                    ·
                      refine ⟨3657631046393835137903455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19507365580767120735485093 3657631046393835137903455)
                      ·
                        rfl

theorem cell23_7123211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 1, 1, 4].length) (baseStart_7123211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123211 prefixEnd_7123211 := by exact prefixLift 7123211
  have htrace : WordTrace (prefixWord ++ tailWord_7123211) baseStart_7123211 baseEnd_7123211 := by
    simpa [prefixWord, tailWord_7123211, baseEnd_7123211] using wordTrace_append hprefix tailTrace_7123211
  have hstable : (prefixWord ++ tailWord_7123211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123211).length < 2 ^ (prefixWord ++ tailWord_7123211).sum := by decide
  have hdescent : baseEnd_7123211 < baseStart_7123211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123234 : List Nat := [3, 3, 1, 1, 3, 1, 3, 8]
def baseStart_7123234 : Nat := 118140960795 + 7123234 * 2 ^ 59
def prefixEnd_7123234 : Nat := 4983230072969 + 3 ^ 40 * 7123234 * 2
def baseEnd_7123234 : Nat := 135468253942551427700587

theorem tailTrace_7123234 : CollatzResearch.WordTrace tailWord_7123234 prefixEnd_7123234 135468253942551427700587 := by
  unfold tailWord_7123234
  simp only [CollatzResearch.WordTrace]
  refine ⟨64951421968936811089424189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173203791917164829571797837 64951421968936811089424189)
  ·
    refine ⟨24356783238351304158534071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64951421968936811089424189 24356783238351304158534071)
    ·
      refine ⟨36535174857526956237801107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24356783238351304158534071 36535174857526956237801107)
      ·
        refine ⟨54802762286290434356701661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36535174857526956237801107 54802762286290434356701661)
        ·
          refine ⟨20551035857358912883763123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54802762286290434356701661 20551035857358912883763123)
          ·
            refine ⟨30826553786038369325644685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20551035857358912883763123 30826553786038369325644685)
            ·
              refine ⟨11559957669764388497116757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30826553786038369325644685 11559957669764388497116757)
              ·
                refine ⟨135468253942551427700587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11559957669764388497116757 135468253942551427700587)
                ·
                  rfl

theorem cell23_7123234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 8].length) (baseStart_7123234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123234 prefixEnd_7123234 := by exact prefixLift 7123234
  have htrace : WordTrace (prefixWord ++ tailWord_7123234) baseStart_7123234 baseEnd_7123234 := by
    simpa [prefixWord, tailWord_7123234, baseEnd_7123234] using wordTrace_append hprefix tailTrace_7123234
  have hstable : (prefixWord ++ tailWord_7123234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123234).length < 2 ^ (prefixWord ++ tailWord_7123234).sum := by decide
  have hdescent : baseEnd_7123234 < baseStart_7123234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123244 : List Nat := [2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 3]
def baseStart_7123244 : Nat := 118140960795 + 7123244 * 2 ^ 59
def prefixEnd_7123244 : Nat := 4983230072969 + 3 ^ 40 * 7123244 * 2
def baseEnd_7123244 : Nat := 3657647991255433508790803

theorem tailTrace_7123244 : CollatzResearch.WordTrace tailWord_7123244 prefixEnd_7123244 3657647991255433508790803 := by
  unfold tailWord_7123244
  simp only [CollatzResearch.WordTrace]
  refine ⟨129903026302855508032780393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173204035070474010710373857 129903026302855508032780393)
  ·
    refine ⟨97427269727141631024585295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129903026302855508032780393 97427269727141631024585295)
    ·
      refine ⟨146140904590712446536877943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97427269727141631024585295 146140904590712446536877943)
      ·
        refine ⟨219211356886068669805316915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146140904590712446536877943 219211356886068669805316915)
        ·
          refine ⟨328817035329103004707975373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219211356886068669805316915 328817035329103004707975373)
          ·
            refine ⟨123306388248413626765490765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328817035329103004707975373 123306388248413626765490765)
            ·
              refine ⟨46239895593155110037059037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123306388248413626765490765 46239895593155110037059037)
              ·
                refine ⟨17339960847433166263897139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46239895593155110037059037 17339960847433166263897139)
                ·
                  refine ⟨26009941271149749395845709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17339960847433166263897139 26009941271149749395845709)
                  ·
                    refine ⟨9753727976681156023442141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26009941271149749395845709 9753727976681156023442141)
                    ·
                      refine ⟨3657647991255433508790803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9753727976681156023442141 3657647991255433508790803)
                      ·
                        rfl

theorem cell23_7123244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_7123244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123244 prefixEnd_7123244 := by exact prefixLift 7123244
  have htrace : WordTrace (prefixWord ++ tailWord_7123244) baseStart_7123244 baseEnd_7123244 := by
    simpa [prefixWord, tailWord_7123244, baseEnd_7123244] using wordTrace_append hprefix tailTrace_7123244
  have hstable : (prefixWord ++ tailWord_7123244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123244).length < 2 ^ (prefixWord ++ tailWord_7123244).sum := by decide
  have hdescent : baseEnd_7123244 < baseStart_7123244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123262 : List Nat := [4, 2, 1, 2, 1, 3, 2, 3, 1, 2, 2]
def baseStart_7123262 : Nat := 118140960795 + 7123262 * 2 ^ 59
def prefixEnd_7123262 : Nat := 4983230072969 + 3 ^ 40 * 7123262 * 2
def baseEnd_7123262 : Nat := 3657657233907214438365721

theorem tailTrace_7123262 : CollatzResearch.WordTrace tailWord_7123262 prefixEnd_7123262 3657657233907214438365721 := by
  unfold tailWord_7123262
  simp only [CollatzResearch.WordTrace]
  refine ⟨32475838639955725642464505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173204472746430536759810693 32475838639955725642464505)
  ·
    refine ⟨24356878979966794231848379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32475838639955725642464505 24356878979966794231848379)
    ·
      refine ⟨36535318469950191347772569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24356878979966794231848379 36535318469950191347772569)
      ·
        refine ⟨27401488852462643510829427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36535318469950191347772569 27401488852462643510829427)
        ·
          refine ⟨41102233278693965266244141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27401488852462643510829427 41102233278693965266244141)
          ·
            refine ⟨15413337479510236974841553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41102233278693965266244141 15413337479510236974841553)
            ·
              refine ⟨11560003109632677731131165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15413337479510236974841553 11560003109632677731131165)
              ·
                refine ⟨4335001166112254149174187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11560003109632677731131165 4335001166112254149174187)
                ·
                  refine ⟨6502501749168381223761281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4335001166112254149174187 6502501749168381223761281)
                  ·
                    refine ⟨4876876311876285917820961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6502501749168381223761281 4876876311876285917820961)
                    ·
                      refine ⟨3657657233907214438365721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4876876311876285917820961 3657657233907214438365721)
                      ·
                        rfl

theorem cell23_7123262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_7123262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123262 prefixEnd_7123262 := by exact prefixLift 7123262
  have htrace : WordTrace (prefixWord ++ tailWord_7123262) baseStart_7123262 baseEnd_7123262 := by
    simpa [prefixWord, tailWord_7123262, baseEnd_7123262] using wordTrace_append hprefix tailTrace_7123262
  have hstable : (prefixWord ++ tailWord_7123262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123262).length < 2 ^ (prefixWord ++ tailWord_7123262).sum := by decide
  have hdescent : baseEnd_7123262 < baseStart_7123262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123352 : List Nat := [2, 1, 2, 5, 1, 1, 4, 1, 2, 2, 2]
def baseStart_7123352 : Nat := 118140960795 + 7123352 * 2 ^ 59
def prefixEnd_7123352 : Nat := 4983230072969 + 3 ^ 40 * 7123352 * 2
def baseEnd_7123352 : Nat := 3657703447166119086240307

theorem tailTrace_7123352 : CollatzResearch.WordTrace tailWord_7123352 prefixEnd_7123352 3657703447166119086240307 := by
  unfold tailWord_7123352
  simp only [CollatzResearch.WordTrace]
  refine ⟨129904995844659875255246155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173206661126213167006994873 129904995844659875255246155)
  ·
    refine ⟨194857493766989812882869233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129904995844659875255246155 194857493766989812882869233)
    ·
      refine ⟨146143120325242359662151925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194857493766989812882869233 146143120325242359662151925)
      ·
        refine ⟨13700917530491471218326743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146143120325242359662151925 13700917530491471218326743)
        ·
          refine ⟨20551376295737206827490115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13700917530491471218326743 20551376295737206827490115)
          ·
            refine ⟨30827064443605810241235173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20551376295737206827490115 30827064443605810241235173)
            ·
              refine ⟨5780074583176089420231595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30827064443605810241235173 5780074583176089420231595)
              ·
                refine ⟨8670111874764134130347393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5780074583176089420231595 8670111874764134130347393)
                ·
                  refine ⟨6502583906073100597760545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8670111874764134130347393 6502583906073100597760545)
                  ·
                    refine ⟨4876937929554825448320409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6502583906073100597760545 4876937929554825448320409)
                    ·
                      refine ⟨3657703447166119086240307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4876937929554825448320409 3657703447166119086240307)
                      ·
                        rfl

theorem cell23_7123352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_7123352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123352 prefixEnd_7123352 := by exact prefixLift 7123352
  have htrace : WordTrace (prefixWord ++ tailWord_7123352) baseStart_7123352 baseEnd_7123352 := by
    simpa [prefixWord, tailWord_7123352, baseEnd_7123352] using wordTrace_append hprefix tailTrace_7123352
  have hstable : (prefixWord ++ tailWord_7123352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123352).length < 2 ^ (prefixWord ++ tailWord_7123352).sum := by decide
  have hdescent : baseEnd_7123352 < baseStart_7123352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123451 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 5, 5, 2]
def baseStart_7123451 : Nat := 118140960795 + 7123451 * 2 ^ 59
def prefixEnd_7123451 : Nat := 4983230072969 + 3 ^ 40 * 7123451 * 2
def baseEnd_7123451 : Nat := 3657754281750914198902351

theorem tailTrace_7123451 : CollatzResearch.WordTrace tailWord_7123451 prefixEnd_7123451 3657754281750914198902351 := by
  unfold tailWord_7123451
  simp only [CollatzResearch.WordTrace]
  refine ⟨259813602515961090418346207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173209068343974060278897471 259813602515961090418346207)
  ·
    refine ⟨389720403773941635627519311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259813602515961090418346207 389720403773941635627519311)
    ·
      refine ⟨584580605660912453441278967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389720403773941635627519311 584580605660912453441278967)
      ·
        refine ⟨876870908491368680161918451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584580605660912453441278967 876870908491368680161918451)
        ·
          refine ⟨1315306362737053020242877677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876870908491368680161918451 1315306362737053020242877677)
          ·
            refine ⟨493239886026394882591079129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1315306362737053020242877677 493239886026394882591079129)
            ·
              refine ⟨369929914519796161943309347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493239886026394882591079129 369929914519796161943309347)
              ·
                refine ⟨554894871779694242914964021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369929914519796161943309347 554894871779694242914964021)
                ·
                  refine ⟨52021394229346335273277877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 554894871779694242914964021 52021394229346335273277877)
                  ·
                    refine ⟨4877005709001218931869801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52021394229346335273277877 4877005709001218931869801)
                    ·
                      refine ⟨3657754281750914198902351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4877005709001218931869801 3657754281750914198902351)
                      ·
                        rfl

theorem cell23_7123451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 5, 2].length) (baseStart_7123451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123451 prefixEnd_7123451 := by exact prefixLift 7123451
  have htrace : WordTrace (prefixWord ++ tailWord_7123451) baseStart_7123451 baseEnd_7123451 := by
    simpa [prefixWord, tailWord_7123451, baseEnd_7123451] using wordTrace_append hprefix tailTrace_7123451
  have hstable : (prefixWord ++ tailWord_7123451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123451).length < 2 ^ (prefixWord ++ tailWord_7123451).sum := by decide
  have hdescent : baseEnd_7123451 < baseStart_7123451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123462 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_7123462 : Nat := 118140960795 + 7123462 * 2 ^ 59
def prefixEnd_7123462 : Nat := 4983230072969 + 3 ^ 40 * 7123462 * 2
def baseEnd_7123462 : Nat := 3657759930038113655864801

theorem tailTrace_7123462 : CollatzResearch.WordTrace tailWord_7123462 prefixEnd_7123462 3657759930038113655864801 := by
  unfold tailWord_7123462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8119187616216288728031145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 173209335812614159531331093 8119187616216288728031145)
  ·
    refine ⟨6089390712162216546023359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8119187616216288728031145 6089390712162216546023359)
    ·
      refine ⟨9134086068243324819035039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6089390712162216546023359 9134086068243324819035039)
      ·
        refine ⟨13701129102364987228552559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9134086068243324819035039 13701129102364987228552559)
        ·
          refine ⟨20551693653547480842828839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13701129102364987228552559 20551693653547480842828839)
          ·
            refine ⟨30827540480321221264243259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20551693653547480842828839 30827540480321221264243259)
            ·
              refine ⟨46241310720481831896364889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30827540480321221264243259 46241310720481831896364889)
              ·
                refine ⟨34680983040361373922273667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46241310720481831896364889 34680983040361373922273667)
                ·
                  refine ⟨52021474560542060883410501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34680983040361373922273667 52021474560542060883410501)
                  ·
                    refine ⟨9754026480101636415639469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52021474560542060883410501 9754026480101636415639469)
                    ·
                      refine ⟨3657759930038113655864801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9754026480101636415639469 3657759930038113655864801)
                      ·
                        rfl

theorem cell23_7123462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_7123462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123462 prefixEnd_7123462 := by exact prefixLift 7123462
  have htrace : WordTrace (prefixWord ++ tailWord_7123462) baseStart_7123462 baseEnd_7123462 := by
    simpa [prefixWord, tailWord_7123462, baseEnd_7123462] using wordTrace_append hprefix tailTrace_7123462
  have hstable : (prefixWord ++ tailWord_7123462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123462).length < 2 ^ (prefixWord ++ tailWord_7123462).sum := by decide
  have hdescent : baseEnd_7123462 < baseStart_7123462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123468 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 1, 5, 2]
def baseStart_7123468 : Nat := 118140960795 + 7123468 * 2 ^ 59
def prefixEnd_7123468 : Nat := 4983230072969 + 3 ^ 40 * 7123468 * 2
def baseEnd_7123468 : Nat := 3657763010922040632389773

theorem tailTrace_7123468 : CollatzResearch.WordTrace tailWord_7123468 prefixEnd_7123468 3657763010922040632389773 := by
  unfold tailWord_7123468
  simp only [CollatzResearch.WordTrace]
  refine ⟨129907111278449751160857529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173209481704599668214476705 129907111278449751160857529)
  ·
    refine ⟨97430333458837313370643147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129907111278449751160857529 97430333458837313370643147)
    ·
      refine ⟨146145500188255970055964721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97430333458837313370643147 146145500188255970055964721)
      ·
        refine ⟨109609125141191977541973541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146145500188255970055964721 109609125141191977541973541)
        ·
          refine ⟨20551710963973495789120039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109609125141191977541973541 20551710963973495789120039)
          ·
            refine ⟨30827566445960243683680059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20551710963973495789120039 30827566445960243683680059)
            ·
              refine ⟨46241349668940365525520089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30827566445960243683680059 46241349668940365525520089)
              ·
                refine ⟨34681012251705274144140067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46241349668940365525520089 34681012251705274144140067)
                ·
                  refine ⟨52021518377557911216210101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34681012251705274144140067 52021518377557911216210101)
                  ·
                    refine ⟨4877017347896054176519697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52021518377557911216210101 4877017347896054176519697)
                    ·
                      refine ⟨3657763010922040632389773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4877017347896054176519697 3657763010922040632389773)
                      ·
                        rfl

theorem cell23_7123468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_7123468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123468 prefixEnd_7123468 := by exact prefixLift 7123468
  have htrace : WordTrace (prefixWord ++ tailWord_7123468) baseStart_7123468 baseEnd_7123468 := by
    simpa [prefixWord, tailWord_7123468, baseEnd_7123468] using wordTrace_append hprefix tailTrace_7123468
  have hstable : (prefixWord ++ tailWord_7123468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123468).length < 2 ^ (prefixWord ++ tailWord_7123468).sum := by decide
  have hdescent : baseEnd_7123468 < baseStart_7123468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123502 : List Nat := [4, 1, 3, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_7123502 : Nat := 118140960795 + 7123502 * 2 ^ 59
def prefixEnd_7123502 : Nat := 4983230072969 + 3 ^ 40 * 7123502 * 2
def baseEnd_7123502 : Nat := 3657780469264293499364617

theorem tailTrace_7123502 : CollatzResearch.WordTrace tailWord_7123502 prefixEnd_7123502 3657780469264293499364617 := by
  unfold tailWord_7123502
  simp only [CollatzResearch.WordTrace]
  refine ⟨32476932829847040766056595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173210308425850884085635173 32476932829847040766056595)
  ·
    refine ⟨48715399244770561149084893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32476932829847040766056595 48715399244770561149084893)
    ·
      refine ⟨18268274716788960430906835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48715399244770561149084893 18268274716788960430906835)
      ·
        refine ⟨27402412075183440646360253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18268274716788960430906835 27402412075183440646360253)
        ·
          refine ⟨10275904528193790242385095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27402412075183440646360253 10275904528193790242385095)
          ·
            refine ⟨15413856792290685363577643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10275904528193790242385095 15413856792290685363577643)
            ·
              refine ⟨23120785188436028045366465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15413856792290685363577643 23120785188436028045366465)
              ·
                refine ⟨17340588891327021034024849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23120785188436028045366465 17340588891327021034024849)
                ·
                  refine ⟨13005441668495265775518637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17340588891327021034024849 13005441668495265775518637)
                  ·
                    refine ⟨4877040625685724665819489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13005441668495265775518637 4877040625685724665819489)
                    ·
                      refine ⟨3657780469264293499364617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4877040625685724665819489 3657780469264293499364617)
                      ·
                        rfl

theorem cell23_7123502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_7123502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123502 prefixEnd_7123502 := by exact prefixLift 7123502
  have htrace : WordTrace (prefixWord ++ tailWord_7123502) baseStart_7123502 baseEnd_7123502 := by
    simpa [prefixWord, tailWord_7123502, baseEnd_7123502] using wordTrace_append hprefix tailTrace_7123502
  have hstable : (prefixWord ++ tailWord_7123502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123502).length < 2 ^ (prefixWord ++ tailWord_7123502).sum := by decide
  have hdescent : baseEnd_7123502 < baseStart_7123502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123504 : List Nat := [2, 1, 1, 1, 2, 3, 13]
def baseStart_7123504 : Nat := 118140960795 + 7123504 * 2 ^ 59
def prefixEnd_7123504 : Nat := 4983230072969 + 3 ^ 40 * 7123504 * 2
def baseEnd_7123504 : Nat := 45157796249698796191847

theorem tailTrace_7123504 : CollatzResearch.WordTrace tailWord_7123504 prefixEnd_7123504 45157796249698796191847 := by
  unfold tailWord_7123504
  simp only [CollatzResearch.WordTrace]
  refine ⟨129907767792384540235012783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173210357056512720313350377 129907767792384540235012783)
  ·
    refine ⟨194861651688576810352519175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129907767792384540235012783 194861651688576810352519175)
    ·
      refine ⟨292292477532865215528778763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194861651688576810352519175 292292477532865215528778763)
      ·
        refine ⟨438438716299297823293168145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292292477532865215528778763 438438716299297823293168145)
        ·
          refine ⟨328829037224473367469876109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438438716299297823293168145 328829037224473367469876109)
          ·
            refine ⟨123310888959177512801203541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328829037224473367469876109 123310888959177512801203541)
            ·
              refine ⟨45157796249698796191847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 123310888959177512801203541 45157796249698796191847)
              ·
                rfl

theorem cell23_7123504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 13].length) (baseStart_7123504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123504 prefixEnd_7123504 := by exact prefixLift 7123504
  have htrace : WordTrace (prefixWord ++ tailWord_7123504) baseStart_7123504 baseEnd_7123504 := by
    simpa [prefixWord, tailWord_7123504, baseEnd_7123504] using wordTrace_append hprefix tailTrace_7123504
  have hstable : (prefixWord ++ tailWord_7123504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123504).length < 2 ^ (prefixWord ++ tailWord_7123504).sum := by decide
  have hdescent : baseEnd_7123504 < baseStart_7123504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123521 : List Nat := [1, 2, 5, 1, 1, 2, 1, 10]
def baseStart_7123521 : Nat := 118140960795 + 7123521 * 2 ^ 59
def prefixEnd_7123521 : Nat := 4983230072969 + 3 ^ 40 * 7123521 * 2
def baseEnd_7123521 : Nat := 135473712051730700926927

theorem tailTrace_7123521 : CollatzResearch.WordTrace tailWord_7123521 prefixEnd_7123521 135473712051730700926927 := by
  unfold tailWord_7123521
  simp only [CollatzResearch.WordTrace]
  refine ⟨259816155625707492373394417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173210770417138328248929611 259816155625707492373394417)
  ·
    refine ⟨194862116719280619280045813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259816155625707492373394417 194862116719280619280045813)
    ·
      refine ⟨18268323442432558057504295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194862116719280619280045813 18268323442432558057504295)
      ·
        refine ⟨27402485163648837086256443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18268323442432558057504295 27402485163648837086256443)
        ·
          refine ⟨41103727745473255629384665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27402485163648837086256443 41103727745473255629384665)
          ·
            refine ⟨30827795809104941722038499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41103727745473255629384665 30827795809104941722038499)
            ·
              refine ⟨46241693713657412583057749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30827795809104941722038499 46241693713657412583057749)
              ·
                refine ⟨135473712051730700926927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46241693713657412583057749 135473712051730700926927)
                ·
                  rfl

theorem cell23_7123521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 10].length) (baseStart_7123521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123521 prefixEnd_7123521 := by exact prefixLift 7123521
  have htrace : WordTrace (prefixWord ++ tailWord_7123521) baseStart_7123521 baseEnd_7123521 := by
    simpa [prefixWord, tailWord_7123521, baseEnd_7123521] using wordTrace_append hprefix tailTrace_7123521
  have hstable : (prefixWord ++ tailWord_7123521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123521).length < 2 ^ (prefixWord ++ tailWord_7123521).sum := by decide
  have hdescent : baseEnd_7123521 < baseStart_7123521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123525 : List Nat := [1, 3, 1, 1, 1, 5, 4, 1, 2, 4]
def baseStart_7123525 : Nat := 118140960795 + 7123525 * 2 ^ 59
def prefixEnd_7123525 : Nat := 4983230072969 + 3 ^ 40 * 7123525 * 2
def baseEnd_7123525 : Nat := 1219264093106448969792337

theorem tailTrace_7123525 : CollatzResearch.WordTrace tailWord_7123525 prefixEnd_7123525 1219264093106448969792337 := by
  unfold tailWord_7123525
  simp only [CollatzResearch.WordTrace]
  refine ⟨259816301517693001056540029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173210867678462000704360019 259816301517693001056540029)
  ·
    refine ⟨97431113069134875396202511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259816301517693001056540029 97431113069134875396202511)
    ·
      refine ⟨146146669603702313094303767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97431113069134875396202511 146146669603702313094303767)
      ·
        refine ⟨219220004405553469641455651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146146669603702313094303767 219220004405553469641455651)
        ·
          refine ⟨328830006608330204462183477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219220004405553469641455651 328830006608330204462183477)
          ·
            refine ⟨30827813119530956668329701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 328830006608330204462183477 30827813119530956668329701)
            ·
              refine ⟨5780214959912054375311819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30827813119530956668329701 5780214959912054375311819)
              ·
                refine ⟨8670322439868081562967729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5780214959912054375311819 8670322439868081562967729)
                ·
                  refine ⟨6502741829901061172225797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8670322439868081562967729 6502741829901061172225797)
                  ·
                    refine ⟨1219264093106448969792337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6502741829901061172225797 1219264093106448969792337)
                    ·
                      rfl

theorem cell23_7123525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 2, 4].length) (baseStart_7123525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123525 prefixEnd_7123525 := by exact prefixLift 7123525
  have htrace : WordTrace (prefixWord ++ tailWord_7123525) baseStart_7123525 baseEnd_7123525 := by
    simpa [prefixWord, tailWord_7123525, baseEnd_7123525] using wordTrace_append hprefix tailTrace_7123525
  have hstable : (prefixWord ++ tailWord_7123525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123525).length < 2 ^ (prefixWord ++ tailWord_7123525).sum := by decide
  have hdescent : baseEnd_7123525 < baseStart_7123525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123566 : List Nat := [4, 1, 2, 2, 2, 1, 4, 2, 1, 2, 2]
def baseStart_7123566 : Nat := 118140960795 + 7123566 * 2 ^ 59
def prefixEnd_7123566 : Nat := 4983230072969 + 3 ^ 40 * 7123566 * 2
def baseEnd_7123566 : Nat := 3657813332026181248964323

theorem tailTrace_7123566 : CollatzResearch.WordTrace tailWord_7123566 prefixEnd_7123566 3657813332026181248964323 := by
  unfold tailWord_7123566
  simp only [CollatzResearch.WordTrace]
  refine ⟨32477224613818058132347819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173211864607029643372521701 32477224613818058132347819)
  ·
    refine ⟨48715836920727087198521729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32477224613818058132347819 48715836920727087198521729)
    ·
      refine ⟨36536877690545315398891297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48715836920727087198521729 36536877690545315398891297)
      ·
        refine ⟨27402658267908986549168473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36536877690545315398891297 27402658267908986549168473)
        ·
          refine ⟨20551993700931739911876355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27402658267908986549168473 20551993700931739911876355)
          ·
            refine ⟨30827990551397609867814533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20551993700931739911876355 30827990551397609867814533)
            ·
              refine ⟨5780248228387051850215225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30827990551397609867814533 5780248228387051850215225)
              ·
                refine ⟨4335186171290288887661419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5780248228387051850215225 4335186171290288887661419)
                ·
                  refine ⟨6502779256935433331492129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4335186171290288887661419 6502779256935433331492129)
                  ·
                    refine ⟨4877084442701574998619097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6502779256935433331492129 4877084442701574998619097)
                    ·
                      refine ⟨3657813332026181248964323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4877084442701574998619097 3657813332026181248964323)
                      ·
                        rfl

theorem cell23_7123566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_7123566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123566 prefixEnd_7123566 := by exact prefixLift 7123566
  have htrace : WordTrace (prefixWord ++ tailWord_7123566) baseStart_7123566 baseEnd_7123566 := by
    simpa [prefixWord, tailWord_7123566, baseEnd_7123566] using wordTrace_append hprefix tailTrace_7123566
  have hstable : (prefixWord ++ tailWord_7123566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123566).length < 2 ^ (prefixWord ++ tailWord_7123566).sum := by decide
  have hdescent : baseEnd_7123566 < baseStart_7123566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123639 : List Nat := [1, 1, 3, 1, 7, 1, 1, 1, 1, 4, 2]
def baseStart_7123639 : Nat := 118140960795 + 7123639 * 2 ^ 59
def prefixEnd_7123639 : Nat := 4983230072969 + 3 ^ 40 * 7123639 * 2
def baseEnd_7123639 : Nat := 3657850816113959463351487

theorem tailTrace_7123639 : CollatzResearch.WordTrace tailWord_7123639 prefixEnd_7123639 3657850816113959463351487 := by
  unfold tailWord_7123639
  simp only [CollatzResearch.WordTrace]
  refine ⟨259820459439279998526189971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173213639626186665684126647 259820459439279998526189971)
  ·
    refine ⟨389730689158919997789284957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259820459439279998526189971 389730689158919997789284957)
    ·
      refine ⟨146149008434594999170981859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389730689158919997789284957 146149008434594999170981859)
      ·
        refine ⟨219223512651892498756472789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146149008434594999170981859 219223512651892498756472789)
        ·
          refine ⟨5138051077778730439604831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 219223512651892498756472789 5138051077778730439604831)
          ·
            refine ⟨7707076616668095659407247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5138051077778730439604831 7707076616668095659407247)
            ·
              refine ⟨11560614925002143489110871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7707076616668095659407247 11560614925002143489110871)
              ·
                refine ⟨17340922387503215233666307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11560614925002143489110871 17340922387503215233666307)
                ·
                  refine ⟨26011383581254822850499461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17340922387503215233666307 26011383581254822850499461)
                  ·
                    refine ⟨4877134421485279284468649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26011383581254822850499461 4877134421485279284468649)
                    ·
                      refine ⟨3657850816113959463351487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4877134421485279284468649 3657850816113959463351487)
                      ·
                        rfl

theorem cell23_7123639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 1, 4, 2].length) (baseStart_7123639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123639 prefixEnd_7123639 := by exact prefixLift 7123639
  have htrace : WordTrace (prefixWord ++ tailWord_7123639) baseStart_7123639 baseEnd_7123639 := by
    simpa [prefixWord, tailWord_7123639, baseEnd_7123639] using wordTrace_append hprefix tailTrace_7123639
  have hstable : (prefixWord ++ tailWord_7123639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123639).length < 2 ^ (prefixWord ++ tailWord_7123639).sum := by decide
  have hdescent : baseEnd_7123639 < baseStart_7123639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123658 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 1, 7]
def baseStart_7123658 : Nat := 118140960795 + 7123658 * 2 ^ 59
def prefixEnd_7123658 : Nat := 4983230072969 + 3 ^ 40 * 7123658 * 2
def baseEnd_7123658 : Nat := 1219286857415464963004633

theorem tailTrace_7123658 : CollatzResearch.WordTrace tailWord_7123658 prefixEnd_7123658 1219286857415464963004633 := by
  unfold tailWord_7123658
  simp only [CollatzResearch.WordTrace]
  refine ⟨64955288106552791192782907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173214101617474109847421085 64955288106552791192782907)
  ·
    refine ⟨97432932159829186789174361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64955288106552791192782907 97432932159829186789174361)
    ·
      refine ⟨73074699119871890091880771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97432932159829186789174361 73074699119871890091880771)
      ·
        refine ⟨109612048679807835137821157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73074699119871890091880771 109612048679807835137821157)
        ·
          refine ⟨20552259127463969088341467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109612048679807835137821157 20552259127463969088341467)
          ·
            refine ⟨30828388691195953632512201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20552259127463969088341467 30828388691195953632512201)
            ·
              refine ⟨23121291518396965224384151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30828388691195953632512201 23121291518396965224384151)
              ·
                refine ⟨34681937277595447836576227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23121291518396965224384151 34681937277595447836576227)
                ·
                  refine ⟨52022905916393171754864341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34681937277595447836576227 52022905916393171754864341)
                  ·
                    refine ⟨1219286857415464963004633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52022905916393171754864341 1219286857415464963004633)
                    ·
                      rfl

theorem cell23_7123658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_7123658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123658 prefixEnd_7123658 := by exact prefixLift 7123658
  have htrace : WordTrace (prefixWord ++ tailWord_7123658) baseStart_7123658 baseEnd_7123658 := by
    simpa [prefixWord, tailWord_7123658, baseEnd_7123658] using wordTrace_append hprefix tailTrace_7123658
  have hstable : (prefixWord ++ tailWord_7123658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123658).length < 2 ^ (prefixWord ++ tailWord_7123658).sum := by decide
  have hdescent : baseEnd_7123658 < baseStart_7123658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123662 : List Nat := [4, 1, 1, 1, 3, 4, 1, 3, 5]
def baseStart_7123662 : Nat := 118140960795 + 7123662 * 2 ^ 59
def prefixEnd_7123662 : Nat := 4983230072969 + 3 ^ 40 * 7123662 * 2
def baseEnd_7123662 : Nat := 406429180685445874818209

theorem tailTrace_7123662 : CollatzResearch.WordTrace tailWord_7123662 prefixEnd_7123662 406429180685445874818209 := by
  unfold tailWord_7123662
  simp only [CollatzResearch.WordTrace]
  refine ⟨32477662289774584181784655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173214198878797782302851493 32477662289774584181784655)
  ·
    refine ⟨48716493434661876272676983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32477662289774584181784655 48716493434661876272676983)
    ·
      refine ⟨73074740151992814409015475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48716493434661876272676983 73074740151992814409015475)
      ·
        refine ⟨109612110227989221613523213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73074740151992814409015475 109612110227989221613523213)
        ·
          refine ⟨41104541335495958105071205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109612110227989221613523213 41104541335495958105071205)
          ·
            refine ⟨7707101500405492144700851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41104541335495958105071205 7707101500405492144700851)
            ·
              refine ⟨11560652250608238217051277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7707101500405492144700851 11560652250608238217051277)
              ·
                refine ⟨4335244593978089331394229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11560652250608238217051277 4335244593978089331394229)
                ·
                  refine ⟨406429180685445874818209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4335244593978089331394229 406429180685445874818209)
                  ·
                    rfl

theorem cell23_7123662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_7123662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123662 prefixEnd_7123662 := by exact prefixLift 7123662
  have htrace : WordTrace (prefixWord ++ tailWord_7123662) baseStart_7123662 baseEnd_7123662 := by
    simpa [prefixWord, tailWord_7123662, baseEnd_7123662] using wordTrace_append hprefix tailTrace_7123662
  have hstable : (prefixWord ++ tailWord_7123662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123662).length < 2 ^ (prefixWord ++ tailWord_7123662).sum := by decide
  have hdescent : baseEnd_7123662 < baseStart_7123662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123722 : List Nat := [3, 1, 2, 2, 1, 2, 2, 5, 1, 4]
def baseStart_7123722 : Nat := 118140960795 + 7123722 * 2 ^ 59
def prefixEnd_7123722 : Nat := 4983230072969 + 3 ^ 40 * 7123722 * 2
def baseEnd_7123722 : Nat := 1219297811669427546204535

theorem tailTrace_7123722 : CollatzResearch.WordTrace tailWord_7123722 prefixEnd_7123722 1219297811669427546204535 := by
  unfold tailWord_7123722
  simp only [CollatzResearch.WordTrace]
  refine ⟨64955871674494825925365355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173215657798652869134307613 64955871674494825925365355)
  ·
    refine ⟨97433807511742238888048033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64955871674494825925365355 97433807511742238888048033)
    ·
      refine ⟨73075355633806679166036025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97433807511742238888048033 73075355633806679166036025)
      ·
        refine ⟨54806516725355009374527019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73075355633806679166036025 54806516725355009374527019)
        ·
          refine ⟨82209775088032514061790529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54806516725355009374527019 82209775088032514061790529)
          ·
            refine ⟨61657331316024385546342897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82209775088032514061790529 61657331316024385546342897)
            ·
              refine ⟨46242998487018289159757173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61657331316024385546342897 46242998487018289159757173)
              ·
                refine ⟨4335281108157964608727235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46242998487018289159757173 4335281108157964608727235)
                ·
                  refine ⟨6502921662236946913090853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4335281108157964608727235 6502921662236946913090853)
                  ·
                    refine ⟨1219297811669427546204535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6502921662236946913090853 1219297811669427546204535)
                    ·
                      rfl

theorem cell23_7123722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_7123722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123722 prefixEnd_7123722 := by exact prefixLift 7123722
  have htrace : WordTrace (prefixWord ++ tailWord_7123722) baseStart_7123722 baseEnd_7123722 := by
    simpa [prefixWord, tailWord_7123722, baseEnd_7123722] using wordTrace_append hprefix tailTrace_7123722
  have hstable : (prefixWord ++ tailWord_7123722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123722).length < 2 ^ (prefixWord ++ tailWord_7123722).sum := by decide
  have hdescent : baseEnd_7123722 < baseStart_7123722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123738 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6]
def baseStart_7123738 : Nat := 118140960795 + 7123738 * 2 ^ 59
def prefixEnd_7123738 : Nat := 4983230072969 + 3 ^ 40 * 7123738 * 2
def baseEnd_7123738 : Nat := 3657901650698754576013531

theorem tailTrace_7123738 : CollatzResearch.WordTrace tailWord_7123738 prefixEnd_7123738 3657901650698754576013531 := by
  unfold tailWord_7123738
  simp only [CollatzResearch.WordTrace]
  refine ⟨64956017566480334608510967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173216046843947558956029245 64956017566480334608510967)
  ·
    refine ⟨97434026349720501912766451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64956017566480334608510967 97434026349720501912766451)
    ·
      refine ⟨146151039524580752869149677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97434026349720501912766451 146151039524580752869149677)
      ·
        refine ⟨54806639821717782325931129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146151039524580752869149677 54806639821717782325931129)
        ·
          refine ⟨41104979866288336744448347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54806639821717782325931129 41104979866288336744448347)
          ·
            refine ⟨61657469799432505116672521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41104979866288336744448347 61657469799432505116672521)
            ·
              refine ⟨46243102349574378837504391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61657469799432505116672521 46243102349574378837504391)
              ·
                refine ⟨69364653524361568256256587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46243102349574378837504391 69364653524361568256256587)
                ·
                  refine ⟨104046980286542352384384881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69364653524361568256256587 104046980286542352384384881)
                  ·
                    refine ⟨78035235214906764288288661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104046980286542352384384881 78035235214906764288288661)
                    ·
                      refine ⟨3657901650698754576013531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78035235214906764288288661 3657901650698754576013531)
                      ·
                        rfl

theorem cell23_7123738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_7123738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123738 prefixEnd_7123738 := by exact prefixLift 7123738
  have htrace : WordTrace (prefixWord ++ tailWord_7123738) baseStart_7123738 baseEnd_7123738 := by
    simpa [prefixWord, tailWord_7123738, baseEnd_7123738] using wordTrace_append hprefix tailTrace_7123738
  have hstable : (prefixWord ++ tailWord_7123738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123738).length < 2 ^ (prefixWord ++ tailWord_7123738).sum := by decide
  have hdescent : baseEnd_7123738 < baseStart_7123738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123755 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 6, 3, 2]
def baseStart_7123755 : Nat := 118140960795 + 7123755 * 2 ^ 59
def prefixEnd_7123755 : Nat := 4983230072969 + 3 ^ 40 * 7123755 * 2
def baseEnd_7123755 : Nat := 3657910379869881009500953

theorem tailTrace_7123755 : CollatzResearch.WordTrace tailWord_7123755 prefixEnd_7123755 3657910379869881009500953 := by
  unfold tailWord_7123755
  simp only [CollatzResearch.WordTrace]
  refine ⟨259824690306859750337412719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173216460204573166891608479 259824690306859750337412719)
  ·
    refine ⟨389737035460289625506119079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259824690306859750337412719 389737035460289625506119079)
    ·
      refine ⟨584605553190434438259178619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389737035460289625506119079 584605553190434438259178619)
      ·
        refine ⟨876908329785651657388767929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584605553190434438259178619 876908329785651657388767929)
        ·
          refine ⟨657681247339238743041575947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 876908329785651657388767929 657681247339238743041575947)
          ·
            refine ⟨986521871008858114562363921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657681247339238743041575947 986521871008858114562363921)
            ·
              refine ⟨739891403256643585921772941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 986521871008858114562363921 739891403256643585921772941)
              ·
                refine ⟨277459276221241344720664853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 739891403256643585921772941 277459276221241344720664853)
                ·
                  refine ⟨13005903572870688033781165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 277459276221241344720664853 13005903572870688033781165)
                  ·
                    refine ⟨4877213839826508012667937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13005903572870688033781165 4877213839826508012667937)
                    ·
                      refine ⟨3657910379869881009500953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4877213839826508012667937 3657910379869881009500953)
                      ·
                        rfl

theorem cell23_7123755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 3, 2].length) (baseStart_7123755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123755 prefixEnd_7123755 := by exact prefixLift 7123755
  have htrace : WordTrace (prefixWord ++ tailWord_7123755) baseStart_7123755 baseEnd_7123755 := by
    simpa [prefixWord, tailWord_7123755, baseEnd_7123755] using wordTrace_append hprefix tailTrace_7123755
  have hstable : (prefixWord ++ tailWord_7123755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123755).length < 2 ^ (prefixWord ++ tailWord_7123755).sum := by decide
  have hdescent : baseEnd_7123755 < baseStart_7123755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123762 : List Nat := [3, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3]
def baseStart_7123762 : Nat := 118140960795 + 7123762 * 2 ^ 59
def prefixEnd_7123762 : Nat := 4983230072969 + 3 ^ 40 * 7123762 * 2
def baseEnd_7123762 : Nat := 3657913974234462482113421

theorem tailTrace_7123762 : CollatzResearch.WordTrace tailWord_7123762 prefixEnd_7123762 3657913974234462482113421 := by
  unfold tailWord_7123762
  simp only [CollatzResearch.WordTrace]
  refine ⟨64956236404458597633229385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173216630411889593688611693 64956236404458597633229385)
  ·
    refine ⟨48717177303343948224922039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64956236404458597633229385 48717177303343948224922039)
    ·
      refine ⟨73075765955015922337383059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48717177303343948224922039 73075765955015922337383059)
      ·
        refine ⟨109613648932523883506074589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73075765955015922337383059 109613648932523883506074589)
        ·
          refine ⟨41105118349696456314777971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109613648932523883506074589 41105118349696456314777971)
          ·
            refine ⟨61657677524544684472166957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41105118349696456314777971 61657677524544684472166957)
            ·
              refine ⟨23121629071704256677062609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61657677524544684472166957 23121629071704256677062609)
              ·
                refine ⟨17341221803778192507796957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23121629071704256677062609 17341221803778192507796957)
                ·
                  refine ⟨6502958176416822190423859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17341221803778192507796957 6502958176416822190423859)
                  ·
                    refine ⟨9754437264625233285635789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6502958176416822190423859 9754437264625233285635789)
                    ·
                      refine ⟨3657913974234462482113421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9754437264625233285635789 3657913974234462482113421)
                      ·
                        rfl

theorem cell23_7123762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_7123762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123762 prefixEnd_7123762 := by exact prefixLift 7123762
  have htrace : WordTrace (prefixWord ++ tailWord_7123762) baseStart_7123762 baseEnd_7123762 := by
    simpa [prefixWord, tailWord_7123762, baseEnd_7123762] using wordTrace_append hprefix tailTrace_7123762
  have hstable : (prefixWord ++ tailWord_7123762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123762).length < 2 ^ (prefixWord ++ tailWord_7123762).sum := by decide
  have hdescent : baseEnd_7123762 < baseStart_7123762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123765 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 3, 5]
def baseStart_7123765 : Nat := 118140960795 + 7123765 * 2 ^ 59
def prefixEnd_7123765 : Nat := 4983230072969 + 3 ^ 40 * 7123765 * 2
def baseEnd_7123765 : Nat := 1219305171558808656791969

theorem tailTrace_7123765 : CollatzResearch.WordTrace tailWord_7123765 prefixEnd_7123765 1219305171558808656791969 := by
  unfold tailWord_7123765
  simp only [CollatzResearch.WordTrace]
  refine ⟨259825055036823522045276749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173216703357882348030184499 259825055036823522045276749)
  ·
    refine ⟨97434395638808820766978781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259825055036823522045276749 97434395638808820766978781)
    ·
      refine ⟨36537898364553307787617043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97434395638808820766978781 36537898364553307787617043)
      ·
        refine ⟨54806847546829961681425565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36537898364553307787617043 54806847546829961681425565)
        ·
          refine ⟨20552567830061235630534587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54806847546829961681425565 20552567830061235630534587)
          ·
            refine ⟨30828851745091853445801881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20552567830061235630534587 30828851745091853445801881)
            ·
              refine ⟨23121638808818890084351411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30828851745091853445801881 23121638808818890084351411)
              ·
                refine ⟨34682458213228335126527117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23121638808818890084351411 34682458213228335126527117)
                ·
                  refine ⟨13005921829960625672447669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34682458213228335126527117 13005921829960625672447669)
                  ·
                    refine ⟨1219305171558808656791969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13005921829960625672447669 1219305171558808656791969)
                    ·
                      rfl

theorem cell23_7123765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_7123765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123765 prefixEnd_7123765 := by exact prefixLift 7123765
  have htrace : WordTrace (prefixWord ++ tailWord_7123765) baseStart_7123765 baseEnd_7123765 := by
    simpa [prefixWord, tailWord_7123765, baseEnd_7123765] using wordTrace_append hprefix tailTrace_7123765
  have hstable : (prefixWord ++ tailWord_7123765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123765).length < 2 ^ (prefixWord ++ tailWord_7123765).sum := by decide
  have hdescent : baseEnd_7123765 < baseStart_7123765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123766 : List Nat := [5, 1, 2, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_7123766 : Nat := 118140960795 + 7123766 * 2 ^ 59
def prefixEnd_7123766 : Nat := 4983230072969 + 3 ^ 40 * 7123766 * 2
def baseEnd_7123766 : Nat := 3657916028157080466463403

theorem tailTrace_7123766 : CollatzResearch.WordTrace tailWord_7123766 prefixEnd_7123766 3657916028157080466463403 := by
  unfold tailWord_7123766
  simp only [CollatzResearch.WordTrace]
  refine ⟨16239068219363743701003947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173216727673213266144042101 16239068219363743701003947)
  ·
    refine ⟨24358602329045615551505921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16239068219363743701003947 24358602329045615551505921)
    ·
      refine ⟨18268951746784211663629441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24358602329045615551505921 18268951746784211663629441)
      ·
        refine ⟨13701713810088158747722081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18268951746784211663629441 13701713810088158747722081)
        ·
          refine ⟨10276285357566119060791561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13701713810088158747722081 10276285357566119060791561)
          ·
            refine ⟨7707214018174589295593671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10276285357566119060791561 7707214018174589295593671)
            ·
              refine ⟨11560821027261883943390507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7707214018174589295593671 11560821027261883943390507)
              ·
                refine ⟨17341231540892825915085761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11560821027261883943390507 17341231540892825915085761)
                ·
                  refine ⟨13005923655669619436314321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17341231540892825915085761 13005923655669619436314321)
                  ·
                    refine ⟨9754442741752214577235741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13005923655669619436314321 9754442741752214577235741)
                    ·
                      refine ⟨3657916028157080466463403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9754442741752214577235741 3657916028157080466463403)
                      ·
                        rfl

theorem cell23_7123766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_7123766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123766 prefixEnd_7123766 := by exact prefixLift 7123766
  have htrace : WordTrace (prefixWord ++ tailWord_7123766) baseStart_7123766 baseEnd_7123766 := by
    simpa [prefixWord, tailWord_7123766, baseEnd_7123766] using wordTrace_append hprefix tailTrace_7123766
  have hstable : (prefixWord ++ tailWord_7123766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123766).length < 2 ^ (prefixWord ++ tailWord_7123766).sum := by decide
  have hdescent : baseEnd_7123766 < baseStart_7123766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123779 : List Nat := [1, 1, 1, 3, 1, 4, 4, 3, 1, 1, 3]
def baseStart_7123779 : Nat := 118140960795 + 7123779 * 2 ^ 59
def prefixEnd_7123779 : Nat := 4983230072969 + 3 ^ 40 * 7123779 * 2
def baseEnd_7123779 : Nat := 3657922703405588915600843

theorem tailTrace_7123779 : CollatzResearch.WordTrace tailWord_7123779 prefixEnd_7123779 3657922703405588915600843 := by
  unfold tailWord_7123779
  simp only [CollatzResearch.WordTrace]
  refine ⟨259825565658772802436286391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173217043772515201624190927 259825565658772802436286391)
  ·
    refine ⟨389738348488159203654429587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259825565658772802436286391 389738348488159203654429587)
    ·
      refine ⟨584607522732238805481644381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389738348488159203654429587 584607522732238805481644381)
      ·
        refine ⟨219227821024589552055616643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 584607522732238805481644381 219227821024589552055616643)
        ·
          refine ⟨328841731536884328083424965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219227821024589552055616643 328841731536884328083424965)
          ·
            refine ⟨61657824663165811515642181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 328841731536884328083424965 61657824663165811515642181)
            ·
              refine ⟨11560842124343589659182909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61657824663165811515642181 11560842124343589659182909)
              ·
                refine ⟨4335315796628846122193591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11560842124343589659182909 4335315796628846122193591)
                ·
                  refine ⟨6502973694943269183290387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4335315796628846122193591 6502973694943269183290387)
                  ·
                    refine ⟨9754460542414903774935581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6502973694943269183290387 9754460542414903774935581)
                    ·
                      refine ⟨3657922703405588915600843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9754460542414903774935581 3657922703405588915600843)
                      ·
                        rfl

theorem cell23_7123779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 1, 1, 3].length) (baseStart_7123779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123779 prefixEnd_7123779 := by exact prefixLift 7123779
  have htrace : WordTrace (prefixWord ++ tailWord_7123779) baseStart_7123779 baseEnd_7123779 := by
    simpa [prefixWord, tailWord_7123779, baseEnd_7123779] using wordTrace_append hprefix tailTrace_7123779
  have hstable : (prefixWord ++ tailWord_7123779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123779).length < 2 ^ (prefixWord ++ tailWord_7123779).sum := by decide
  have hdescent : baseEnd_7123779 < baseStart_7123779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123808 : List Nat := [2, 1, 1, 3, 3, 1, 2, 10]
def baseStart_7123808 : Nat := 118140960795 + 7123808 * 2 ^ 59
def prefixEnd_7123808 : Nat := 4983230072969 + 3 ^ 40 * 7123808 * 2
def baseEnd_7123808 : Nat := 135479170160909974153267

theorem tailTrace_7123808 : CollatzResearch.WordTrace tailWord_7123808 prefixEnd_7123808 135479170160909974153267 := by
  unfold tailWord_7123808
  simp only [CollatzResearch.WordTrace]
  refine ⟨129913311687833870194546039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173217748917111826926061385 129913311687833870194546039)
  ·
    refine ⟨194869967531750805291819059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129913311687833870194546039 194869967531750805291819059)
    ·
      refine ⟨292304951297626207937728589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194869967531750805291819059 292304951297626207937728589)
      ·
        refine ⟨109614356736609827976648221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292304951297626207937728589 109614356736609827976648221)
        ·
          refine ⟨41105383776228685491243083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109614356736609827976648221 41105383776228685491243083)
          ·
            refine ⟨61658075664343028236864625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41105383776228685491243083 61658075664343028236864625)
            ·
              refine ⟨46243556748257271177648469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61658075664343028236864625 46243556748257271177648469)
              ·
                refine ⟨135479170160909974153267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46243556748257271177648469 135479170160909974153267)
                ·
                  rfl

theorem cell23_7123808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 10].length) (baseStart_7123808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123808 prefixEnd_7123808 := by exact prefixLift 7123808
  have htrace : WordTrace (prefixWord ++ tailWord_7123808) baseStart_7123808 baseEnd_7123808 := by
    simpa [prefixWord, tailWord_7123808, baseEnd_7123808] using wordTrace_append hprefix tailTrace_7123808
  have hstable : (prefixWord ++ tailWord_7123808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123808).length < 2 ^ (prefixWord ++ tailWord_7123808).sum := by decide
  have hdescent : baseEnd_7123808 < baseStart_7123808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123812 : List Nat := [2, 3, 1, 1, 4, 3, 1, 1, 1, 6]
def baseStart_7123812 : Nat := 118140960795 + 7123812 * 2 ^ 59
def prefixEnd_7123812 : Nat := 4983230072969 + 3 ^ 40 * 7123812 * 2
def baseEnd_7123812 : Nat := 1219313216089062428829397

theorem tailTrace_7123812 : CollatzResearch.WordTrace tailWord_7123812 prefixEnd_7123812 1219313216089062428829397 := by
  unfold tailWord_7123812
  simp only [CollatzResearch.WordTrace]
  refine ⟨129913384633826624536118845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173217846178435499381491793 129913384633826624536118845)
  ·
    refine ⟨48717519237684984201044567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129913384633826624536118845 48717519237684984201044567)
    ·
      refine ⟨73076278856527476301566851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48717519237684984201044567 73076278856527476301566851)
      ·
        refine ⟨109614418284791214452350277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73076278856527476301566851 109614418284791214452350277)
        ·
          refine ⟨20552703428398352709815677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109614418284791214452350277 20552703428398352709815677)
          ·
            refine ⟨7707263785649382266180879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20552703428398352709815677 7707263785649382266180879)
            ·
              refine ⟨11560895678474073399271319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7707263785649382266180879 11560895678474073399271319)
              ·
                refine ⟨17341343517711110098906979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11560895678474073399271319 17341343517711110098906979)
                ·
                  refine ⟨26012015276566665148360469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17341343517711110098906979 26012015276566665148360469)
                  ·
                    refine ⟨1219313216089062428829397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26012015276566665148360469 1219313216089062428829397)
                    ·
                      rfl

theorem cell23_7123812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_7123812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123812 prefixEnd_7123812 := by exact prefixLift 7123812
  have htrace : WordTrace (prefixWord ++ tailWord_7123812) baseStart_7123812 baseEnd_7123812 := by
    simpa [prefixWord, tailWord_7123812, baseEnd_7123812] using wordTrace_append hprefix tailTrace_7123812
  have hstable : (prefixWord ++ tailWord_7123812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123812).length < 2 ^ (prefixWord ++ tailWord_7123812).sum := by decide
  have hdescent : baseEnd_7123812 < baseStart_7123812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123815 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_7123815 : Nat := 118140960795 + 7123815 * 2 ^ 59
def prefixEnd_7123815 : Nat := 4983230072969 + 3 ^ 40 * 7123815 * 2
def baseEnd_7123815 : Nat := 3657941188709150774750677

theorem tailTrace_7123815 : CollatzResearch.WordTrace tailWord_7123815 prefixEnd_7123815 3657941188709150774750677 := by
  unfold tailWord_7123815
  simp only [CollatzResearch.WordTrace]
  refine ⟨259826878686642380584596899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173217919124428253723064599 259826878686642380584596899)
  ·
    refine ⟨389740318029963570876895349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259826878686642380584596899 389740318029963570876895349)
    ·
      refine ⟨36538154815309084769708939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 389740318029963570876895349 36538154815309084769708939)
      ·
        refine ⟨54807232222963627154563409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36538154815309084769708939 54807232222963627154563409)
        ·
          refine ⟨41105424167222720365922557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54807232222963627154563409 41105424167222720365922557)
          ·
            refine ⟨15414534062708520137220959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41105424167222720365922557 15414534062708520137220959)
            ·
              refine ⟨23121801094062780205831439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15414534062708520137220959 23121801094062780205831439)
              ·
                refine ⟨34682701641094170308747159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23121801094062780205831439 34682701641094170308747159)
                ·
                  refine ⟨52024052461641255463120739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34682701641094170308747159 52024052461641255463120739)
                  ·
                    refine ⟨78036078692461883194681109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52024052461641255463120739 78036078692461883194681109)
                    ·
                      refine ⟨3657941188709150774750677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78036078692461883194681109 3657941188709150774750677)
                      ·
                        rfl

theorem cell23_7123815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_7123815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123815 prefixEnd_7123815 := by exact prefixLift 7123815
  have htrace : WordTrace (prefixWord ++ tailWord_7123815) baseStart_7123815 baseEnd_7123815 := by
    simpa [prefixWord, tailWord_7123815, baseEnd_7123815] using wordTrace_append hprefix tailTrace_7123815
  have hstable : (prefixWord ++ tailWord_7123815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123815).length < 2 ^ (prefixWord ++ tailWord_7123815).sum := by decide
  have hdescent : baseEnd_7123815 < baseStart_7123815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123825 : List Nat := [1, 2, 2, 2, 1, 4, 4, 7]
def baseStart_7123825 : Nat := 118140960795 + 7123825 * 2 ^ 59
def prefixEnd_7123825 : Nat := 4983230072969 + 3 ^ 40 * 7123825 * 2
def baseEnd_7123825 : Nat := 135479493463544286504653

theorem tailTrace_7123825 : CollatzResearch.WordTrace tailWord_7123825 prefixEnd_7123825 135479493463544286504653 := by
  unfold tailWord_7123825
  simp only [CollatzResearch.WordTrace]
  refine ⟨259827243416606152292460929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173218162277737434861640619 259827243416606152292460929)
  ·
    refine ⟨194870432562454614219345697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259827243416606152292460929 194870432562454614219345697)
    ·
      refine ⟨146152824421840960664509273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194870432562454614219345697 146152824421840960664509273)
      ·
        refine ⟨109614618316380720498381955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146152824421840960664509273 109614618316380720498381955)
        ·
          refine ⟨164421927474571080747572933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109614618316380720498381955 164421927474571080747572933)
          ·
            refine ⟨30829111401482077640169925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164421927474571080747572933 30829111401482077640169925)
            ·
              refine ⟨5780458387777889557531861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30829111401482077640169925 5780458387777889557531861)
              ·
                refine ⟨135479493463544286504653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5780458387777889557531861 135479493463544286504653)
                ·
                  rfl

theorem cell23_7123825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 7].length) (baseStart_7123825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123825 prefixEnd_7123825 := by exact prefixLift 7123825
  have htrace : WordTrace (prefixWord ++ tailWord_7123825) baseStart_7123825 baseEnd_7123825 := by
    simpa [prefixWord, tailWord_7123825, baseEnd_7123825] using wordTrace_append hprefix tailTrace_7123825
  have hstable : (prefixWord ++ tailWord_7123825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123825).length < 2 ^ (prefixWord ++ tailWord_7123825).sum := by decide
  have hdescent : baseEnd_7123825 < baseStart_7123825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123835 : List Nat := [1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 3]
def baseStart_7123835 : Nat := 118140960795 + 7123835 * 2 ^ 59
def prefixEnd_7123835 : Nat := 4983230072969 + 3 ^ 40 * 7123835 * 2
def baseEnd_7123835 : Nat := 3657951458322240696500585

theorem tailTrace_7123835 : CollatzResearch.WordTrace tailWord_7123835 prefixEnd_7123835 3657951458322240696500585 := by
  unfold tailWord_7123835
  simp only [CollatzResearch.WordTrace]
  refine ⟨259827608146569924000324959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173218405431046616000216639 259827608146569924000324959)
  ·
    refine ⟨389741412219854886000487439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259827608146569924000324959 389741412219854886000487439)
    ·
      refine ⟨584612118329782329000731159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389741412219854886000487439 584612118329782329000731159)
      ·
        refine ⟨876918177494673493501096739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584612118329782329000731159 876918177494673493501096739)
        ·
          refine ⟨1315377266242010240251645109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876918177494673493501096739 1315377266242010240251645109)
          ·
            refine ⟨123316618710188460023591729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1315377266242010240251645109 123316618710188460023591729)
            ·
              refine ⟨92487464032641345017693797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123316618710188460023591729 92487464032641345017693797)
              ·
                refine ⟨17341399506120252190817587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92487464032641345017693797 17341399506120252190817587)
                ·
                  refine ⟨26012099259180378286226381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17341399506120252190817587 26012099259180378286226381)
                  ·
                    refine ⟨9754537222192641857334893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26012099259180378286226381 9754537222192641857334893)
                    ·
                      refine ⟨3657951458322240696500585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9754537222192641857334893 3657951458322240696500585)
                      ·
                        rfl

theorem cell23_7123835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 3].length) (baseStart_7123835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123835 prefixEnd_7123835 := by exact prefixLift 7123835
  have htrace : WordTrace (prefixWord ++ tailWord_7123835) baseStart_7123835 baseEnd_7123835 := by
    simpa [prefixWord, tailWord_7123835, baseEnd_7123835] using wordTrace_append hprefix tailTrace_7123835
  have hstable : (prefixWord ++ tailWord_7123835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123835).length < 2 ^ (prefixWord ++ tailWord_7123835).sum := by decide
  have hdescent : baseEnd_7123835 < baseStart_7123835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123852 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 4, 1, 3]
def baseStart_7123852 : Nat := 118140960795 + 7123852 * 2 ^ 59
def prefixEnd_7123852 : Nat := 4983230072969 + 3 ^ 40 * 7123852 * 2
def baseEnd_7123852 : Nat := 3657960187493367129988007

theorem tailTrace_7123852 : CollatzResearch.WordTrace tailWord_7123852 prefixEnd_7123852 3657960187493367129988007 := by
  unfold tailWord_7123852
  simp only [CollatzResearch.WordTrace]
  refine ⟨129914114093754167951846905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173218818791672223935795873 129914114093754167951846905)
  ·
    refine ⟨97435585570315625963885179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129914114093754167951846905 97435585570315625963885179)
    ·
      refine ⟨146153378355473438945827769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97435585570315625963885179 146153378355473438945827769)
      ·
        refine ⟨109615033766605079209370827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146153378355473438945827769 109615033766605079209370827)
        ·
          refine ⟨164422550649907618814056241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109615033766605079209370827 164422550649907618814056241)
          ·
            refine ⟨123316912987430714110542181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164422550649907618814056241 123316912987430714110542181)
            ·
              refine ⟨23121921185143258895726659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123316912987430714110542181 23121921185143258895726659)
              ·
                refine ⟨34682881777714888343589989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23121921185143258895726659 34682881777714888343589989)
                ·
                  refine ⟨6503040333321541564423123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34682881777714888343589989 6503040333321541564423123)
                  ·
                    refine ⟨9754560499982312346634685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6503040333321541564423123 9754560499982312346634685)
                    ·
                      refine ⟨3657960187493367129988007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9754560499982312346634685 3657960187493367129988007)
                      ·
                        rfl

theorem cell23_7123852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_7123852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123852 prefixEnd_7123852 := by exact prefixLift 7123852
  have htrace : WordTrace (prefixWord ++ tailWord_7123852) baseStart_7123852 baseEnd_7123852 := by
    simpa [prefixWord, tailWord_7123852, baseEnd_7123852] using wordTrace_append hprefix tailTrace_7123852
  have hstable : (prefixWord ++ tailWord_7123852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123852).length < 2 ^ (prefixWord ++ tailWord_7123852).sum := by decide
  have hdescent : baseEnd_7123852 < baseStart_7123852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123869 : List Nat := [1, 4, 2, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_7123869 : Nat := 118140960795 + 7123869 * 2 ^ 59
def prefixEnd_7123869 : Nat := 4983230072969 + 3 ^ 40 * 7123869 * 2
def baseEnd_7123869 : Nat := 3657968916664493563475429

theorem tailTrace_7123869 : CollatzResearch.WordTrace tailWord_7123869 prefixEnd_7123869 3657968916664493563475429 := by
  unfold tailWord_7123869
  simp only [CollatzResearch.WordTrace]
  refine ⟨259828848228446747807062661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173219232152297831871375107 259828848228446747807062661)
  ·
    refine ⟨48717909042833765213824249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259828848228446747807062661 48717909042833765213824249)
    ·
      refine ⟨36538431782125323910368187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48717909042833765213824249 36538431782125323910368187)
      ·
        refine ⟨54807647673187985865552281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36538431782125323910368187 54807647673187985865552281)
        ·
          refine ⟨41105735754890989399164211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54807647673187985865552281 41105735754890989399164211)
          ·
            refine ⟨61658603632336484098746317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41105735754890989399164211 61658603632336484098746317)
            ·
              refine ⟨23121976362126181537029869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61658603632336484098746317 23121976362126181537029869)
              ·
                refine ⟨8670741135797318076386201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23121976362126181537029869 8670741135797318076386201)
                ·
                  refine ⟨6503055851847988557289651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8670741135797318076386201 6503055851847988557289651)
                  ·
                    refine ⟨9754583777771982835934477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6503055851847988557289651 9754583777771982835934477)
                    ·
                      refine ⟨3657968916664493563475429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9754583777771982835934477 3657968916664493563475429)
                      ·
                        rfl

theorem cell23_7123869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_7123869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123869 prefixEnd_7123869 := by exact prefixLift 7123869
  have htrace : WordTrace (prefixWord ++ tailWord_7123869) baseStart_7123869 baseEnd_7123869 := by
    simpa [prefixWord, tailWord_7123869, baseEnd_7123869] using wordTrace_append hprefix tailTrace_7123869
  have hstable : (prefixWord ++ tailWord_7123869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123869).length < 2 ^ (prefixWord ++ tailWord_7123869).sum := by decide
  have hdescent : baseEnd_7123869 < baseStart_7123869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123895 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 5]
def baseStart_7123895 : Nat := 118140960795 + 7123895 * 2 ^ 59
def prefixEnd_7123895 : Nat := 4983230072969 + 3 ^ 40 * 7123895 * 2
def baseEnd_7123895 : Nat := 3657982267161510461750309

theorem tailTrace_7123895 : CollatzResearch.WordTrace tailWord_7123895 prefixEnd_7123895 3657982267161510461750309 := by
  unfold tailWord_7123895
  simp only [CollatzResearch.WordTrace]
  refine ⟨259829796526352554247509139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173219864350901702831672759 259829796526352554247509139)
  ·
    refine ⟨389744694789528831371263709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259829796526352554247509139 389744694789528831371263709)
    ·
      refine ⟨146154260546073311764223891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389744694789528831371263709 146154260546073311764223891)
      ·
        refine ⟨219231390819109967646335837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146154260546073311764223891 219231390819109967646335837)
        ·
          refine ⟨82211771557166237867375939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219231390819109967646335837 82211771557166237867375939)
          ·
            refine ⟨123317657335749356801063909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82211771557166237867375939 123317657335749356801063909)
            ·
              refine ⟨23122060750453004400199483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123317657335749356801063909 23122060750453004400199483)
              ·
                refine ⟨34683091125679506600299225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23122060750453004400199483 34683091125679506600299225)
                ·
                  refine ⟨26012318344259629950224419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34683091125679506600299225 26012318344259629950224419)
                  ·
                    refine ⟨39018477516389444925336629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26012318344259629950224419 39018477516389444925336629)
                    ·
                      refine ⟨3657982267161510461750309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39018477516389444925336629 3657982267161510461750309)
                      ·
                        rfl

theorem cell23_7123895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_7123895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123895 prefixEnd_7123895 := by exact prefixLift 7123895
  have htrace : WordTrace (prefixWord ++ tailWord_7123895) baseStart_7123895 baseEnd_7123895 := by
    simpa [prefixWord, tailWord_7123895, baseEnd_7123895] using wordTrace_append hprefix tailTrace_7123895
  have hstable : (prefixWord ++ tailWord_7123895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123895).length < 2 ^ (prefixWord ++ tailWord_7123895).sum := by decide
  have hdescent : baseEnd_7123895 < baseStart_7123895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123896 : List Nat := [2, 1, 2, 1, 2, 5, 3, 1, 1, 3, 2]
def baseStart_7123896 : Nat := 118140960795 + 7123896 * 2 ^ 59
def prefixEnd_7123896 : Nat := 4983230072969 + 3 ^ 40 * 7123896 * 2
def baseEnd_7123896 : Nat := 3657982780642164957837805

theorem tailTrace_7123896 : CollatzResearch.WordTrace tailWord_7123896 prefixEnd_7123896 3657982780642164957837805 := by
  unfold tailWord_7123896
  simp only [CollatzResearch.WordTrace]
  refine ⟨129914916499674465709147771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173219888666232620945530361 129914916499674465709147771)
  ·
    refine ⟨194872374749511698563721657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129914916499674465709147771 194872374749511698563721657)
    ·
      refine ⟨146154281062133773922791243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194872374749511698563721657 146154281062133773922791243)
      ·
        refine ⟨219231421593200660884186865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146154281062133773922791243 219231421593200660884186865)
        ·
          refine ⟨164423566194900495663140149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219231421593200660884186865 164423566194900495663140149)
          ·
            refine ⟨15414709330771921468419389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164423566194900495663140149 15414709330771921468419389)
            ·
              refine ⟨5780515999039470550657271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15414709330771921468419389 5780515999039470550657271)
              ·
                refine ⟨8670773998559205825985907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5780515999039470550657271 8670773998559205825985907)
                ·
                  refine ⟨13006160997838808738978861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8670773998559205825985907 13006160997838808738978861)
                  ·
                    refine ⟨4877310374189553277117073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13006160997838808738978861 4877310374189553277117073)
                    ·
                      refine ⟨3657982780642164957837805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4877310374189553277117073 3657982780642164957837805)
                      ·
                        rfl

theorem cell23_7123896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 1, 3, 2].length) (baseStart_7123896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123896 prefixEnd_7123896 := by exact prefixLift 7123896
  have htrace : WordTrace (prefixWord ++ tailWord_7123896) baseStart_7123896 baseEnd_7123896 := by
    simpa [prefixWord, tailWord_7123896, baseEnd_7123896] using wordTrace_append hprefix tailTrace_7123896
  have hstable : (prefixWord ++ tailWord_7123896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123896).length < 2 ^ (prefixWord ++ tailWord_7123896).sum := by decide
  have hdescent : baseEnd_7123896 < baseStart_7123896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123910 : List Nat := [6, 1, 3, 1, 2, 1, 1, 8]
def baseStart_7123910 : Nat := 118140960795 + 7123910 * 2 ^ 59
def prefixEnd_7123910 : Nat := 4983230072969 + 3 ^ 40 * 7123910 * 2
def baseEnd_7123910 : Nat := 135481109976715848261583

theorem tailTrace_7123910 : CollatzResearch.WordTrace tailWord_7123910 prefixEnd_7123910 135481109976715848261583 := by
  unfold tailWord_7123910
  simp only [CollatzResearch.WordTrace]
  refine ⟨8119698238165569119040787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 173220229080865474539536789 8119698238165569119040787)
  ·
    refine ⟨12179547357248353678561181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8119698238165569119040787 12179547357248353678561181)
    ·
      refine ⟨4567330258968132629460443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12179547357248353678561181 4567330258968132629460443)
      ·
        refine ⟨6850995388452198944190665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4567330258968132629460443 6850995388452198944190665)
        ·
          refine ⟨5138246541339149208142999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6850995388452198944190665 5138246541339149208142999)
          ·
            refine ⟨7707369812008723812214499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5138246541339149208142999 7707369812008723812214499)
            ·
              refine ⟨11561054718013085718321749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7707369812008723812214499 11561054718013085718321749)
              ·
                refine ⟨135481109976715848261583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11561054718013085718321749 135481109976715848261583)
                ·
                  rfl

theorem cell23_7123910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_7123910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123910 prefixEnd_7123910 := by exact prefixLift 7123910
  have htrace : WordTrace (prefixWord ++ tailWord_7123910) baseStart_7123910 baseEnd_7123910 := by
    simpa [prefixWord, tailWord_7123910, baseEnd_7123910] using wordTrace_append hprefix tailTrace_7123910
  have hstable : (prefixWord ++ tailWord_7123910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123910).length < 2 ^ (prefixWord ++ tailWord_7123910).sum := by decide
  have hdescent : baseEnd_7123910 < baseStart_7123910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123922 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_7123922 : Nat := 118140960795 + 7123922 * 2 ^ 59
def prefixEnd_7123922 : Nat := 4983230072969 + 3 ^ 40 * 7123922 * 2
def baseEnd_7123922 : Nat := 3657996131139181856112685

theorem tailTrace_7123922 : CollatzResearch.WordTrace tailWord_7123922 prefixEnd_7123922 3657996131139181856112685 := by
  unfold tailWord_7123922
  simp only [CollatzResearch.WordTrace]
  refine ⟨64957695324313684464685505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173220520864836491905828013 64957695324313684464685505)
  ·
    refine ⟨48718271493235263348514129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64957695324313684464685505 48718271493235263348514129)
    ·
      refine ⟨36538703619926447511385597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48718271493235263348514129 36538703619926447511385597)
      ·
        refine ⟨13702013857472417816769599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36538703619926447511385597 13702013857472417816769599)
        ·
          refine ⟨20553020786208626725154399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13702013857472417816769599 20553020786208626725154399)
          ·
            refine ⟨30829531179312940087731599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20553020786208626725154399 30829531179312940087731599)
            ·
              refine ⟨46244296768969410131597399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30829531179312940087731599 46244296768969410131597399)
              ·
                refine ⟨69366445153454115197396099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46244296768969410131597399 69366445153454115197396099)
                ·
                  refine ⟨104049667730181172796094149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69366445153454115197396099 104049667730181172796094149)
                  ·
                    refine ⟨19509312699408969899267653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104049667730181172796094149 19509312699408969899267653)
                    ·
                      refine ⟨3657996131139181856112685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19509312699408969899267653 3657996131139181856112685)
                      ·
                        rfl

theorem cell23_7123922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_7123922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123922 prefixEnd_7123922 := by exact prefixLift 7123922
  have htrace : WordTrace (prefixWord ++ tailWord_7123922) baseStart_7123922 baseEnd_7123922 := by
    simpa [prefixWord, tailWord_7123922, baseEnd_7123922] using wordTrace_append hprefix tailTrace_7123922
  have hstable : (prefixWord ++ tailWord_7123922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123922).length < 2 ^ (prefixWord ++ tailWord_7123922).sum := by decide
  have hdescent : baseEnd_7123922 < baseStart_7123922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123926 : List Nat := [5, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_7123926 : Nat := 118140960795 + 7123926 * 2 ^ 59
def prefixEnd_7123926 : Nat := 4983230072969 + 3 ^ 40 * 7123926 * 2
def baseEnd_7123926 : Nat := 3657998185061799840462667

theorem tailTrace_7123926 : CollatzResearch.WordTrace tailWord_7123926 prefixEnd_7123926 3657998185061799840462667 := by
  unfold tailWord_7123926
  simp only [CollatzResearch.WordTrace]
  refine ⟨16239432949327515408867977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173220618126160164361258421 16239432949327515408867977)
  ·
    refine ⟨12179574711995636556650983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16239432949327515408867977 12179574711995636556650983)
    ·
      refine ⟨18269362067993454834976475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12179574711995636556650983 18269362067993454834976475)
      ·
        refine ⟨27404043101990182252464713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18269362067993454834976475 27404043101990182252464713)
        ·
          refine ⟨20553032326492636689348535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27404043101990182252464713 20553032326492636689348535)
          ·
            refine ⟨30829548489738955034022803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20553032326492636689348535 30829548489738955034022803)
            ·
              refine ⟨46244322734608432551034205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30829548489738955034022803 46244322734608432551034205)
              ·
                refine ⟨17341621025478162206637827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46244322734608432551034205 17341621025478162206637827)
                ·
                  refine ⟨26012431538217243309956741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17341621025478162206637827 26012431538217243309956741)
                  ·
                    refine ⟨4877330913415733120616889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26012431538217243309956741 4877330913415733120616889)
                    ·
                      refine ⟨3657998185061799840462667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4877330913415733120616889 3657998185061799840462667)
                      ·
                        rfl

theorem cell23_7123926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_7123926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123926 prefixEnd_7123926 := by exact prefixLift 7123926
  have htrace : WordTrace (prefixWord ++ tailWord_7123926) baseStart_7123926 baseEnd_7123926 := by
    simpa [prefixWord, tailWord_7123926, baseEnd_7123926] using wordTrace_append hprefix tailTrace_7123926
  have hstable : (prefixWord ++ tailWord_7123926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123926).length < 2 ^ (prefixWord ++ tailWord_7123926).sum := by decide
  have hdescent : baseEnd_7123926 < baseStart_7123926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7123982 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_7123982 : Nat := 118140960795 + 7123982 * 2 ^ 59
def prefixEnd_7123982 : Nat := 4983230072969 + 3 ^ 40 * 7123982 * 2
def baseEnd_7123982 : Nat := 3658026939978451621362409

theorem tailTrace_7123982 : CollatzResearch.WordTrace tailWord_7123982 prefixEnd_7123982 3658026939978451621362409 := by
  unfold tailWord_7123982
  simp only [CollatzResearch.WordTrace]
  refine ⟨32479121209629671013240775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173221979784691578737284133 32479121209629671013240775)
  ·
    refine ⟨48718681814444506519861163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32479121209629671013240775 48718681814444506519861163)
    ·
      refine ⟨73078022721666759779791745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48718681814444506519861163 73078022721666759779791745)
      ·
        refine ⟨54808517041250069834843809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73078022721666759779791745 54808517041250069834843809)
        ·
          refine ⟨41106387780937552376132857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54808517041250069834843809 41106387780937552376132857)
          ·
            refine ⟨30829790835703164282099643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41106387780937552376132857 30829790835703164282099643)
            ·
              refine ⟨46244686253554746423149465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30829790835703164282099643 46244686253554746423149465)
              ·
                refine ⟨34683514690166059817362099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46244686253554746423149465 34683514690166059817362099)
                ·
                  refine ⟨52025272035249089726043149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34683514690166059817362099 52025272035249089726043149)
                  ·
                    refine ⟨19509477013218408647266181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52025272035249089726043149 19509477013218408647266181)
                    ·
                      refine ⟨3658026939978451621362409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19509477013218408647266181 3658026939978451621362409)
                      ·
                        rfl

theorem cell23_7123982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_7123982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7123982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7123982 prefixEnd_7123982 := by exact prefixLift 7123982
  have htrace : WordTrace (prefixWord ++ tailWord_7123982) baseStart_7123982 baseEnd_7123982 := by
    simpa [prefixWord, tailWord_7123982, baseEnd_7123982] using wordTrace_append hprefix tailTrace_7123982
  have hstable : (prefixWord ++ tailWord_7123982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7123982).length < 2 ^ (prefixWord ++ tailWord_7123982).sum := by decide
  have hdescent : baseEnd_7123982 < baseStart_7123982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7123982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124005 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 10]
def baseStart_7124005 : Nat := 118140960795 + 7124005 * 2 ^ 59
def prefixEnd_7124005 : Nat := 4983230072969 + 3 ^ 40 * 7124005 * 2
def baseEnd_7124005 : Nat := 406448750003722781263867

theorem tailTrace_7124005 : CollatzResearch.WordTrace tailWord_7124005 prefixEnd_7124005 406448750003722781263867 := by
  unfold tailWord_7124005
  simp only [CollatzResearch.WordTrace]
  refine ⟨259833808555954043034013469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173222539037302695356008979 259833808555954043034013469)
  ·
    refine ⟨97437678208482766137755051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259833808555954043034013469 97437678208482766137755051)
    ·
      refine ⟨146156517312724149206632577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97437678208482766137755051 146156517312724149206632577)
      ·
        refine ⟨109617387984543111904974433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146156517312724149206632577 109617387984543111904974433)
        ·
          refine ⟨82213040988407333928730825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109617387984543111904974433 82213040988407333928730825)
          ·
            refine ⟨61659780741305500446548119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82213040988407333928730825 61659780741305500446548119)
            ·
              refine ⟨92489671111958250669822179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61659780741305500446548119 92489671111958250669822179)
              ·
                refine ⟨138734506667937376004733269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92489671111958250669822179 138734506667937376004733269)
                ·
                  refine ⟨406448750003722781263867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 138734506667937376004733269 406448750003722781263867)
                  ·
                    rfl

theorem cell23_7124005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 10].length) (baseStart_7124005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124005 prefixEnd_7124005 := by exact prefixLift 7124005
  have htrace : WordTrace (prefixWord ++ tailWord_7124005) baseStart_7124005 baseEnd_7124005 := by
    simpa [prefixWord, tailWord_7124005, baseEnd_7124005] using wordTrace_append hprefix tailTrace_7124005
  have hstable : (prefixWord ++ tailWord_7124005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124005).length < 2 ^ (prefixWord ++ tailWord_7124005).sum := by decide
  have hdescent : baseEnd_7124005 < baseStart_7124005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124039 : List Nat := [1, 1, 4, 1, 3, 2, 4, 1, 6]
def baseStart_7124039 : Nat := 118140960795 + 7124039 * 2 ^ 59
def prefixEnd_7124039 : Nat := 4983230072969 + 3 ^ 40 * 7124039 * 2
def baseEnd_7124039 : Nat := 406450689819528655372183

theorem tailTrace_7124039 : CollatzResearch.WordTrace tailWord_7124039 prefixEnd_7124039 406450689819528655372183 := by
  unfold tailWord_7124039
  simp only [CollatzResearch.WordTrace]
  refine ⟨259835048637830866840751171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173223365758553911227167447 259835048637830866840751171)
  ·
    refine ⟨389752572956746300261126757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259835048637830866840751171 389752572956746300261126757)
    ·
      refine ⟨73078607429389931298961267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389752572956746300261126757 73078607429389931298961267)
      ·
        refine ⟨109617911144084896948441901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73078607429389931298961267 109617911144084896948441901)
        ·
          refine ⟨41106716679031836355665713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109617911144084896948441901 41106716679031836355665713)
          ·
            refine ⟨30830037509273877266749285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41106716679031836355665713 30830037509273877266749285)
            ·
              refine ⟨5780632032988851987515491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30830037509273877266749285 5780632032988851987515491)
              ·
                refine ⟨8670948049483277981273237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5780632032988851987515491 8670948049483277981273237)
                ·
                  refine ⟨406450689819528655372183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8670948049483277981273237 406450689819528655372183)
                  ·
                    rfl

theorem cell23_7124039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 6].length) (baseStart_7124039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124039 prefixEnd_7124039 := by exact prefixLift 7124039
  have htrace : WordTrace (prefixWord ++ tailWord_7124039) baseStart_7124039 baseEnd_7124039 := by
    simpa [prefixWord, tailWord_7124039, baseEnd_7124039] using wordTrace_append hprefix tailTrace_7124039
  have hstable : (prefixWord ++ tailWord_7124039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124039).length < 2 ^ (prefixWord ++ tailWord_7124039).sum := by decide
  have hdescent : baseEnd_7124039 < baseStart_7124039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124049 : List Nat := [1, 2, 2, 1, 3, 1, 2, 4, 3, 1, 3]
def baseStart_7124049 : Nat := 118140960795 + 7124049 * 2 ^ 59
def prefixEnd_7124049 : Nat := 4983230072969 + 3 ^ 40 * 7124049 * 2
def baseEnd_7124049 : Nat := 3658061343182302859224601

theorem tailTrace_7124049 : CollatzResearch.WordTrace tailWord_7124049 prefixEnd_7124049 3658061343182302859224601 := by
  unfold tailWord_7124049
  simp only [CollatzResearch.WordTrace]
  refine ⟨259835413367794638548615201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173223608911863092365743467 259835413367794638548615201)
  ·
    refine ⟨194876560025845978911461401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259835413367794638548615201 194876560025845978911461401)
    ·
      refine ⟨146157420019384484183596051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194876560025845978911461401 146157420019384484183596051)
      ·
        refine ⟨219236130029076726275394077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146157420019384484183596051 219236130029076726275394077)
        ·
          refine ⟨82213548760903772353272779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219236130029076726275394077 82213548760903772353272779)
          ·
            refine ⟨123320323141355658529909169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82213548760903772353272779 123320323141355658529909169)
            ·
              refine ⟨92490242356016743897431877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123320323141355658529909169 92490242356016743897431877)
              ·
                refine ⟨17341920441753139480768477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92490242356016743897431877 17341920441753139480768477)
                ·
                  refine ⟨6503220165657427305288179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17341920441753139480768477 6503220165657427305288179)
                  ·
                    refine ⟨9754830248486140957932269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6503220165657427305288179 9754830248486140957932269)
                    ·
                      refine ⟨3658061343182302859224601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9754830248486140957932269 3658061343182302859224601)
                      ·
                        rfl

theorem cell23_7124049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 1, 3].length) (baseStart_7124049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124049 prefixEnd_7124049 := by exact prefixLift 7124049
  have htrace : WordTrace (prefixWord ++ tailWord_7124049) baseStart_7124049 baseEnd_7124049 := by
    simpa [prefixWord, tailWord_7124049, baseEnd_7124049] using wordTrace_append hprefix tailTrace_7124049
  have hstable : (prefixWord ++ tailWord_7124049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124049).length < 2 ^ (prefixWord ++ tailWord_7124049).sum := by decide
  have hdescent : baseEnd_7124049 < baseStart_7124049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124082 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 3, 6]
def baseStart_7124082 : Nat := 118140960795 + 7124082 * 2 ^ 59
def prefixEnd_7124082 : Nat := 4983230072969 + 3 ^ 40 * 7124082 * 2
def baseEnd_7124082 : Nat := 1219359429347967076703983

theorem tailTrace_7124082 : CollatzResearch.WordTrace tailWord_7124082 prefixEnd_7124082 1219359429347967076703983 := by
  unfold tailWord_7124082
  simp only [CollatzResearch.WordTrace]
  refine ⟨64959154244168771296141625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173224411317783390123044333 64959154244168771296141625)
  ·
    refine ⟨48719365683126578472106219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64959154244168771296141625 48719365683126578472106219)
    ·
      refine ⟨73079048524689867708159329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48719365683126578472106219 73079048524689867708159329)
      ·
        refine ⟨54809286393517400781119497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73079048524689867708159329 54809286393517400781119497)
        ·
          refine ⟨41106964795138050585839623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54809286393517400781119497 41106964795138050585839623)
          ·
            refine ⟨61660447192707075878759435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41106964795138050585839623 61660447192707075878759435)
            ·
              refine ⟨92490670789060613818139153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61660447192707075878759435 92490670789060613818139153)
              ·
                refine ⟨69368003091795460363604365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92490670789060613818139153 69368003091795460363604365)
                ·
                  refine ⟨26013001159423297636351637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69368003091795460363604365 26013001159423297636351637)
                  ·
                    refine ⟨1219359429347967076703983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26013001159423297636351637 1219359429347967076703983)
                    ·
                      rfl

theorem cell23_7124082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_7124082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124082 prefixEnd_7124082 := by exact prefixLift 7124082
  have htrace : WordTrace (prefixWord ++ tailWord_7124082) baseStart_7124082 baseEnd_7124082 := by
    simpa [prefixWord, tailWord_7124082, baseEnd_7124082] using wordTrace_append hprefix tailTrace_7124082
  have hstable : (prefixWord ++ tailWord_7124082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124082).length < 2 ^ (prefixWord ++ tailWord_7124082).sum := by decide
  have hdescent : baseEnd_7124082 < baseStart_7124082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124092 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_7124092 : Nat := 118140960795 + 7124092 * 2 ^ 59
def prefixEnd_7124092 : Nat := 4983230072969 + 3 ^ 40 * 7124092 * 2
def baseEnd_7124092 : Nat := 3658083422850446190986903

theorem tailTrace_7124092 : CollatzResearch.WordTrace tailWord_7124092 prefixEnd_7124092 3658083422850446190986903 := by
  unfold tailWord_7124092
  simp only [CollatzResearch.WordTrace]
  refine ⟨129918490853319428446215265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173224654471092571261620353 129918490853319428446215265)
  ·
    refine ⟨97438868139989571334661449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129918490853319428446215265 97438868139989571334661449)
    ·
      refine ⟨73079151104992178500996087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97438868139989571334661449 73079151104992178500996087)
      ·
        refine ⟨109618726657488267751494131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73079151104992178500996087 109618726657488267751494131)
        ·
          refine ⟨164428089986232401627241197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109618726657488267751494131 164428089986232401627241197)
          ·
            refine ⟨61660533744837150610215449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164428089986232401627241197 61660533744837150610215449)
            ·
              refine ⟨46245400308627862957661587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61660533744837150610215449 46245400308627862957661587)
              ·
                refine ⟨69368100462941794436492381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46245400308627862957661587 69368100462941794436492381)
                ·
                  refine ⟨26013037673603172913684643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69368100462941794436492381 26013037673603172913684643)
                  ·
                    refine ⟨39019556510404759370526965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26013037673603172913684643 39019556510404759370526965)
                    ·
                      refine ⟨3658083422850446190986903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39019556510404759370526965 3658083422850446190986903)
                      ·
                        rfl

theorem cell23_7124092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_7124092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124092 prefixEnd_7124092 := by exact prefixLift 7124092
  have htrace : WordTrace (prefixWord ++ tailWord_7124092) baseStart_7124092 baseEnd_7124092 := by
    simpa [prefixWord, tailWord_7124092, baseEnd_7124092] using wordTrace_append hprefix tailTrace_7124092
  have hstable : (prefixWord ++ tailWord_7124092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124092).length < 2 ^ (prefixWord ++ tailWord_7124092).sum := by decide
  have hdescent : baseEnd_7124092 < baseStart_7124092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124099 : List Nat := [1, 1, 1, 3, 3, 2, 1, 5, 2, 4]
def baseStart_7124099 : Nat := 118140960795 + 7124099 * 2 ^ 59
def prefixEnd_7124099 : Nat := 4983230072969 + 3 ^ 40 * 7124099 * 2
def baseEnd_7124099 : Nat := 1219362339071675887866457

theorem tailTrace_7124099 : CollatzResearch.WordTrace tailWord_7124099 prefixEnd_7124099 1219362339071675887866457 := by
  unfold tailWord_7124099
  simp only [CollatzResearch.WordTrace]
  refine ⟨259837237017613497087935351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173224824678408998058623567 259837237017613497087935351)
  ·
    refine ⟨389755855526420245631903027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259837237017613497087935351 389755855526420245631903027)
    ·
      refine ⟨584633783289630368447854541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389755855526420245631903027 584633783289630368447854541)
      ·
        refine ⟨219237668733611388167945453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 584633783289630368447854541 219237668733611388167945453)
        ·
          refine ⟨82214125775104270562979545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219237668733611388167945453 82214125775104270562979545)
          ·
            refine ⟨61660594331328202922234659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82214125775104270562979545 61660594331328202922234659)
            ·
              refine ⟨92490891496992304383351989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61660594331328202922234659 92490891496992304383351989)
              ·
                refine ⟨8671021077843028535939249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92490891496992304383351989 8671021077843028535939249)
                ·
                  refine ⟨6503265808382271401954437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8671021077843028535939249 6503265808382271401954437)
                  ·
                    refine ⟨1219362339071675887866457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6503265808382271401954437 1219362339071675887866457)
                    ·
                      rfl

theorem cell23_7124099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 4].length) (baseStart_7124099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124099 prefixEnd_7124099 := by exact prefixLift 7124099
  have htrace : WordTrace (prefixWord ++ tailWord_7124099) baseStart_7124099 baseEnd_7124099 := by
    simpa [prefixWord, tailWord_7124099, baseEnd_7124099] using wordTrace_append hprefix tailTrace_7124099
  have hstable : (prefixWord ++ tailWord_7124099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124099).length < 2 ^ (prefixWord ++ tailWord_7124099).sum := by decide
  have hdescent : baseEnd_7124099 < baseStart_7124099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124119 : List Nat := [1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 4]
def baseStart_7124119 : Nat := 118140960795 + 7124119 * 2 ^ 59
def prefixEnd_7124119 : Nat := 4983230072969 + 3 ^ 40 * 7124119 * 2
def baseEnd_7124119 : Nat := 3658097286828117585349279

theorem tailTrace_7124119 : CollatzResearch.WordTrace tailWord_7124119 prefixEnd_7124119 3658097286828117585349279 := by
  unfold tailWord_7124119
  simp only [CollatzResearch.WordTrace]
  refine ⟨259837966477541040503663411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173225310985027360335775607 259837966477541040503663411)
  ·
    refine ⟨389756949716311560755495117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259837966477541040503663411 389756949716311560755495117)
    ·
      refine ⟨146158856143616835283310669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389756949716311560755495117 146158856143616835283310669)
      ·
        refine ⟨54809571053856313231241501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146158856143616835283310669 54809571053856313231241501)
        ·
          refine ⟨20553589145196117461715563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54809571053856313231241501 20553589145196117461715563)
          ·
            refine ⟨30830383717794176192573345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20553589145196117461715563 30830383717794176192573345)
            ·
              refine ⟨23122787788345632144430009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30830383717794176192573345 23122787788345632144430009)
              ·
                refine ⟨17342090841259224108322507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23122787788345632144430009 17342090841259224108322507)
                ·
                  refine ⟨26013136261888836162483761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17342090841259224108322507 26013136261888836162483761)
                  ·
                    refine ⟨19509852196416627121862821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26013136261888836162483761 19509852196416627121862821)
                    ·
                      refine ⟨3658097286828117585349279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19509852196416627121862821 3658097286828117585349279)
                      ·
                        rfl

theorem cell23_7124119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_7124119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124119 prefixEnd_7124119 := by exact prefixLift 7124119
  have htrace : WordTrace (prefixWord ++ tailWord_7124119) baseStart_7124119 baseEnd_7124119 := by
    simpa [prefixWord, tailWord_7124119, baseEnd_7124119] using wordTrace_append hprefix tailTrace_7124119
  have hstable : (prefixWord ++ tailWord_7124119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124119).length < 2 ^ (prefixWord ++ tailWord_7124119).sum := by decide
  have hdescent : baseEnd_7124119 < baseStart_7124119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124150 : List Nat := [5, 1, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_7124150 : Nat := 118140960795 + 7124150 * 2 ^ 59
def prefixEnd_7124150 : Nat := 4983230072969 + 3 ^ 40 * 7124150 * 2
def baseEnd_7124150 : Nat := 1219371068242802321353879

theorem tailTrace_7124150 : CollatzResearch.WordTrace tailWord_7124150 prefixEnd_7124150 1219371068242802321353879 := by
  unfold tailWord_7124150
  simp only [CollatzResearch.WordTrace]
  refine ⟨16239943571276795799877619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173226064760285821865361269 16239943571276795799877619)
  ·
    refine ⟨24359915356915193699816429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16239943571276795799877619 24359915356915193699816429)
    ·
      refine ⟨9134968258843197637431161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24359915356915193699816429 9134968258843197637431161)
      ·
        refine ⟨6851226194132398228073371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9134968258843197637431161 6851226194132398228073371)
        ·
          refine ⟨10276839291198597342110057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6851226194132398228073371 10276839291198597342110057)
          ·
            refine ⟨7707629468398948006582543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10276839291198597342110057 7707629468398948006582543)
            ·
              refine ⟨11561444202598422009873815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7707629468398948006582543 11561444202598422009873815)
              ·
                refine ⟨17342166303897633014810723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11561444202598422009873815 17342166303897633014810723)
                ·
                  refine ⟨26013249455846449522216085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17342166303897633014810723 26013249455846449522216085)
                  ·
                    refine ⟨1219371068242802321353879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26013249455846449522216085 1219371068242802321353879)
                    ·
                      rfl

theorem cell23_7124150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_7124150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124150 prefixEnd_7124150 := by exact prefixLift 7124150
  have htrace : WordTrace (prefixWord ++ tailWord_7124150) baseStart_7124150 baseEnd_7124150 := by
    simpa [prefixWord, tailWord_7124150, baseEnd_7124150] using wordTrace_append hprefix tailTrace_7124150
  have hstable : (prefixWord ++ tailWord_7124150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124150).length < 2 ^ (prefixWord ++ tailWord_7124150).sum := by decide
  have hdescent : baseEnd_7124150 < baseStart_7124150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124156 : List Nat := [2, 2, 2, 3, 2, 1, 3, 1, 1, 3, 3]
def baseStart_7124156 : Nat := 118140960795 + 7124156 * 2 ^ 59
def prefixEnd_7124156 : Nat := 4983230072969 + 3 ^ 40 * 7124156 * 2
def baseEnd_7124156 : Nat := 3658116285612333940586609

theorem tailTrace_7124156 : CollatzResearch.WordTrace tailWord_7124156 prefixEnd_7124156 3658116285612333940586609 := by
  unfold tailWord_7124156
  simp only [CollatzResearch.WordTrace]
  refine ⟨129919657989203497911380161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173226210652271330548506881 129919657989203497911380161)
  ·
    refine ⟨97439743491902623433535121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129919657989203497911380161 97439743491902623433535121)
    ·
      refine ⟨73079807618926967575151341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97439743491902623433535121 73079807618926967575151341)
      ·
        refine ⟨27404927857097612840681753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73079807618926967575151341 27404927857097612840681753)
        ·
          refine ⟨20553695892823209630511315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27404927857097612840681753 20553695892823209630511315)
          ·
            refine ⟨30830543839234814445766973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20553695892823209630511315 30830543839234814445766973)
            ·
              refine ⟨11561453939713055417162615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30830543839234814445766973 11561453939713055417162615)
              ·
                refine ⟨17342180909569583125743923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11561453939713055417162615 17342180909569583125743923)
                ·
                  refine ⟨26013271364354374688615885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17342180909569583125743923 26013271364354374688615885)
                  ·
                    refine ⟨9754976761632890508230957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26013271364354374688615885 9754976761632890508230957)
                    ·
                      refine ⟨3658116285612333940586609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9754976761632890508230957 3658116285612333940586609)
                      ·
                        rfl

theorem cell23_7124156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_7124156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124156 prefixEnd_7124156 := by exact prefixLift 7124156
  have htrace : WordTrace (prefixWord ++ tailWord_7124156) baseStart_7124156 baseEnd_7124156 := by
    simpa [prefixWord, tailWord_7124156, baseEnd_7124156] using wordTrace_append hprefix tailTrace_7124156
  have hstable : (prefixWord ++ tailWord_7124156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124156).length < 2 ^ (prefixWord ++ tailWord_7124156).sum := by decide
  have hdescent : baseEnd_7124156 < baseStart_7124156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124174 : List Nat := [4, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2]
def baseStart_7124174 : Nat := 118140960795 + 7124174 * 2 ^ 59
def prefixEnd_7124174 : Nat := 4983230072969 + 3 ^ 40 * 7124174 * 2
def baseEnd_7124174 : Nat := 3658125528264114870161527

theorem tailTrace_7124174 : CollatzResearch.WordTrace tailWord_7124174 prefixEnd_7124174 3658125528264114870161527 := by
  unfold tailWord_7124174
  simp only [CollatzResearch.WordTrace]
  refine ⟨32479996561542723112114447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173226648328227856597943717 32479996561542723112114447)
  ·
    refine ⟨48719994842314084668171671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32479996561542723112114447 48719994842314084668171671)
    ·
      refine ⟨73079992263471127002257507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48719994842314084668171671 73079992263471127002257507)
      ·
        refine ⟨109619988395206690503386261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73079992263471127002257507 109619988395206690503386261)
        ·
          refine ⟨5138436956025313617346231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109619988395206690503386261 5138436956025313617346231)
          ·
            refine ⟨7707655434037970426019347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5138436956025313617346231 7707655434037970426019347)
            ·
              refine ⟨11561483151056955639029021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7707655434037970426019347 11561483151056955639029021)
              ·
                refine ⟨4335556181646358364635883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11561483151056955639029021 4335556181646358364635883)
                ·
                  refine ⟨6503334272469537546953825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4335556181646358364635883 6503334272469537546953825)
                  ·
                    refine ⟨4877500704352153160215369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6503334272469537546953825 4877500704352153160215369)
                    ·
                      refine ⟨3658125528264114870161527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4877500704352153160215369 3658125528264114870161527)
                      ·
                        rfl

theorem cell23_7124174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2].length) (baseStart_7124174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124174 prefixEnd_7124174 := by exact prefixLift 7124174
  have htrace : WordTrace (prefixWord ++ tailWord_7124174) baseStart_7124174 baseEnd_7124174 := by
    simpa [prefixWord, tailWord_7124174, baseEnd_7124174] using wordTrace_append hprefix tailTrace_7124174
  have hstable : (prefixWord ++ tailWord_7124174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124174).length < 2 ^ (prefixWord ++ tailWord_7124174).sum := by decide
  have hdescent : baseEnd_7124174 < baseStart_7124174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124207 : List Nat := [1, 1, 2, 1, 8, 1, 2, 1, 2, 1, 3]
def baseStart_7124207 : Nat := 118140960795 + 7124207 * 2 ^ 59
def prefixEnd_7124207 : Nat := 4983230072969 + 3 ^ 40 * 7124207 * 2
def baseEnd_7124207 : Nat := 3658142473125713241048875

theorem tailTrace_7124207 : CollatzResearch.WordTrace tailWord_7124207 prefixEnd_7124207 3658142473125713241048875 := by
  unfold tailWord_7124207
  simp only [CollatzResearch.WordTrace]
  refine ⟨259841176101222231532866875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173227450734148154355244583 259841176101222231532866875)
  ·
    refine ⟨389761764151833347299300313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259841176101222231532866875 389761764151833347299300313)
    ·
      refine ⟨292321323113875010474475235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389761764151833347299300313 292321323113875010474475235)
      ·
        refine ⟨438481984670812515711712853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292321323113875010474475235 438481984670812515711712853)
        ·
          refine ⟨5138460757861084168496635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 438481984670812515711712853 5138460757861084168496635)
          ·
            refine ⟨7707691136791626252744953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5138460757861084168496635 7707691136791626252744953)
            ·
              refine ⟨5780768352593719689558715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7707691136791626252744953 5780768352593719689558715)
              ·
                refine ⟨8671152528890579534338073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5780768352593719689558715 8671152528890579534338073)
                ·
                  refine ⟨6503364396667934650753555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8671152528890579534338073 6503364396667934650753555)
                  ·
                    refine ⟨9755046595001901976130333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6503364396667934650753555 9755046595001901976130333)
                    ·
                      refine ⟨3658142473125713241048875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9755046595001901976130333 3658142473125713241048875)
                      ·
                        rfl

theorem cell23_7124207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 2, 1, 3].length) (baseStart_7124207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124207 prefixEnd_7124207 := by exact prefixLift 7124207
  have htrace : WordTrace (prefixWord ++ tailWord_7124207) baseStart_7124207 baseEnd_7124207 := by
    simpa [prefixWord, tailWord_7124207, baseEnd_7124207] using wordTrace_append hprefix tailTrace_7124207
  have hstable : (prefixWord ++ tailWord_7124207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124207).length < 2 ^ (prefixWord ++ tailWord_7124207).sum := by decide
  have hdescent : baseEnd_7124207 < baseStart_7124207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124253 : List Nat := [1, 4, 2, 3, 1, 2, 1, 4, 5]
def baseStart_7124253 : Nat := 118140960795 + 7124253 * 2 ^ 59
def prefixEnd_7124253 : Nat := 4983230072969 + 3 ^ 40 * 7124253 * 2
def baseEnd_7124253 : Nat := 406462899248424451230407

theorem tailTrace_7124253 : CollatzResearch.WordTrace tailWord_7124253 prefixEnd_7124253 406462899248424451230407 := by
  unfold tailWord_7124253
  simp only [CollatzResearch.WordTrace]
  refine ⟨259842853859055581389041413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173228569239370387592694275 259842853859055581389041413)
  ·
    refine ⟨48720535098572921510445265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259842853859055581389041413 48720535098572921510445265)
    ·
      refine ⟨36540401323929691132833949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48720535098572921510445265 36540401323929691132833949)
      ·
        refine ⟨13702650496473634174812731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36540401323929691132833949 13702650496473634174812731)
        ·
          refine ⟨20553975744710451262219097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13702650496473634174812731 20553975744710451262219097)
          ·
            refine ⟨15415481808532838446664323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20553975744710451262219097 15415481808532838446664323)
            ·
              refine ⟨23123222712799257669996485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15415481808532838446664323 23123222712799257669996485)
              ·
                refine ⟨4335604258649860813124341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23123222712799257669996485 4335604258649860813124341)
                ·
                  refine ⟨406462899248424451230407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4335604258649860813124341 406462899248424451230407)
                  ·
                    rfl

theorem cell23_7124253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_7124253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124253 prefixEnd_7124253 := by exact prefixLift 7124253
  have htrace : WordTrace (prefixWord ++ tailWord_7124253) baseStart_7124253 baseEnd_7124253 := by
    simpa [prefixWord, tailWord_7124253, baseEnd_7124253] using wordTrace_append hprefix tailTrace_7124253
  have hstable : (prefixWord ++ tailWord_7124253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124253).length < 2 ^ (prefixWord ++ tailWord_7124253).sum := by decide
  have hdescent : baseEnd_7124253 < baseStart_7124253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124259 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 5]
def baseStart_7124259 : Nat := 118140960795 + 7124259 * 2 ^ 59
def prefixEnd_7124259 : Nat := 4983230072969 + 3 ^ 40 * 7124259 * 2
def baseEnd_7124259 : Nat := 3658169174119747037598635

theorem tailTrace_7124259 : CollatzResearch.WordTrace tailWord_7124259 prefixEnd_7124259 3658169174119747037598635 := by
  unfold tailWord_7124259
  simp only [CollatzResearch.WordTrace]
  refine ⟨259843072697033844413759831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173228715131355896275839887 259843072697033844413759831)
  ·
    refine ⟨389764609045550766620639747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259843072697033844413759831 389764609045550766620639747)
    ·
      refine ⟨584646913568326149930959621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389764609045550766620639747 584646913568326149930959621)
      ·
        refine ⟨109621296294061153112054929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 584646913568326149930959621 109621296294061153112054929)
        ·
          refine ⟨82215972220545864834041197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109621296294061153112054929 82215972220545864834041197)
          ·
            refine ⟨30830989582704699312765449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82215972220545864834041197 30830989582704699312765449)
            ·
              refine ⟨23123242187028524484574087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30830989582704699312765449 23123242187028524484574087)
              ·
                refine ⟨34684863280542786726861131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23123242187028524484574087 34684863280542786726861131)
                ·
                  refine ⟨52027294920814180090291697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34684863280542786726861131 52027294920814180090291697)
                  ·
                    refine ⟨39020471190610635067718773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52027294920814180090291697 39020471190610635067718773)
                    ·
                      refine ⟨3658169174119747037598635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39020471190610635067718773 3658169174119747037598635)
                      ·
                        rfl

theorem cell23_7124259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_7124259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124259 prefixEnd_7124259 := by exact prefixLift 7124259
  have htrace : WordTrace (prefixWord ++ tailWord_7124259) baseStart_7124259 baseEnd_7124259 := by
    simpa [prefixWord, tailWord_7124259, baseEnd_7124259] using wordTrace_append hprefix tailTrace_7124259
  have hstable : (prefixWord ++ tailWord_7124259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124259).length < 2 ^ (prefixWord ++ tailWord_7124259).sum := by decide
  have hdescent : baseEnd_7124259 < baseStart_7124259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124286 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_7124286 : Nat := 118140960795 + 7124286 * 2 ^ 59
def prefixEnd_7124286 : Nat := 4983230072969 + 3 ^ 40 * 7124286 * 2
def baseEnd_7124286 : Nat := 3658183038097418431961011

theorem tailTrace_7124286 : CollatzResearch.WordTrace tailWord_7124286 prefixEnd_7124286 3658183038097418431961011 := by
  unfold tailWord_7124286
  simp only [CollatzResearch.WordTrace]
  refine ⟨32480507183492003503124089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173229371645290685349995141 32480507183492003503124089)
  ·
    refine ⟨24360380387619002627343067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32480507183492003503124089 24360380387619002627343067)
    ·
      refine ⟨36540570581428503941014601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24360380387619002627343067 36540570581428503941014601)
      ·
        refine ⟨27405427936071377955760951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36540570581428503941014601 27405427936071377955760951)
        ·
          refine ⟨41108141904107066933641427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27405427936071377955760951 41108141904107066933641427)
          ·
            refine ⟨61662212856160600400462141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41108141904107066933641427 61662212856160600400462141)
            ·
              refine ⟨23123329821060225150173303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61662212856160600400462141 23123329821060225150173303)
              ·
                refine ⟨34684994731590337725259955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23123329821060225150173303 34684994731590337725259955)
                ·
                  refine ⟨52027492097385506587889933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34684994731590337725259955 52027492097385506587889933)
                  ·
                    refine ⟨19510309536519564970458725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52027492097385506587889933 19510309536519564970458725)
                    ·
                      refine ⟨3658183038097418431961011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19510309536519564970458725 3658183038097418431961011)
                      ·
                        rfl

theorem cell23_7124286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_7124286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124286 prefixEnd_7124286 := by exact prefixLift 7124286
  have htrace : WordTrace (prefixWord ++ tailWord_7124286) baseStart_7124286 baseEnd_7124286 := by
    simpa [prefixWord, tailWord_7124286, baseEnd_7124286] using wordTrace_append hprefix tailTrace_7124286
  have hstable : (prefixWord ++ tailWord_7124286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124286).length < 2 ^ (prefixWord ++ tailWord_7124286).sum := by decide
  have hdescent : baseEnd_7124286 < baseStart_7124286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124306 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_7124306 : Nat := 118140960795 + 7124306 * 2 ^ 59
def prefixEnd_7124306 : Nat := 4983230072969 + 3 ^ 40 * 7124306 * 2
def baseEnd_7124306 : Nat := 3658193307710508353710919

theorem tailTrace_7124306 : CollatzResearch.WordTrace tailWord_7124306 prefixEnd_7124306 3658193307710508353710919 := by
  unfold tailWord_7124306
  simp only [CollatzResearch.WordTrace]
  refine ⟨64961196731965892860180193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173229857951909047627147181 64961196731965892860180193)
  ·
    refine ⟨48720897548974419645135145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64961196731965892860180193 48720897548974419645135145)
    ·
      refine ⟨36540673161730814733851359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48720897548974419645135145 36540673161730814733851359)
      ·
        refine ⟨54811009742596222100777039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36540673161730814733851359 54811009742596222100777039)
        ·
          refine ⟨82216514613894333151165559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54811009742596222100777039 82216514613894333151165559)
          ·
            refine ⟨123324771920841499726748339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82216514613894333151165559 123324771920841499726748339)
            ·
              refine ⟨184987157881262249590122509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123324771920841499726748339 184987157881262249590122509)
              ·
                refine ⟨69370184205473343596295941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184987157881262249590122509 69370184205473343596295941)
                ·
                  refine ⟨13006909538526251924305489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69370184205473343596295941 13006909538526251924305489)
                  ·
                    refine ⟨9755182153894688943229117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13006909538526251924305489 9755182153894688943229117)
                    ·
                      refine ⟨3658193307710508353710919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9755182153894688943229117 3658193307710508353710919)
                      ·
                        rfl

theorem cell23_7124306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_7124306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124306 prefixEnd_7124306 := by exact prefixLift 7124306
  have htrace : WordTrace (prefixWord ++ tailWord_7124306) baseStart_7124306 baseEnd_7124306 := by
    simpa [prefixWord, tailWord_7124306, baseEnd_7124306] using wordTrace_append hprefix tailTrace_7124306
  have hstable : (prefixWord ++ tailWord_7124306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124306).length < 2 ^ (prefixWord ++ tailWord_7124306).sum := by decide
  have hdescent : baseEnd_7124306 < baseStart_7124306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124313 : List Nat := [1, 2, 1, 2, 2, 2, 4, 4, 1, 4]
def baseStart_7124313 : Nat := 118140960795 + 7124313 * 2 ^ 59
def prefixEnd_7124313 : Nat := 4983230072969 + 3 ^ 40 * 7124313 * 2
def baseEnd_7124313 : Nat := 1219398967358363275441129

theorem tailTrace_7124313 : CollatzResearch.WordTrace tailWord_7124313 prefixEnd_7124313 1219398967358363275441129 := by
  unfold tailWord_7124313
  simp only [CollatzResearch.WordTrace]
  refine ⟨259845042238838211636225593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173230028159225474424150395 259845042238838211636225593)
  ·
    refine ⟨194883781679128658727169195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259845042238838211636225593 194883781679128658727169195)
    ·
      refine ⟨292325672518692988090753793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194883781679128658727169195 292325672518692988090753793)
      ·
        refine ⟨219244254389019741068065345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292325672518692988090753793 219244254389019741068065345)
        ·
          refine ⟨164433190791764805801049009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219244254389019741068065345 164433190791764805801049009)
          ·
            refine ⟨123324893093823604350786757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164433190791764805801049009 123324893093823604350786757)
            ·
              refine ⟨23123417455091925815772517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123324893093823604350786757 23123417455091925815772517)
              ·
                refine ⟨4335640772829736090457347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23123417455091925815772517 4335640772829736090457347)
                ·
                  refine ⟨6503461159244604135686021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4335640772829736090457347 6503461159244604135686021)
                  ·
                    refine ⟨1219398967358363275441129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6503461159244604135686021 1219398967358363275441129)
                    ·
                      rfl

theorem cell23_7124313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 1, 4].length) (baseStart_7124313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124313 prefixEnd_7124313 := by exact prefixLift 7124313
  have htrace : WordTrace (prefixWord ++ tailWord_7124313) baseStart_7124313 baseEnd_7124313 := by
    simpa [prefixWord, tailWord_7124313, baseEnd_7124313] using wordTrace_append hprefix tailTrace_7124313
  have hstable : (prefixWord ++ tailWord_7124313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124313).length < 2 ^ (prefixWord ++ tailWord_7124313).sum := by decide
  have hdescent : baseEnd_7124313 < baseStart_7124313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124363 : List Nat := [1, 1, 1, 1, 4, 3, 3, 2, 2, 3, 2]
def baseStart_7124363 : Nat := 118140960795 + 7124363 * 2 ^ 59
def prefixEnd_7124363 : Nat := 4983230072969 + 3 ^ 40 * 7124363 * 2
def baseEnd_7124363 : Nat := 3658222576107814630698157

theorem tailTrace_7124363 : CollatzResearch.WordTrace tailWord_7124363 prefixEnd_7124363 3658222576107814630698157 := by
  unfold tailWord_7124363
  simp only [CollatzResearch.WordTrace]
  refine ⟨259846865888657070175545743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173231243925771380117030495 259846865888657070175545743)
  ·
    refine ⟨389770298832985605263318615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259846865888657070175545743 389770298832985605263318615)
    ·
      refine ⟨584655448249478407894977923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389770298832985605263318615 584655448249478407894977923)
      ·
        refine ⟨876983172374217611842466885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584655448249478407894977923 876983172374217611842466885)
        ·
          refine ⟨164434344820165802220462541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 876983172374217611842466885 164434344820165802220462541)
          ·
            refine ⟨61662879307562175832673453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164434344820165802220462541 61662879307562175832673453)
            ·
              refine ⟨23123579740335815937252545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61662879307562175832673453 23123579740335815937252545)
              ·
                refine ⟨17342684805251861952939409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23123579740335815937252545 17342684805251861952939409)
                ·
                  refine ⟨13007013603938896464704557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17342684805251861952939409 13007013603938896464704557)
                  ·
                    refine ⟨4877630101477086174264209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13007013603938896464704557 4877630101477086174264209)
                    ·
                      refine ⟨3658222576107814630698157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4877630101477086174264209 3658222576107814630698157)
                      ·
                        rfl

theorem cell23_7124363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 3, 2].length) (baseStart_7124363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124363 prefixEnd_7124363 := by exact prefixLift 7124363
  have htrace : WordTrace (prefixWord ++ tailWord_7124363) baseStart_7124363 baseEnd_7124363 := by
    simpa [prefixWord, tailWord_7124363, baseEnd_7124363] using wordTrace_append hprefix tailTrace_7124363
  have hstable : (prefixWord ++ tailWord_7124363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124363).length < 2 ^ (prefixWord ++ tailWord_7124363).sum := by decide
  have hdescent : baseEnd_7124363 < baseStart_7124363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124369 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 3, 6]
def baseStart_7124369 : Nat := 118140960795 + 7124369 * 2 ^ 59
def prefixEnd_7124369 : Nat := 4983230072969 + 3 ^ 40 * 7124369 * 2
def baseEnd_7124369 : Nat := 1219408552330580535741043

theorem tailTrace_7124369 : CollatzResearch.WordTrace tailWord_7124369 prefixEnd_7124369 1219408552330580535741043 := by
  unfold tailWord_7124369
  simp only [CollatzResearch.WordTrace]
  refine ⟨259847084726635333200264161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173231389817756888800176107 259847084726635333200264161)
  ·
    refine ⟨194885313544976499900198121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259847084726635333200264161 194885313544976499900198121)
    ·
      refine ⟨146163985158732374925148591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194885313544976499900198121 146163985158732374925148591)
      ·
        refine ⟨219245977738098562387722887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146163985158732374925148591 219245977738098562387722887)
        ·
          refine ⟨328868966607147843581584331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219245977738098562387722887 328868966607147843581584331)
          ·
            refine ⟨493303449910721765372376497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328868966607147843581584331 493303449910721765372376497)
            ·
              refine ⟨369977587433041324029282373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493303449910721765372376497 369977587433041324029282373)
              ·
                refine ⟨69370797643695248255490445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 369977587433041324029282373 69370797643695248255490445)
                ·
                  refine ⟨26014049116385718095808917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69370797643695248255490445 26014049116385718095808917)
                  ·
                    refine ⟨1219408552330580535741043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26014049116385718095808917 1219408552330580535741043)
                    ·
                      rfl

theorem cell23_7124369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_7124369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124369 prefixEnd_7124369 := by exact prefixLift 7124369
  have htrace : WordTrace (prefixWord ++ tailWord_7124369) baseStart_7124369 baseEnd_7124369 := by
    simpa [prefixWord, tailWord_7124369, baseEnd_7124369] using wordTrace_append hprefix tailTrace_7124369
  have hstable : (prefixWord ++ tailWord_7124369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124369).length < 2 ^ (prefixWord ++ tailWord_7124369).sum := by decide
  have hdescent : baseEnd_7124369 < baseStart_7124369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124397 : List Nat := [1, 5, 2, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_7124397 : Nat := 118140960795 + 7124397 * 2 ^ 59
def prefixEnd_7124397 : Nat := 4983230072969 + 3 ^ 40 * 7124397 * 2
def baseEnd_7124397 : Nat := 3658240034450067497673001

theorem tailTrace_7124397 : CollatzResearch.WordTrace tailWord_7124397 prefixEnd_7124397 3658240034450067497673001 := by
  unfold tailWord_7124397
  simp only [CollatzResearch.WordTrace]
  refine ⟨259848105970533893982283445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173232070647022595988188963 259848105970533893982283445)
  ·
    refine ⟨24360759934737552560839073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 259848105970533893982283445 24360759934737552560839073)
    ·
      refine ⟨18270569951053164420629305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24360759934737552560839073 18270569951053164420629305)
      ·
        refine ⟨13702927463289873315471979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18270569951053164420629305 13702927463289873315471979)
        ·
          refine ⟨20554391194934809973207969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13702927463289873315471979 20554391194934809973207969)
          ·
            refine ⟨15415793396201107479905977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20554391194934809973207969 15415793396201107479905977)
            ·
              refine ⟨11561845047150830609929483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15415793396201107479905977 11561845047150830609929483)
              ·
                refine ⟨17342767570726245914894225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11561845047150830609929483 17342767570726245914894225)
                ·
                  refine ⟨13007075678044684436170669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17342767570726245914894225 13007075678044684436170669)
                  ·
                    refine ⟨4877653379266756663564001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13007075678044684436170669 4877653379266756663564001)
                    ·
                      refine ⟨3658240034450067497673001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4877653379266756663564001 3658240034450067497673001)
                      ·
                        rfl

theorem cell23_7124397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_7124397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124397 prefixEnd_7124397 := by exact prefixLift 7124397
  have htrace : WordTrace (prefixWord ++ tailWord_7124397) baseStart_7124397 baseEnd_7124397 := by
    simpa [prefixWord, tailWord_7124397, baseEnd_7124397] using wordTrace_append hprefix tailTrace_7124397
  have hstable : (prefixWord ++ tailWord_7124397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124397).length < 2 ^ (prefixWord ++ tailWord_7124397).sum := by decide
  have hdescent : baseEnd_7124397 < baseStart_7124397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124420 : List Nat := [2, 3, 3, 2, 1, 1, 1, 4, 2, 4]
def baseStart_7124420 : Nat := 118140960795 + 7124420 * 2 ^ 59
def prefixEnd_7124420 : Nat := 4983230072969 + 3 ^ 40 * 7124420 * 2
def baseEnd_7124420 : Nat := 1219417281501706969228465

theorem tailTrace_7124420 : CollatzResearch.WordTrace tailWord_7124420 prefixEnd_7124420 1219417281501706969228465 := by
  unfold tailWord_7124420
  simp only [CollatzResearch.WordTrace]
  refine ⟨129924472424725284455185357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173232629899633712606913809 129924472424725284455185357)
  ·
    refine ⟨48721677159271981670694509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129924472424725284455185357 48721677159271981670694509)
    ·
      refine ⟨18270628934726993126510441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48721677159271981670694509 18270628934726993126510441)
      ·
        refine ⟨13702971701045244844882831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18270628934726993126510441 13702971701045244844882831)
        ·
          refine ⟨20554457551567867267324247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13702971701045244844882831 20554457551567867267324247)
          ·
            refine ⟨30831686327351800900986371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20554457551567867267324247 30831686327351800900986371)
            ·
              refine ⟨46247529491027701351479557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30831686327351800900986371 46247529491027701351479557)
              ·
                refine ⟨8671411779567694003402417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46247529491027701351479557 8671411779567694003402417)
                ·
                  refine ⟨6503558834675770502551813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8671411779567694003402417 6503558834675770502551813)
                  ·
                    refine ⟨1219417281501706969228465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6503558834675770502551813 1219417281501706969228465)
                    ·
                      rfl

theorem cell23_7124420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_7124420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124420 prefixEnd_7124420 := by exact prefixLift 7124420
  have htrace : WordTrace (prefixWord ++ tailWord_7124420) baseStart_7124420 baseEnd_7124420 := by
    simpa [prefixWord, tailWord_7124420, baseEnd_7124420] using wordTrace_append hprefix tailTrace_7124420
  have hstable : (prefixWord ++ tailWord_7124420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124420).length < 2 ^ (prefixWord ++ tailWord_7124420).sum := by decide
  have hdescent : baseEnd_7124420 < baseStart_7124420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124456 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_7124456 : Nat := 118140960795 + 7124456 * 2 ^ 59
def prefixEnd_7124456 : Nat := 4983230072969 + 3 ^ 40 * 7124456 * 2
def baseEnd_7124456 : Nat := 3658270329808682766835229

theorem tailTrace_7124456 : CollatzResearch.WordTrace tailWord_7124456 prefixEnd_7124456 3658270329808682766835229 := by
  unfold tailWord_7124456
  simp only [CollatzResearch.WordTrace]
  refine ⟨129925128938660073529340611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173233505251546764705787481 129925128938660073529340611)
  ·
    refine ⟨194887693407990110294010917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129925128938660073529340611 194887693407990110294010917)
    ·
      refine ⟨36541442513998145680127047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194887693407990110294010917 36541442513998145680127047)
      ·
        refine ⟨54812163770997218520190571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36541442513998145680127047 54812163770997218520190571)
        ·
          refine ⟨82218245656495827780285857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54812163770997218520190571 82218245656495827780285857)
          ·
            refine ⟨61663684242371870835214393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82218245656495827780285857 61663684242371870835214393)
            ·
              refine ⟨46247763181778903126410795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61663684242371870835214393 46247763181778903126410795)
              ·
                refine ⟨69371644772668354689616193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46247763181778903126410795 69371644772668354689616193)
                ·
                  refine ⟨52028733579501266017212145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69371644772668354689616193 52028733579501266017212145)
                  ·
                    refine ⟨39021550184625949512909109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52028733579501266017212145 39021550184625949512909109)
                    ·
                      refine ⟨3658270329808682766835229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39021550184625949512909109 3658270329808682766835229)
                      ·
                        rfl

theorem cell23_7124456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_7124456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124456 prefixEnd_7124456 := by exact prefixLift 7124456
  have htrace : WordTrace (prefixWord ++ tailWord_7124456) baseStart_7124456 baseEnd_7124456 := by
    simpa [prefixWord, tailWord_7124456, baseEnd_7124456] using wordTrace_append hprefix tailTrace_7124456
  have hstable : (prefixWord ++ tailWord_7124456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124456).length < 2 ^ (prefixWord ++ tailWord_7124456).sum := by decide
  have hdescent : baseEnd_7124456 < baseStart_7124456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124461 : List Nat := [1, 5, 1, 3, 2, 1, 2, 3, 1, 2, 2]
def baseStart_7124461 : Nat := 118140960795 + 7124461 * 2 ^ 59
def prefixEnd_7124461 : Nat := 4983230072969 + 3 ^ 40 * 7124461 * 2
def baseEnd_7124461 : Nat := 3658272897211955247272707

theorem tailTrace_7124461 : CollatzResearch.WordTrace tailWord_7124461 prefixEnd_7124461 3658272897211955247272707 := by
  unfold tailWord_7124461
  simp only [CollatzResearch.WordTrace]
  refine ⟨259850440242302032912613237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173233626828201355275075491 259850440242302032912613237)
  ·
    refine ⟨24360978772715815585557491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 259850440242302032912613237 24360978772715815585557491)
    ·
      refine ⟨36541468159073723378336237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24360978772715815585557491 36541468159073723378336237)
      ·
        refine ⟨13703050559652646266876089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36541468159073723378336237 13703050559652646266876089)
        ·
          refine ⟨10277287919739484700157067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13703050559652646266876089 10277287919739484700157067)
          ·
            refine ⟨15415931879609227050235601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10277287919739484700157067 15415931879609227050235601)
            ·
              refine ⟨11561948909706920287676701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15415931879609227050235601 11561948909706920287676701)
              ·
                refine ⟨4335730841140095107878763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11561948909706920287676701 4335730841140095107878763)
                ·
                  refine ⟨6503596261710142661818145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4335730841140095107878763 6503596261710142661818145)
                  ·
                    refine ⟨4877697196282606996363609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6503596261710142661818145 4877697196282606996363609)
                    ·
                      refine ⟨3658272897211955247272707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4877697196282606996363609 3658272897211955247272707)
                      ·
                        rfl

theorem cell23_7124461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_7124461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124461 prefixEnd_7124461 := by exact prefixLift 7124461
  have htrace : WordTrace (prefixWord ++ tailWord_7124461) baseStart_7124461 baseEnd_7124461 := by
    simpa [prefixWord, tailWord_7124461, baseEnd_7124461] using wordTrace_append hprefix tailTrace_7124461
  have hstable : (prefixWord ++ tailWord_7124461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124461).length < 2 ^ (prefixWord ++ tailWord_7124461).sum := by decide
  have hdescent : baseEnd_7124461 < baseStart_7124461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124476 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 2, 6]
def baseStart_7124476 : Nat := 118140960795 + 7124476 * 2 ^ 59
def prefixEnd_7124476 : Nat := 4983230072969 + 3 ^ 40 * 7124476 * 2
def baseEnd_7124476 : Nat := 1219426866473924229528379

theorem tailTrace_7124476 : CollatzResearch.WordTrace tailWord_7124476 prefixEnd_7124476 1219426866473924229528379 := by
  unfold tailWord_7124476
  simp only [CollatzResearch.WordTrace]
  refine ⟨129925493668623845237204641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173233991558165126982939521 129925493668623845237204641)
  ·
    refine ⟨97444120251467883927903481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129925493668623845237204641 97444120251467883927903481)
    ·
      refine ⟨73083090188600912945927611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97444120251467883927903481 73083090188600912945927611)
      ·
        refine ⟨109624635282901369418891417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73083090188600912945927611 109624635282901369418891417)
        ·
          refine ⟨82218476462176027064168563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109624635282901369418891417 82218476462176027064168563)
          ·
            refine ⟨123327714693264040596252845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82218476462176027064168563 123327714693264040596252845)
            ·
              refine ⟨46247893009974015223594817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123327714693264040596252845 46247893009974015223594817)
              ·
                refine ⟨34685919757480511417696113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46247893009974015223594817 34685919757480511417696113)
                ·
                  refine ⟨26014439818110383563272085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34685919757480511417696113 26014439818110383563272085)
                  ·
                    refine ⟨1219426866473924229528379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26014439818110383563272085 1219426866473924229528379)
                    ·
                      rfl

theorem cell23_7124476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_7124476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124476 prefixEnd_7124476 := by exact prefixLift 7124476
  have htrace : WordTrace (prefixWord ++ tailWord_7124476) baseStart_7124476 baseEnd_7124476 := by
    simpa [prefixWord, tailWord_7124476, baseEnd_7124476] using wordTrace_append hprefix tailTrace_7124476
  have hstable : (prefixWord ++ tailWord_7124476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124476).length < 2 ^ (prefixWord ++ tailWord_7124476).sum := by decide
  have hdescent : baseEnd_7124476 < baseStart_7124476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124477 : List Nat := [1, 4, 1, 1, 1, 6, 1, 2, 2, 1, 3]
def baseStart_7124477 : Nat := 118140960795 + 7124477 * 2 ^ 59
def prefixEnd_7124477 : Nat := 4983230072969 + 3 ^ 40 * 7124477 * 2
def baseEnd_7124477 : Nat := 3658281112902427184672633

theorem tailTrace_7124477 : CollatzResearch.WordTrace tailWord_7124477 prefixEnd_7124477 3658281112902427184672633 := by
  unfold tailWord_7124477
  simp only [CollatzResearch.WordTrace]
  refine ⟨259851023810244067645195685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173234015873496045096797123 259851023810244067645195685)
  ·
    refine ⟨48722066964420762683474191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259851023810244067645195685 48722066964420762683474191)
    ·
      refine ⟨73083100446631144025211287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48722066964420762683474191 73083100446631144025211287)
      ·
        refine ⟨109624650669946716037816931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73083100446631144025211287 109624650669946716037816931)
        ·
          refine ⟨164436976004920074056725397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109624650669946716037816931 164436976004920074056725397)
          ·
            refine ⟨7707983250230628471409003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 164436976004920074056725397 7707983250230628471409003)
            ·
              refine ⟨11561974875345942707113505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7707983250230628471409003 11561974875345942707113505)
              ·
                refine ⟨8671481156509457030335129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11561974875345942707113505 8671481156509457030335129)
                ·
                  refine ⟨6503610867382092772751347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8671481156509457030335129 6503610867382092772751347)
                  ·
                    refine ⟨9755416301073139159127021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6503610867382092772751347 9755416301073139159127021)
                    ·
                      refine ⟨3658281112902427184672633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9755416301073139159127021 3658281112902427184672633)
                      ·
                        rfl

theorem cell23_7124477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_7124477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124477 prefixEnd_7124477 := by exact prefixLift 7124477
  have htrace : WordTrace (prefixWord ++ tailWord_7124477) baseStart_7124477 baseEnd_7124477 := by
    simpa [prefixWord, tailWord_7124477, baseEnd_7124477] using wordTrace_append hprefix tailTrace_7124477
  have hstable : (prefixWord ++ tailWord_7124477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124477).length < 2 ^ (prefixWord ++ tailWord_7124477).sum := by decide
  have hdescent : baseEnd_7124477 < baseStart_7124477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124494 : List Nat := [4, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3]
def baseStart_7124494 : Nat := 118140960795 + 7124494 * 2 ^ 59
def prefixEnd_7124494 : Nat := 4983230072969 + 3 ^ 40 * 7124494 * 2
def baseEnd_7124494 : Nat := 3658289842073553618160055

theorem tailTrace_7124494 : CollatzResearch.WordTrace tailWord_7124494 prefixEnd_7124494 3658289842073553618160055 := by
  unfold tailWord_7124494
  simp only [CollatzResearch.WordTrace]
  refine ⟨32481455481397809943570567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173234429234121653032376357 32481455481397809943570567)
  ·
    refine ⟨48722183222096714915355851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32481455481397809943570567 48722183222096714915355851)
    ·
      refine ⟨73083274833145072373033777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48722183222096714915355851 73083274833145072373033777)
      ·
        refine ⟨54812456124858804279775333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73083274833145072373033777 54812456124858804279775333)
        ·
          refine ⟨10277335523411025802457875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54812456124858804279775333 10277335523411025802457875)
          ·
            refine ⟨15416003285116538703686813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10277335523411025802457875 15416003285116538703686813)
            ·
              refine ⟨5781001231918702013882555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15416003285116538703686813 5781001231918702013882555)
              ·
                refine ⟨8671501847878053020823833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5781001231918702013882555 8671501847878053020823833)
                ·
                  refine ⟨6503626385908539765617875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8671501847878053020823833 6503626385908539765617875)
                  ·
                    refine ⟨9755439578862809648426813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6503626385908539765617875 9755439578862809648426813)
                    ·
                      refine ⟨3658289842073553618160055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9755439578862809648426813 3658289842073553618160055)
                      ·
                        rfl

theorem cell23_7124494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_7124494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124494 prefixEnd_7124494 := by exact prefixLift 7124494
  have htrace : WordTrace (prefixWord ++ tailWord_7124494) baseStart_7124494 baseEnd_7124494 := by
    simpa [prefixWord, tailWord_7124494, baseEnd_7124494] using wordTrace_append hprefix tailTrace_7124494
  have hstable : (prefixWord ++ tailWord_7124494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124494).length < 2 ^ (prefixWord ++ tailWord_7124494).sum := by decide
  have hdescent : baseEnd_7124494 < baseStart_7124494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124520 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_7124520 : Nat := 118140960795 + 7124520 * 2 ^ 59
def prefixEnd_7124520 : Nat := 4983230072969 + 3 ^ 40 * 7124520 * 2
def baseEnd_7124520 : Nat := 3658303192570570516434935

theorem tailTrace_7124520 : CollatzResearch.WordTrace tailWord_7124520 prefixEnd_7124520 3658303192570570516434935 := by
  unfold tailWord_7124520
  simp only [CollatzResearch.WordTrace]
  refine ⟨129926296074544142994505507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173235061432725523992674009 129926296074544142994505507)
  ·
    refine ⟨194889444111816214491758261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129926296074544142994505507 194889444111816214491758261)
    ·
      refine ⟨18270885385482770108602337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194889444111816214491758261 18270885385482770108602337)
      ·
        refine ⟨13703164039112077581451753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18270885385482770108602337 13703164039112077581451753)
        ·
          refine ⟨10277373029334058186088815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13703164039112077581451753 10277373029334058186088815)
          ·
            refine ⟨15416059544001087279133223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10277373029334058186088815 15416059544001087279133223)
            ·
              refine ⟨23124089316001630918699835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15416059544001087279133223 23124089316001630918699835)
              ·
                refine ⟨34686133974002446378049753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23124089316001630918699835 34686133974002446378049753)
                ·
                  refine ⟨26014600480501834783537315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34686133974002446378049753 26014600480501834783537315)
                  ·
                    refine ⟨39021900720752752175305973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26014600480501834783537315 39021900720752752175305973)
                    ·
                      refine ⟨3658303192570570516434935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39021900720752752175305973 3658303192570570516434935)
                      ·
                        rfl

theorem cell23_7124520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_7124520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124520 prefixEnd_7124520 := by exact prefixLift 7124520
  have htrace : WordTrace (prefixWord ++ tailWord_7124520) baseStart_7124520 baseEnd_7124520 := by
    simpa [prefixWord, tailWord_7124520, baseEnd_7124520] using wordTrace_append hprefix tailTrace_7124520
  have hstable : (prefixWord ++ tailWord_7124520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124520).length < 2 ^ (prefixWord ++ tailWord_7124520).sum := by decide
  have hdescent : baseEnd_7124520 < baseStart_7124520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124540 : List Nat := [2, 2, 2, 2, 4, 2, 1, 1, 7]
def baseStart_7124540 : Nat := 118140960795 + 7124540 * 2 ^ 59
def prefixEnd_7124540 : Nat := 4983230072969 + 3 ^ 40 * 7124540 * 2
def baseEnd_7124540 : Nat := 406479273575962270909427

theorem tailTrace_7124540 : CollatzResearch.WordTrace tailWord_7124540 prefixEnd_7124540 406479273575962270909427 := by
  unfold tailWord_7124540
  simp only [CollatzResearch.WordTrace]
  refine ⟨129926660804507914702369537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173235547739343886269826049 129926660804507914702369537)
  ·
    refine ⟨97444995603380936026777153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129926660804507914702369537 97444995603380936026777153)
    ·
      refine ⟨73083746702535702020082865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97444995603380936026777153 73083746702535702020082865)
      ·
        refine ⟨54812810026901776515062149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73083746702535702020082865 54812810026901776515062149)
        ·
          refine ⟨10277401880044083096574153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54812810026901776515062149 10277401880044083096574153)
          ·
            refine ⟨7708051410033062322430615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10277401880044083096574153 7708051410033062322430615)
            ·
              refine ⟨11562077115049593483645923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7708051410033062322430615 11562077115049593483645923)
              ·
                refine ⟨17343115672574390225468885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11562077115049593483645923 17343115672574390225468885)
                ·
                  refine ⟨406479273575962270909427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17343115672574390225468885 406479273575962270909427)
                  ·
                    rfl

theorem cell23_7124540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 7].length) (baseStart_7124540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124540 prefixEnd_7124540 := by exact prefixLift 7124540
  have htrace : WordTrace (prefixWord ++ tailWord_7124540) baseStart_7124540 baseEnd_7124540 := by
    simpa [prefixWord, tailWord_7124540, baseEnd_7124540] using wordTrace_append hprefix tailTrace_7124540
  have hstable : (prefixWord ++ tailWord_7124540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124540).length < 2 ^ (prefixWord ++ tailWord_7124540).sum := by decide
  have hdescent : baseEnd_7124540 < baseStart_7124540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124551 : List Nat := [1, 1, 4, 1, 5, 2, 2, 1, 2, 2, 2]
def baseStart_7124551 : Nat := 118140960795 + 7124551 * 2 ^ 59
def prefixEnd_7124551 : Nat := 4983230072969 + 3 ^ 40 * 7124551 * 2
def baseEnd_7124551 : Nat := 3658319110470859895147293

theorem tailTrace_7124551 : CollatzResearch.WordTrace tailWord_7124551 prefixEnd_7124551 3658319110470859895147293 := by
  unfold tailWord_7124551
  simp only [CollatzResearch.WordTrace]
  refine ⟨259853722811975978283389507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173235815207983985522259671 259853722811975978283389507)
  ·
    refine ⟨389780584217963967425084261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259853722811975978283389507 389780584217963967425084261)
    ·
      refine ⟨73083859540868243892203299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389780584217963967425084261 73083859540868243892203299)
      ·
        refine ⟨109625789311302365838304949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73083859540868243892203299 109625789311302365838304949)
        ·
          refine ⟨10277417747934596797341089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109625789311302365838304949 10277417747934596797341089)
          ·
            refine ⟨7708063310950947598005817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10277417747934596797341089 7708063310950947598005817)
            ·
              refine ⟨5781047483213210698504363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7708063310950947598005817 5781047483213210698504363)
              ·
                refine ⟨8671571224819816047756545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5781047483213210698504363 8671571224819816047756545)
                ·
                  refine ⟨6503678418614862035817409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8671571224819816047756545 6503678418614862035817409)
                  ·
                    refine ⟨4877758813961146526863057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6503678418614862035817409 4877758813961146526863057)
                    ·
                      refine ⟨3658319110470859895147293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4877758813961146526863057 3658319110470859895147293)
                      ·
                        rfl

theorem cell23_7124551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_7124551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124551 prefixEnd_7124551 := by exact prefixLift 7124551
  have htrace : WordTrace (prefixWord ++ tailWord_7124551) baseStart_7124551 baseEnd_7124551 := by
    simpa [prefixWord, tailWord_7124551, baseEnd_7124551] using wordTrace_append hprefix tailTrace_7124551
  have hstable : (prefixWord ++ tailWord_7124551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124551).length < 2 ^ (prefixWord ++ tailWord_7124551).sum := by decide
  have hdescent : baseEnd_7124551 < baseStart_7124551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124613 : List Nat := [1, 3, 1, 1, 4, 1, 1, 5, 6]
def baseStart_7124613 : Nat := 118140960795 + 7124613 * 2 ^ 59
def prefixEnd_7124613 : Nat := 4983230072969 + 3 ^ 40 * 7124613 * 2
def baseEnd_7124613 : Nat := 406483438474604294730223

theorem tailTrace_7124613 : CollatzResearch.WordTrace tailWord_7124613 prefixEnd_7124613 406483438474604294730223 := by
  unfold tailWord_7124613
  simp only [CollatzResearch.WordTrace]
  refine ⟨259855984137751362872146493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173237322758500908581430995 259855984137751362872146493)
  ·
    refine ⟨97445994051656761077054935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259855984137751362872146493 97445994051656761077054935)
    ·
      refine ⟨146168991077485141615582403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97445994051656761077054935 146168991077485141615582403)
      ·
        refine ⟨219253486616227712423373605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146168991077485141615582403 219253486616227712423373605)
        ·
          refine ⟨41110028740542696079382551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219253486616227712423373605 41110028740542696079382551)
          ·
            refine ⟨61665043110814044119073827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41110028740542696079382551 61665043110814044119073827)
            ·
              refine ⟨92497564666221066178610741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61665043110814044119073827 92497564666221066178610741)
              ·
                refine ⟨8671646687458224954244757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92497564666221066178610741 8671646687458224954244757)
                ·
                  refine ⟨406483438474604294730223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8671646687458224954244757 406483438474604294730223)
                  ·
                    rfl

theorem cell23_7124613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 6].length) (baseStart_7124613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124613 prefixEnd_7124613 := by exact prefixLift 7124613
  have htrace : WordTrace (prefixWord ++ tailWord_7124613) baseStart_7124613 baseEnd_7124613 := by
    simpa [prefixWord, tailWord_7124613, baseEnd_7124613] using wordTrace_append hprefix tailTrace_7124613
  have hstable : (prefixWord ++ tailWord_7124613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124613).length < 2 ^ (prefixWord ++ tailWord_7124613).sum := by decide
  have hdescent : baseEnd_7124613 < baseStart_7124613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124680 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 2, 6, 2]
def baseStart_7124680 : Nat := 118140960795 + 7124680 * 2 ^ 59
def prefixEnd_7124680 : Nat := 4983230072969 + 3 ^ 40 * 7124680 * 2
def baseEnd_7124680 : Nat := 3658385349475289890434199

theorem tailTrace_7124680 : CollatzResearch.WordTrace tailWord_7124680 prefixEnd_7124680 3658385349475289890434199 := by
  unfold tailWord_7124680
  simp only [CollatzResearch.WordTrace]
  refine ⟨129929213914254316657417747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173238951885672422209890329 129929213914254316657417747)
  ·
    refine ⟨194893820871381474986126621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129929213914254316657417747 194893820871381474986126621)
    ·
      refine ⟨73085182826768053119797483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194893820871381474986126621 73085182826768053119797483)
      ·
        refine ⟨109627774240152079679696225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73085182826768053119797483 109627774240152079679696225)
        ·
          refine ⟨82220830680114059759772169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109627774240152079679696225 82220830680114059759772169)
          ·
            refine ⟨61665623010085544819829127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82220830680114059759772169 61665623010085544819829127)
            ·
              refine ⟨92498434515128317229743691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61665623010085544819829127 92498434515128317229743691)
              ·
                refine ⟨138747651772692475844615537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92498434515128317229743691 138747651772692475844615537)
                ·
                  refine ⟨104060738829519356883461653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138747651772692475844615537 104060738829519356883461653)
                  ·
                    refine ⟨4877847132633719853912265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104060738829519356883461653 4877847132633719853912265)
                    ·
                      refine ⟨3658385349475289890434199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4877847132633719853912265 3658385349475289890434199)
                      ·
                        rfl

theorem cell23_7124680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_7124680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124680 prefixEnd_7124680 := by exact prefixLift 7124680
  have htrace : WordTrace (prefixWord ++ tailWord_7124680) baseStart_7124680 baseEnd_7124680 := by
    simpa [prefixWord, tailWord_7124680, baseEnd_7124680] using wordTrace_append hprefix tailTrace_7124680
  have hstable : (prefixWord ++ tailWord_7124680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124680).length < 2 ^ (prefixWord ++ tailWord_7124680).sum := by decide
  have hdescent : baseEnd_7124680 < baseStart_7124680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124683 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 3]
def baseStart_7124683 : Nat := 118140960795 + 7124683 * 2 ^ 59
def prefixEnd_7124683 : Nat := 4983230072969 + 3 ^ 40 * 7124683 * 2
def baseEnd_7124683 : Nat := 3658386889917253378696685

theorem tailTrace_7124683 : CollatzResearch.WordTrace tailWord_7124683 prefixEnd_7124683 3658386889917253378696685 := by
  unfold tailWord_7124683
  simp only [CollatzResearch.WordTrace]
  refine ⟨259858537247497764827194703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173239024831665176551463135 259858537247497764827194703)
  ·
    refine ⟨389787805871246647240792055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259858537247497764827194703 389787805871246647240792055)
    ·
      refine ⟨584681708806869970861188083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389787805871246647240792055 584681708806869970861188083)
      ·
        refine ⟨877022563210304956291782125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584681708806869970861188083 877022563210304956291782125)
        ·
          refine ⟨328883461203864358609418297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 877022563210304956291782125 328883461203864358609418297)
          ·
            refine ⟨246662595902898268957063723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328883461203864358609418297 246662595902898268957063723)
            ·
              refine ⟨369993893854347403435595585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246662595902898268957063723 369993893854347403435595585)
              ·
                refine ⟨277495420390760552576696689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369993893854347403435595585 277495420390760552576696689)
                ·
                  refine ⟨208121565293070414432522517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277495420390760552576696689 208121565293070414432522517)
                  ·
                    refine ⟨9755698373112675676524493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 208121565293070414432522517 9755698373112675676524493)
                    ·
                      refine ⟨3658386889917253378696685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9755698373112675676524493 3658386889917253378696685)
                      ·
                        rfl

theorem cell23_7124683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 3].length) (baseStart_7124683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124683 prefixEnd_7124683 := by exact prefixLift 7124683
  have htrace : WordTrace (prefixWord ++ tailWord_7124683) baseStart_7124683 baseEnd_7124683 := by
    simpa [prefixWord, tailWord_7124683, baseEnd_7124683] using wordTrace_append hprefix tailTrace_7124683
  have hstable : (prefixWord ++ tailWord_7124683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124683).length < 2 ^ (prefixWord ++ tailWord_7124683).sum := by decide
  have hdescent : baseEnd_7124683 < baseStart_7124683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124701 : List Nat := [1, 4, 3, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_7124701 : Nat := 118140960795 + 7124701 * 2 ^ 59
def prefixEnd_7124701 : Nat := 4983230072969 + 3 ^ 40 * 7124701 * 2
def baseEnd_7124701 : Nat := 3658396132569034308271603

theorem tailTrace_7124701 : CollatzResearch.WordTrace tailWord_7124701 prefixEnd_7124701 3658396132569034308271603 := by
  unfold tailWord_7124701
  simp only [CollatzResearch.WordTrace]
  refine ⟨259859193761432553901349957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173239462507621702600899971 259859193761432553901349957)
  ·
    refine ⟨48723598830268603856503117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259859193761432553901349957 48723598830268603856503117)
    ·
      refine ⟨18271349561350726446188669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48723598830268603856503117 18271349561350726446188669)
      ·
        refine ⟨6851756085506522417320751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18271349561350726446188669 6851756085506522417320751)
        ·
          refine ⟨10277634128259783625981127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6851756085506522417320751 10277634128259783625981127)
          ·
            refine ⟨15416451192389675438971691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10277634128259783625981127 15416451192389675438971691)
            ·
              refine ⟨23124676788584513158457537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15416451192389675438971691 23124676788584513158457537)
              ·
                refine ⟨17343507591438384868843153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23124676788584513158457537 17343507591438384868843153)
                ·
                  refine ⟨13007630693578788651632365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17343507591438384868843153 13007630693578788651632365)
                  ·
                    refine ⟨4877861510092045744362137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13007630693578788651632365 4877861510092045744362137)
                    ·
                      refine ⟨3658396132569034308271603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4877861510092045744362137 3658396132569034308271603)
                      ·
                        rfl

theorem cell23_7124701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_7124701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124701 prefixEnd_7124701 := by exact prefixLift 7124701
  have htrace : WordTrace (prefixWord ++ tailWord_7124701) baseStart_7124701 baseEnd_7124701 := by
    simpa [prefixWord, tailWord_7124701, baseEnd_7124701] using wordTrace_append hprefix tailTrace_7124701
  have hstable : (prefixWord ++ tailWord_7124701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124701).length < 2 ^ (prefixWord ++ tailWord_7124701).sum := by decide
  have hdescent : baseEnd_7124701 < baseStart_7124701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124714 : List Nat := [3, 1, 3, 1, 1, 1, 5, 1, 3, 2, 2]
def baseStart_7124714 : Nat := 118140960795 + 7124714 * 2 ^ 59
def prefixEnd_7124714 : Nat := 4983230072969 + 3 ^ 40 * 7124714 * 2
def baseEnd_7124714 : Nat := 3658402807817542757409043

theorem tailTrace_7124714 : CollatzResearch.WordTrace tailWord_7124714 prefixEnd_7124714 3658402807817542757409043 := by
  unfold tailWord_7124714
  simp only [CollatzResearch.WordTrace]
  refine ⟨64964916977596364280393299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173239778606923638081048797 64964916977596364280393299)
  ·
    refine ⟨97447375466394546420589949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64964916977596364280393299 97447375466394546420589949)
    ·
      refine ⟨36542765799897954907721231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97447375466394546420589949 36542765799897954907721231)
      ·
        refine ⟨54814148699846932361581847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36542765799897954907721231 54814148699846932361581847)
        ·
          refine ⟨82221223049770398542372771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54814148699846932361581847 82221223049770398542372771)
          ·
            refine ⟨123331834574655597813559157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82221223049770398542372771 123331834574655597813559157)
            ·
              refine ⟨11562359491373962295021171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123331834574655597813559157 11562359491373962295021171)
              ·
                refine ⟨17343539237060943442531757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11562359491373962295021171 17343539237060943442531757)
                ·
                  refine ⟨6503827213897853790949409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17343539237060943442531757 6503827213897853790949409)
                  ·
                    refine ⟨4877870410423390343212057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6503827213897853790949409 4877870410423390343212057)
                    ·
                      refine ⟨3658402807817542757409043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4877870410423390343212057 3658402807817542757409043)
                      ·
                        rfl

theorem cell23_7124714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_7124714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124714 prefixEnd_7124714 := by exact prefixLift 7124714
  have htrace : WordTrace (prefixWord ++ tailWord_7124714) baseStart_7124714 baseEnd_7124714 := by
    simpa [prefixWord, tailWord_7124714, baseEnd_7124714] using wordTrace_append hprefix tailTrace_7124714
  have hstable : (prefixWord ++ tailWord_7124714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124714).length < 2 ^ (prefixWord ++ tailWord_7124714).sum := by decide
  have hdescent : baseEnd_7124714 < baseStart_7124714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124730 : List Nat := [3, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3]
def baseStart_7124730 : Nat := 118140960795 + 7124730 * 2 ^ 59
def prefixEnd_7124730 : Nat := 4983230072969 + 3 ^ 40 * 7124730 * 2
def baseEnd_7124730 : Nat := 3658411023508014694808969

theorem tailTrace_7124730 : CollatzResearch.WordTrace tailWord_7124730 prefixEnd_7124730 3658411023508014694808969 := by
  unfold tailWord_7124730
  simp only [CollatzResearch.WordTrace]
  refine ⟨64965062869581872963538911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173240167652218327902770429 64965062869581872963538911)
  ·
    refine ⟨97447594304372809445308367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64965062869581872963538911 97447594304372809445308367)
    ·
      refine ⟨146171391456559214167962551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97447594304372809445308367 146171391456559214167962551)
      ·
        refine ⟨219257087184838821251943827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146171391456559214167962551 219257087184838821251943827)
        ·
          refine ⟨328885630777258231877915741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219257087184838821251943827 328885630777258231877915741)
          ·
            refine ⟨123332111541471836954218403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328885630777258231877915741 123332111541471836954218403)
            ·
              refine ⟨184998167312207755431327605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123332111541471836954218403 184998167312207755431327605)
              ·
                refine ⟨17343578185519477071686963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184998167312207755431327605 17343578185519477071686963)
                ·
                  refine ⟨26015367278279215607530445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17343578185519477071686963 26015367278279215607530445)
                  ·
                    refine ⟨9755762729354705852823917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26015367278279215607530445 9755762729354705852823917)
                    ·
                      refine ⟨3658411023508014694808969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9755762729354705852823917 3658411023508014694808969)
                      ·
                        rfl

theorem cell23_7124730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_7124730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124730 prefixEnd_7124730 := by exact prefixLift 7124730
  have htrace : WordTrace (prefixWord ++ tailWord_7124730) baseStart_7124730 baseEnd_7124730 := by
    simpa [prefixWord, tailWord_7124730, baseEnd_7124730] using wordTrace_append hprefix tailTrace_7124730
  have hstable : (prefixWord ++ tailWord_7124730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124730).length < 2 ^ (prefixWord ++ tailWord_7124730).sum := by decide
  have hdescent : baseEnd_7124730 < baseStart_7124730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124733 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 4, 7]
def baseStart_7124733 : Nat := 118140960795 + 7124733 * 2 ^ 59
def prefixEnd_7124733 : Nat := 4983230072969 + 3 ^ 40 * 7124733 * 2
def baseEnd_7124733 : Nat := 1219470854649992727690485

theorem tailTrace_7124733 : CollatzResearch.WordTrace tailWord_7124733 prefixEnd_7124733 1219470854649992727690485 := by
  unfold tailWord_7124733
  simp only [CollatzResearch.WordTrace]
  refine ⟨259860360897316623366514853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173240240598211082244343235 259860360897316623366514853)
  ·
    refine ⟨48723817668246866881221535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259860360897316623366514853 48723817668246866881221535)
    ·
      refine ⟨73085726502370300321832303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48723817668246866881221535 73085726502370300321832303)
      ·
        refine ⟨109628589753555450482748455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73085726502370300321832303 109628589753555450482748455)
        ·
          refine ⟨164442884630333175724122683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109628589753555450482748455 164442884630333175724122683)
          ·
            refine ⟨246664326945499763586184025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164442884630333175724122683 246664326945499763586184025)
            ·
              refine ⟨184998245209124822689638019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246664326945499763586184025 184998245209124822689638019)
              ·
                refine ⟨277497367813687234034457029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184998245209124822689638019 277497367813687234034457029)
                ·
                  refine ⟨52030756465066356381460693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 277497367813687234034457029 52030756465066356381460693)
                  ·
                    refine ⟨1219470854649992727690485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52030756465066356381460693 1219470854649992727690485)
                    ·
                      rfl

theorem cell23_7124733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_7124733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124733 prefixEnd_7124733 := by exact prefixLift 7124733
  have htrace : WordTrace (prefixWord ++ tailWord_7124733) baseStart_7124733 baseEnd_7124733 := by
    simpa [prefixWord, tailWord_7124733, baseEnd_7124733] using wordTrace_append hprefix tailTrace_7124733
  have hstable : (prefixWord ++ tailWord_7124733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124733).length < 2 ^ (prefixWord ++ tailWord_7124733).sum := by decide
  have hdescent : baseEnd_7124733 < baseStart_7124733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124734 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_7124734 : Nat := 118140960795 + 7124734 * 2 ^ 59
def prefixEnd_7124734 : Nat := 4983230072969 + 3 ^ 40 * 7124734 * 2
def baseEnd_7124734 : Nat := 3658413077430632679158951

theorem tailTrace_7124734 : CollatzResearch.WordTrace tailWord_7124734 prefixEnd_7124734 3658413077430632679158951 := by
  unfold tailWord_7124734
  simp only [CollatzResearch.WordTrace]
  refine ⟨32482549671289125067162657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173240264913542000358200837 32482549671289125067162657)
  ·
    refine ⟨24361912253466843800371993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32482549671289125067162657 24361912253466843800371993)
    ·
      refine ⟨18271434190100132850278995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24361912253466843800371993 18271434190100132850278995)
      ·
        refine ⟨27407151285150199275418493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18271434190100132850278995 27407151285150199275418493)
        ·
          refine ⟨10277681731931324728281935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27407151285150199275418493 10277681731931324728281935)
          ·
            refine ⟨15416522597896987092422903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10277681731931324728281935 15416522597896987092422903)
            ·
              refine ⟨23124783896845480638634355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15416522597896987092422903 23124783896845480638634355)
              ·
                refine ⟨34687175845268220957951533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23124783896845480638634355 34687175845268220957951533)
                ·
                  refine ⟨13007690941975582859231825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34687175845268220957951533 13007690941975582859231825)
                  ·
                    refine ⟨9755768206481687144423869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13007690941975582859231825 9755768206481687144423869)
                    ·
                      refine ⟨3658413077430632679158951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9755768206481687144423869 3658413077430632679158951)
                      ·
                        rfl

theorem cell23_7124734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_7124734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124734 prefixEnd_7124734 := by exact prefixLift 7124734
  have htrace : WordTrace (prefixWord ++ tailWord_7124734) baseStart_7124734 baseEnd_7124734 := by
    simpa [prefixWord, tailWord_7124734, baseEnd_7124734] using wordTrace_append hprefix tailTrace_7124734
  have hstable : (prefixWord ++ tailWord_7124734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124734).length < 2 ^ (prefixWord ++ tailWord_7124734).sum := by decide
  have hdescent : baseEnd_7124734 < baseStart_7124734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124763 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 4, 6]
def baseStart_7124763 : Nat := 118140960795 + 7124763 * 2 ^ 59
def prefixEnd_7124763 : Nat := 4983230072969 + 3 ^ 40 * 7124763 * 2
def baseEnd_7124763 : Nat := 1219475989456537688565439

theorem tailTrace_7124763 : CollatzResearch.WordTrace tailWord_7124763 prefixEnd_7124763 1219475989456537688565439 := by
  unfold tailWord_7124763
  simp only [CollatzResearch.WordTrace]
  refine ⟨259861455087207938490106943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173240970058138625660071295 259861455087207938490106943)
  ·
    refine ⟨389792182630811907735160415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259861455087207938490106943 389792182630811907735160415)
    ·
      refine ⟨584688273946217861602740623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389792182630811907735160415 584688273946217861602740623)
      ·
        refine ⟨877032410919326792404110935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584688273946217861602740623 877032410919326792404110935)
        ·
          refine ⟨1315548616378990188606166403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 877032410919326792404110935 1315548616378990188606166403)
          ·
            refine ⟨1973322924568485282909249605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315548616378990188606166403 1973322924568485282909249605)
            ·
              refine ⟨369998048356590990545484301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1973322924568485282909249605 369998048356590990545484301)
              ·
                refine ⟨138749268133721621454556613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369998048356590990545484301 138749268133721621454556613)
                ·
                  refine ⟨26015487775072804022729365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138749268133721621454556613 26015487775072804022729365)
                  ·
                    refine ⟨1219475989456537688565439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26015487775072804022729365 1219475989456537688565439)
                    ·
                      rfl

theorem cell23_7124763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 6].length) (baseStart_7124763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124763 prefixEnd_7124763 := by exact prefixLift 7124763
  have htrace : WordTrace (prefixWord ++ tailWord_7124763) baseStart_7124763 baseEnd_7124763 := by
    simpa [prefixWord, tailWord_7124763, baseEnd_7124763] using wordTrace_append hprefix tailTrace_7124763
  have hstable : (prefixWord ++ tailWord_7124763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124763).length < 2 ^ (prefixWord ++ tailWord_7124763).sum := by decide
  have hdescent : baseEnd_7124763 < baseStart_7124763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124764 : List Nat := [2, 2, 3, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_7124764 : Nat := 118140960795 + 7124764 * 2 ^ 59
def prefixEnd_7124764 : Nat := 4983230072969 + 3 ^ 40 * 7124764 * 2
def baseEnd_7124764 : Nat := 3658428481850267561783813

theorem tailTrace_7124764 : CollatzResearch.WordTrace tailWord_7124764 prefixEnd_7124764 3658428481850267561783813 := by
  unfold tailWord_7124764
  simp only [CollatzResearch.WordTrace]
  refine ⟨129930745780102157830446673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173240994373469543773928897 129930745780102157830446673)
  ·
    refine ⟨97448059335076618372835005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129930745780102157830446673 97448059335076618372835005)
    ·
      refine ⟨36543022250653731889813127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97448059335076618372835005 36543022250653731889813127)
      ·
        refine ⟨54814533375980597834719691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36543022250653731889813127 54814533375980597834719691)
        ·
          refine ⟨82221800063970896752079537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54814533375980597834719691 82221800063970896752079537)
          ·
            refine ⟨61666350047978172564059653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82221800063970896752079537 61666350047978172564059653)
            ·
              refine ⟨11562440633995907355761185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61666350047978172564059653 11562440633995907355761185)
              ·
                refine ⟨8671830475496930516820889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11562440633995907355761185 8671830475496930516820889)
                ·
                  refine ⟨6503872856622697887615667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8671830475496930516820889 6503872856622697887615667)
                  ·
                    refine ⟨9755809284934046831423501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6503872856622697887615667 9755809284934046831423501)
                    ·
                      refine ⟨3658428481850267561783813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9755809284934046831423501 3658428481850267561783813)
                      ·
                        rfl

theorem cell23_7124764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_7124764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124764 prefixEnd_7124764 := by exact prefixLift 7124764
  have htrace : WordTrace (prefixWord ++ tailWord_7124764) baseStart_7124764 baseEnd_7124764 := by
    simpa [prefixWord, tailWord_7124764, baseEnd_7124764] using wordTrace_append hprefix tailTrace_7124764
  have hstable : (prefixWord ++ tailWord_7124764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124764).length < 2 ^ (prefixWord ++ tailWord_7124764).sum := by decide
  have hdescent : baseEnd_7124764 < baseStart_7124764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124770 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_7124770 : Nat := 118140960795 + 7124770 * 2 ^ 59
def prefixEnd_7124770 : Nat := 4983230072969 + 3 ^ 40 * 7124770 * 2
def baseEnd_7124770 : Nat := 3658431562734194538308785

theorem tailTrace_7124770 : CollatzResearch.WordTrace tailWord_7124770 prefixEnd_7124770 3658431562734194538308785 := by
  unfold tailWord_7124770
  simp only [CollatzResearch.WordTrace]
  refine ⟨64965427599545644671402941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173241140265455052457074509 64965427599545644671402941)
  ·
    refine ⟨24362035349829616751776103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64965427599545644671402941 24362035349829616751776103)
    ·
      refine ⟨36543053024744425127664155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24362035349829616751776103 36543053024744425127664155)
      ·
        refine ⟨54814579537116637691496233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36543053024744425127664155 54814579537116637691496233)
        ·
          refine ⟨41110934652837478268622175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54814579537116637691496233 41110934652837478268622175)
          ·
            refine ⟨61666401979256217402933263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41110934652837478268622175 61666401979256217402933263)
            ·
              refine ⟨92499602968884326104399895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61666401979256217402933263 92499602968884326104399895)
              ·
                refine ⟨138749404453326489156599843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92499602968884326104399895 138749404453326489156599843)
                ·
                  refine ⟨208124106679989733734899765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138749404453326489156599843 208124106679989733734899765)
                  ·
                    refine ⟨19511635001249037537646853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 208124106679989733734899765 19511635001249037537646853)
                    ·
                      refine ⟨3658431562734194538308785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19511635001249037537646853 3658431562734194538308785)
                      ·
                        rfl

theorem cell23_7124770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_7124770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124770 prefixEnd_7124770 := by exact prefixLift 7124770
  have htrace : WordTrace (prefixWord ++ tailWord_7124770) baseStart_7124770 baseEnd_7124770 := by
    simpa [prefixWord, tailWord_7124770, baseEnd_7124770] using wordTrace_append hprefix tailTrace_7124770
  have hstable : (prefixWord ++ tailWord_7124770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124770).length < 2 ^ (prefixWord ++ tailWord_7124770).sum := by decide
  have hdescent : baseEnd_7124770 < baseStart_7124770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124780 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 2, 6]
def baseStart_7124780 : Nat := 118140960795 + 7124780 * 2 ^ 59
def prefixEnd_7124780 : Nat := 4983230072969 + 3 ^ 40 * 7124780 * 2
def baseEnd_7124780 : Nat := 1219478899180246499727913

theorem tailTrace_7124780 : CollatzResearch.WordTrace tailWord_7124780 prefixEnd_7124780 1219478899180246499727913 := by
  unfold tailWord_7124780
  simp only [CollatzResearch.WordTrace]
  refine ⟨129931037564073175196737897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173241383418764233595650529 129931037564073175196737897)
  ·
    refine ⟨97448278173054881397553423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129931037564073175196737897 97448278173054881397553423)
    ·
      refine ⟨146172417259582322096330135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97448278173054881397553423 146172417259582322096330135)
      ·
        refine ⟨219258625889373483144495203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146172417259582322096330135 219258625889373483144495203)
        ·
          refine ⟨328887938834060224716742805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219258625889373483144495203 328887938834060224716742805)
          ·
            refine ⟨15416622132846573033597319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 328887938834060224716742805 15416622132846573033597319)
            ·
              refine ⟨23124933199269859550395979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15416622132846573033597319 23124933199269859550395979)
              ·
                refine ⟨34687399798904789325593969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23124933199269859550395979 34687399798904789325593969)
                ·
                  refine ⟨26015549849178591994195477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34687399798904789325593969 26015549849178591994195477)
                  ·
                    refine ⟨1219478899180246499727913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26015549849178591994195477 1219478899180246499727913)
                    ·
                      rfl

theorem cell23_7124780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_7124780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124780 prefixEnd_7124780 := by exact prefixLift 7124780
  have htrace : WordTrace (prefixWord ++ tailWord_7124780) baseStart_7124780 baseEnd_7124780 := by
    simpa [prefixWord, tailWord_7124780, baseEnd_7124780] using wordTrace_append hprefix tailTrace_7124780
  have hstable : (prefixWord ++ tailWord_7124780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124780).length < 2 ^ (prefixWord ++ tailWord_7124780).sum := by decide
  have hdescent : baseEnd_7124780 < baseStart_7124780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124783 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 6]
def baseStart_7124783 : Nat := 118140960795 + 7124783 * 2 ^ 59
def prefixEnd_7124783 : Nat := 4983230072969 + 3 ^ 40 * 7124783 * 2
def baseEnd_7124783 : Nat := 3658438237982702987446225

theorem tailTrace_7124783 : CollatzResearch.WordTrace tailWord_7124783 prefixEnd_7124783 3658438237982702987446225 := by
  unfold tailWord_7124783
  simp only [CollatzResearch.WordTrace]
  refine ⟨259862184547135481905835003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173241456364756987937223335 259862184547135481905835003)
  ·
    refine ⟨389793276820703222858752505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259862184547135481905835003 389793276820703222858752505)
    ·
      refine ⟨292344957615527417144064379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389793276820703222858752505 292344957615527417144064379)
      ·
        refine ⟨438517436423291125716096569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292344957615527417144064379 438517436423291125716096569)
        ·
          refine ⟨328888077317468344287072427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438517436423291125716096569 328888077317468344287072427)
          ·
            refine ⟨493332115976202516430608641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328888077317468344287072427 493332115976202516430608641)
            ·
              refine ⟨369999086982151887322956481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493332115976202516430608641 369999086982151887322956481)
              ·
                refine ⟨277499315236613915492217361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369999086982151887322956481 277499315236613915492217361)
                ·
                  refine ⟨208124486427460436619163021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277499315236613915492217361 208124486427460436619163021)
                  ·
                    refine ⟨78046682410297663732186133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 208124486427460436619163021 78046682410297663732186133)
                    ·
                      refine ⟨3658438237982702987446225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78046682410297663732186133 3658438237982702987446225)
                      ·
                        rfl

theorem cell23_7124783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_7124783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124783 prefixEnd_7124783 := by exact prefixLift 7124783
  have htrace : WordTrace (prefixWord ++ tailWord_7124783) baseStart_7124783 baseEnd_7124783 := by
    simpa [prefixWord, tailWord_7124783, baseEnd_7124783] using wordTrace_append hprefix tailTrace_7124783
  have hstable : (prefixWord ++ tailWord_7124783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124783).length < 2 ^ (prefixWord ++ tailWord_7124783).sum := by decide
  have hdescent : baseEnd_7124783 < baseStart_7124783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124821 : List Nat := [1, 3, 2, 2, 2, 2, 3, 2, 2, 2, 2]
def baseStart_7124821 : Nat := 118140960795 + 7124821 * 2 ^ 59
def prefixEnd_7124821 : Nat := 4983230072969 + 3 ^ 40 * 7124821 * 2
def baseEnd_7124821 : Nat := 3658457750247573838771051

theorem tailTrace_7124821 : CollatzResearch.WordTrace tailWord_7124821 prefixEnd_7124821 3658457750247573838771051 := by
  unfold tailWord_7124821
  simp only [CollatzResearch.WordTrace]
  refine ⟨259863570520997814395718317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173242380347331876263812211 259863570520997814395718317)
  ·
    refine ⟨97448838945374180398394369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259863570520997814395718317 97448838945374180398394369)
    ·
      refine ⟨73086629209030635298795777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97448838945374180398394369 73086629209030635298795777)
      ·
        refine ⟨54814971906772976474096833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73086629209030635298795777 54814971906772976474096833)
        ·
          refine ⟨41111228930079732355572625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54814971906772976474096833 41111228930079732355572625)
          ·
            refine ⟨30833421697559799266679469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41111228930079732355572625 30833421697559799266679469)
            ·
              refine ⟨11562533136584924725004801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30833421697559799266679469 11562533136584924725004801)
              ·
                refine ⟨8671899852438693543753601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11562533136584924725004801 8671899852438693543753601)
                ·
                  refine ⟨6503924889329020157815201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8671899852438693543753601 6503924889329020157815201)
                  ·
                    refine ⟨4877943666996765118361401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6503924889329020157815201 4877943666996765118361401)
                    ·
                      refine ⟨3658457750247573838771051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4877943666996765118361401 3658457750247573838771051)
                      ·
                        rfl

theorem cell23_7124821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_7124821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124821 prefixEnd_7124821 := by exact prefixLift 7124821
  have htrace : WordTrace (prefixWord ++ tailWord_7124821) baseStart_7124821 baseEnd_7124821 := by
    simpa [prefixWord, tailWord_7124821, baseEnd_7124821] using wordTrace_append hprefix tailTrace_7124821
  have hstable : (prefixWord ++ tailWord_7124821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124821).length < 2 ^ (prefixWord ++ tailWord_7124821).sum := by decide
  have hdescent : baseEnd_7124821 < baseStart_7124821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124840 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 3, 7]
def baseStart_7124840 : Nat := 118140960795 + 7124840 * 2 ^ 59
def prefixEnd_7124840 : Nat := 4983230072969 + 3 ^ 40 * 7124840 * 2
def baseEnd_7124840 : Nat := 1219489168793336421477821

theorem tailTrace_7124840 : CollatzResearch.WordTrace tailWord_7124840 prefixEnd_7124840 1219489168793336421477821 := by
  unfold tailWord_7124840
  simp only [CollatzResearch.WordTrace]
  refine ⟨129932131753964490320329987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173242842338619320427106649 129932131753964490320329987)
  ·
    refine ⟨194898197630946735480494981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129932131753964490320329987 194898197630946735480494981)
    ·
      refine ⟨36543412055802512902592809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194898197630946735480494981 36543412055802512902592809)
      ·
        refine ⟨27407559041851884676944607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36543412055802512902592809 27407559041851884676944607)
        ·
          refine ⟨41111338562777827015416911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27407559041851884676944607 41111338562777827015416911)
          ·
            refine ⟨61667007844166740523125367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41111338562777827015416911 61667007844166740523125367)
            ·
              refine ⟨92500511766250110784688051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61667007844166740523125367 92500511766250110784688051)
              ·
                refine ⟨138750767649375166177032077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92500511766250110784688051 138750767649375166177032077)
                ·
                  refine ⟨52031537868515687316387029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138750767649375166177032077 52031537868515687316387029)
                  ·
                    refine ⟨1219489168793336421477821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52031537868515687316387029 1219489168793336421477821)
                    ·
                      rfl

theorem cell23_7124840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_7124840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124840 prefixEnd_7124840 := by exact prefixLift 7124840
  have htrace : WordTrace (prefixWord ++ tailWord_7124840) baseStart_7124840 baseEnd_7124840 := by
    simpa [prefixWord, tailWord_7124840, baseEnd_7124840] using wordTrace_append hprefix tailTrace_7124840
  have hstable : (prefixWord ++ tailWord_7124840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124840).length < 2 ^ (prefixWord ++ tailWord_7124840).sum := by decide
  have hdescent : baseEnd_7124840 < baseStart_7124840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124850 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_7124850 : Nat := 118140960795 + 7124850 * 2 ^ 59
def prefixEnd_7124850 : Nat := 4983230072969 + 3 ^ 40 * 7124850 * 2
def baseEnd_7124850 : Nat := 3658472641186554225308417

theorem tailTrace_7124850 : CollatzResearch.WordTrace tailWord_7124850 prefixEnd_7124850 3658472641186554225308417 := by
  unfold tailWord_7124850
  simp only [CollatzResearch.WordTrace]
  refine ⟨64966157059473188087131001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173243085491928501565682669 64966157059473188087131001)
  ·
    refine ⟨48724617794604891065348251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64966157059473188087131001 48724617794604891065348251)
    ·
      refine ⟨73086926691907336598022377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48724617794604891065348251 73086926691907336598022377)
      ·
        refine ⟨54815195018930502448516783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73086926691907336598022377 54815195018930502448516783)
        ·
          refine ⟨82222792528395753672775175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54815195018930502448516783 82222792528395753672775175)
          ·
            refine ⟨123334188792593630509162763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82222792528395753672775175 123334188792593630509162763)
            ·
              refine ⟨185001283188890445763744145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123334188792593630509162763 185001283188890445763744145)
              ·
                refine ⟨138750962391667834322808109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185001283188890445763744145 138750962391667834322808109)
                ·
                  refine ⟨52031610896875437871053041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138750962391667834322808109 52031610896875437871053041)
                  ·
                    refine ⟨39023708172656578403289781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52031610896875437871053041 39023708172656578403289781)
                    ·
                      refine ⟨3658472641186554225308417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39023708172656578403289781 3658472641186554225308417)
                      ·
                        rfl

theorem cell23_7124850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_7124850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124850 prefixEnd_7124850 := by exact prefixLift 7124850
  have htrace : WordTrace (prefixWord ++ tailWord_7124850) baseStart_7124850 baseEnd_7124850 := by
    simpa [prefixWord, tailWord_7124850, baseEnd_7124850] using wordTrace_append hprefix tailTrace_7124850
  have hstable : (prefixWord ++ tailWord_7124850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124850).length < 2 ^ (prefixWord ++ tailWord_7124850).sum := by decide
  have hdescent : baseEnd_7124850 < baseStart_7124850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124874 : List Nat := [3, 1, 2, 4, 2, 1, 1, 2, 2, 5]
def baseStart_7124874 : Nat := 118140960795 + 7124874 * 2 ^ 59
def prefixEnd_7124874 : Nat := 4983230072969 + 3 ^ 40 * 7124874 * 2
def baseEnd_7124874 : Nat := 1219494988240754043802769

theorem tailTrace_7124874 : CollatzResearch.WordTrace tailWord_7124874 prefixEnd_7124874 1219494988240754043802769 := by
  unfold tailWord_7124874
  simp only [CollatzResearch.WordTrace]
  refine ⟨64966375897451451111849419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173243669059870536298265117 64966375897451451111849419)
  ·
    refine ⟨97449563846177176667774129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64966375897451451111849419 97449563846177176667774129)
    ·
      refine ⟨73087172884632882500830597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97449563846177176667774129 73087172884632882500830597)
      ·
        refine ⟨13703844915868665468905737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73087172884632882500830597 13703844915868665468905737)
        ·
          refine ⟨10277883686901499101679303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13703844915868665468905737 10277883686901499101679303)
          ·
            refine ⟨15416825530352248652518955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10277883686901499101679303 15416825530352248652518955)
            ·
              refine ⟨23125238295528372978778433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15416825530352248652518955 23125238295528372978778433)
              ·
                refine ⟨17343928721646279734083825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23125238295528372978778433 17343928721646279734083825)
                ·
                  refine ⟨13007946541234709800562869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17343928721646279734083825 13007946541234709800562869)
                  ·
                    refine ⟨1219494988240754043802769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13007946541234709800562869 1219494988240754043802769)
                    ·
                      rfl

theorem cell23_7124874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_7124874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124874 prefixEnd_7124874 := by exact prefixLift 7124874
  have htrace : WordTrace (prefixWord ++ tailWord_7124874) baseStart_7124874 baseEnd_7124874 := by
    simpa [prefixWord, tailWord_7124874, baseEnd_7124874] using wordTrace_append hprefix tailTrace_7124874
  have hstable : (prefixWord ++ tailWord_7124874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124874).length < 2 ^ (prefixWord ++ tailWord_7124874).sum := by decide
  have hdescent : baseEnd_7124874 < baseStart_7124874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7124878 : List Nat := [4, 1, 1, 5, 1, 1, 3, 2, 5]
def baseStart_7124878 : Nat := 118140960795 + 7124878 * 2 ^ 59
def prefixEnd_7124878 : Nat := 4983230072969 + 3 ^ 40 * 7124878 * 2
def baseEnd_7124878 : Nat := 406498557627208901750921

theorem tailTrace_7124878 : CollatzResearch.WordTrace tailWord_7124878 prefixEnd_7124878 406498557627208901750921 := by
  unfold tailWord_7124878
  simp only [CollatzResearch.WordTrace]
  refine ⟨32483206185223914141317911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173243766321194208753695525 32483206185223914141317911)
  ·
    refine ⟨48724809277835871211976867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32483206185223914141317911 48724809277835871211976867)
    ·
      refine ⟨73087213916753806817965301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48724809277835871211976867 73087213916753806817965301)
      ·
        refine ⟨6851926304695669389184247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73087213916753806817965301 6851926304695669389184247)
        ·
          refine ⟨10277889457043504083776371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6851926304695669389184247 10277889457043504083776371)
          ·
            refine ⟨15416834185565256125664557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10277889457043504083776371 15416834185565256125664557)
            ·
              refine ⟨5781312819586971047124209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15416834185565256125664557 5781312819586971047124209)
              ·
                refine ⟨4335984614690228285343157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5781312819586971047124209 4335984614690228285343157)
                ·
                  refine ⟨406498557627208901750921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4335984614690228285343157 406498557627208901750921)
                  ·
                    rfl

theorem cell23_7124878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_7124878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7124878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7124878 prefixEnd_7124878 := by exact prefixLift 7124878
  have htrace : WordTrace (prefixWord ++ tailWord_7124878) baseStart_7124878 baseEnd_7124878 := by
    simpa [prefixWord, tailWord_7124878, baseEnd_7124878] using wordTrace_append hprefix tailTrace_7124878
  have hstable : (prefixWord ++ tailWord_7124878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7124878).length < 2 ^ (prefixWord ++ tailWord_7124878).sum := by decide
  have hdescent : baseEnd_7124878 < baseStart_7124878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7124878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125021 : List Nat := [1, 4, 2, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_7125021 : Nat := 118140960795 + 7125021 * 2 ^ 59
def prefixEnd_7125021 : Nat := 4983230072969 + 3 ^ 40 * 7125021 * 2
def baseEnd_7125021 : Nat := 3658560446378473056270131

theorem tailTrace_7125021 : CollatzResearch.WordTrace tailWord_7125021 prefixEnd_7125021 3658560446378473056270131 := by
  unfold tailWord_7125021
  simp only [CollatzResearch.WordTrace]
  refine ⟨259870865120273248552998917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173247243413515499035332611 259870865120273248552998917)
  ·
    refine ⟨48725787210051234103687297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259870865120273248552998917 48725787210051234103687297)
    ·
      refine ⟨36544340407538425577765473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48725787210051234103687297 36544340407538425577765473)
      ·
        refine ⟨27408255305653819183324105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36544340407538425577765473 27408255305653819183324105)
        ·
          refine ⟨20556191479240364387493079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27408255305653819183324105 20556191479240364387493079)
          ·
            refine ⟨30834287218860546581239619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20556191479240364387493079 30834287218860546581239619)
            ·
              refine ⟨46251430828290819871859429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30834287218860546581239619 46251430828290819871859429)
              ·
                refine ⟨8672143280304528725973643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46251430828290819871859429 8672143280304528725973643)
                ·
                  refine ⟨13008214920456793088960465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8672143280304528725973643 13008214920456793088960465)
                  ·
                    refine ⟨9756161190342594816720349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13008214920456793088960465 9756161190342594816720349)
                    ·
                      refine ⟨3658560446378473056270131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9756161190342594816720349 3658560446378473056270131)
                      ·
                        rfl

theorem cell23_7125021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_7125021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125021 prefixEnd_7125021 := by exact prefixLift 7125021
  have htrace : WordTrace (prefixWord ++ tailWord_7125021) baseStart_7125021 baseEnd_7125021 := by
    simpa [prefixWord, tailWord_7125021, baseEnd_7125021] using wordTrace_append hprefix tailTrace_7125021
  have hstable : (prefixWord ++ tailWord_7125021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125021).length < 2 ^ (prefixWord ++ tailWord_7125021).sum := by decide
  have hdescent : baseEnd_7125021 < baseStart_7125021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125068 : List Nat := [2, 2, 1, 3, 1, 1, 6, 1, 2, 1, 3]
def baseStart_7125068 : Nat := 118140960795 + 7125068 * 2 ^ 59
def prefixEnd_7125068 : Nat := 4983230072969 + 3 ^ 40 * 7125068 * 2
def baseEnd_7125068 : Nat := 3658584579969234372382415

theorem tailTrace_7125068 : CollatzResearch.WordTrace tailWord_7125068 prefixEnd_7125068 3658584579969234372382415 := by
  unfold tailWord_7125068
  simp only [CollatzResearch.WordTrace]
  refine ⟨129936289675551487789979929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173248386234068650386639905 129936289675551487789979929)
  ·
    refine ⟨97452217256663615842484947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129936289675551487789979929 97452217256663615842484947)
    ·
      refine ⟨146178325884995423763727421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97452217256663615842484947 146178325884995423763727421)
      ·
        refine ⟨54816872206873283911397783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146178325884995423763727421 54816872206873283911397783)
        ·
          refine ⟨82225308310309925867096675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54816872206873283911397783 82225308310309925867096675)
          ·
            refine ⟨123337962465464888800645013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82225308310309925867096675 123337962465464888800645013)
            ·
              refine ⟨5781466990568666662530235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123337962465464888800645013 5781466990568666662530235)
              ·
                refine ⟨8672200485852999993795353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5781466990568666662530235 8672200485852999993795353)
                ·
                  refine ⟨6504150364389749995346515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8672200485852999993795353 6504150364389749995346515)
                  ·
                    refine ⟨9756225546584624993019773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6504150364389749995346515 9756225546584624993019773)
                    ·
                      refine ⟨3658584579969234372382415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9756225546584624993019773 3658584579969234372382415)
                      ·
                        rfl

theorem cell23_7125068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_7125068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125068 prefixEnd_7125068 := by exact prefixLift 7125068
  have htrace : WordTrace (prefixWord ++ tailWord_7125068) baseStart_7125068 baseEnd_7125068 := by
    simpa [prefixWord, tailWord_7125068, baseEnd_7125068] using wordTrace_append hprefix tailTrace_7125068
  have hstable : (prefixWord ++ tailWord_7125068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125068).length < 2 ^ (prefixWord ++ tailWord_7125068).sum := by decide
  have hdescent : baseEnd_7125068 < baseStart_7125068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125087 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 4]
def baseStart_7125087 : Nat := 118140960795 + 7125087 * 2 ^ 59
def prefixEnd_7125087 : Nat := 4983230072969 + 3 ^ 40 * 7125087 * 2
def baseEnd_7125087 : Nat := 3658594336101669798044827

theorem tailTrace_7125087 : CollatzResearch.WordTrace tailWord_7125087 prefixEnd_7125087 3658594336101669798044827 := by
  unfold tailWord_7125087
  simp only [CollatzResearch.WordTrace]
  refine ⟨259873272338034141824901515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173248848225356094549934343 259873272338034141824901515)
  ·
    refine ⟨389809908507051212737352273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259873272338034141824901515 389809908507051212737352273)
    ·
      refine ⟨292357431380288409553014205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389809908507051212737352273 292357431380288409553014205)
      ·
        refine ⟨109634036767608153582380327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292357431380288409553014205 109634036767608153582380327)
        ·
          refine ⟨164451055151412230373570491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109634036767608153582380327 164451055151412230373570491)
          ·
            refine ⟨246676582727118345560355737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164451055151412230373570491 246676582727118345560355737)
            ·
              refine ⟨185007437045338759170266803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246676582727118345560355737 185007437045338759170266803)
              ·
                refine ⟨277511155568008138755400205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185007437045338759170266803 277511155568008138755400205)
                ·
                  refine ⟨104066683338003052033275077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277511155568008138755400205 104066683338003052033275077)
                  ·
                    refine ⟨19512503125875572256239077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104066683338003052033275077 19512503125875572256239077)
                    ·
                      refine ⟨3658594336101669798044827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19512503125875572256239077 3658594336101669798044827)
                      ·
                        rfl

theorem cell23_7125087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_7125087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125087 prefixEnd_7125087 := by exact prefixLift 7125087
  have htrace : WordTrace (prefixWord ++ tailWord_7125087) baseStart_7125087 baseEnd_7125087 := by
    simpa [prefixWord, tailWord_7125087, baseEnd_7125087] using wordTrace_append hprefix tailTrace_7125087
  have hstable : (prefixWord ++ tailWord_7125087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125087).length < 2 ^ (prefixWord ++ tailWord_7125087).sum := by decide
  have hdescent : baseEnd_7125087 < baseStart_7125087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125091 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 6, 2, 2]
def baseStart_7125091 : Nat := 118140960795 + 7125091 * 2 ^ 59
def prefixEnd_7125091 : Nat := 4983230072969 + 3 ^ 40 * 7125091 * 2
def baseEnd_7125091 : Nat := 3658596390024287782394809

theorem tailTrace_7125091 : CollatzResearch.WordTrace tailWord_7125091 prefixEnd_7125091 3658596390024287782394809 := by
  unfold tailWord_7125091
  simp only [CollatzResearch.WordTrace]
  refine ⟨259873418230019650508047127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173248945486679767005364751 259873418230019650508047127)
  ·
    refine ⟨389810127345029475762070691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259873418230019650508047127 389810127345029475762070691)
    ·
      refine ⟨584715191017544213643106037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389810127345029475762070691 584715191017544213643106037)
      ·
        refine ⟨54817049157894770029041191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 584715191017544213643106037 54817049157894770029041191)
        ·
          refine ⟨82225573736842155043561787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54817049157894770029041191 82225573736842155043561787)
          ·
            refine ⟨123338360605263232565342681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82225573736842155043561787 123338360605263232565342681)
            ·
              refine ⟨92503770453947424424007011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123338360605263232565342681 92503770453947424424007011)
              ·
                refine ⟨138755655680921136636010517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92503770453947424424007011 138755655680921136636010517)
                ·
                  refine ⟨6504171360043178279812993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138755655680921136636010517 6504171360043178279812993)
                  ·
                    refine ⟨4878128520032383709859745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6504171360043178279812993 4878128520032383709859745)
                    ·
                      refine ⟨3658596390024287782394809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4878128520032383709859745 3658596390024287782394809)
                      ·
                        rfl

theorem cell23_7125091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_7125091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125091 prefixEnd_7125091 := by exact prefixLift 7125091
  have htrace : WordTrace (prefixWord ++ tailWord_7125091) baseStart_7125091 baseEnd_7125091 := by
    simpa [prefixWord, tailWord_7125091, baseEnd_7125091] using wordTrace_append hprefix tailTrace_7125091
  have hstable : (prefixWord ++ tailWord_7125091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125091).length < 2 ^ (prefixWord ++ tailWord_7125091).sum := by decide
  have hdescent : baseEnd_7125091 < baseStart_7125091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125121 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_7125121 : Nat := 118140960795 + 7125121 * 2 ^ 59
def prefixEnd_7125121 : Nat := 4983230072969 + 3 ^ 40 * 7125121 * 2
def baseEnd_7125121 : Nat := 3658611794443922665019671

theorem tailTrace_7125121 : CollatzResearch.WordTrace tailWord_7125121 prefixEnd_7125121 3658611794443922665019671 := by
  unfold tailWord_7125121
  simp only [CollatzResearch.WordTrace]
  refine ⟨259874512419910965631639217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173249674946607310421092811 259874512419910965631639217)
  ·
    refine ⟨194905884314933224223729413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259874512419910965631639217 194905884314933224223729413)
    ·
      refine ⟨36544853309049979541949265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194905884314933224223729413 36544853309049979541949265)
      ·
        refine ⟨27408639981787484656461949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36544853309049979541949265 27408639981787484656461949)
        ·
          refine ⟨10278239993170306746173231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27408639981787484656461949 10278239993170306746173231)
          ·
            refine ⟨15417359989755460119259847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10278239993170306746173231 15417359989755460119259847)
            ·
              refine ⟨23126039984633190178889771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15417359989755460119259847 23126039984633190178889771)
              ·
                refine ⟨34689059976949785268334657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23126039984633190178889771 34689059976949785268334657)
                ·
                  refine ⟨26016794982712338951250993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34689059976949785268334657 26016794982712338951250993)
                  ·
                    refine ⟨19512596237034254213438245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26016794982712338951250993 19512596237034254213438245)
                    ·
                      refine ⟨3658611794443922665019671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19512596237034254213438245 3658611794443922665019671)
                      ·
                        rfl

theorem cell23_7125121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_7125121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125121 prefixEnd_7125121 := by exact prefixLift 7125121
  have htrace : WordTrace (prefixWord ++ tailWord_7125121) baseStart_7125121 baseEnd_7125121 := by
    simpa [prefixWord, tailWord_7125121, baseEnd_7125121] using wordTrace_append hprefix tailTrace_7125121
  have hstable : (prefixWord ++ tailWord_7125121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125121).length < 2 ^ (prefixWord ++ tailWord_7125121).sum := by decide
  have hdescent : baseEnd_7125121 < baseStart_7125121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125137 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 5]
def baseStart_7125137 : Nat := 118140960795 + 7125137 * 2 ^ 59
def prefixEnd_7125137 : Nat := 4983230072969 + 3 ^ 40 * 7125137 * 2
def baseEnd_7125137 : Nat := 3658620010134394602419597

theorem tailTrace_7125137 : CollatzResearch.WordTrace tailWord_7125137 prefixEnd_7125137 3658620010134394602419597 := by
  unfold tailWord_7125137
  simp only [CollatzResearch.WordTrace]
  refine ⟨259875095987853000364221665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173250063991902000242814443 259875095987853000364221665)
  ·
    refine ⟨194906321990889750273166249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259875095987853000364221665 194906321990889750273166249)
    ·
      refine ⟨146179741493167312704874687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194906321990889750273166249 146179741493167312704874687)
      ·
        refine ⟨219269612239750969057312031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146179741493167312704874687 219269612239750969057312031)
        ·
          refine ⟨328904418359626453585968047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219269612239750969057312031 328904418359626453585968047)
          ·
            refine ⟨493356627539439680378952071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328904418359626453585968047 493356627539439680378952071)
            ·
              refine ⟨740034941309159520568428107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493356627539439680378952071 740034941309159520568428107)
              ·
                refine ⟨1110052411963739280852642161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 740034941309159520568428107 1110052411963739280852642161)
                ·
                  refine ⟨832539308972804460639481621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1110052411963739280852642161 832539308972804460639481621)
                  ·
                    refine ⟨39025280108100209092475701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 832539308972804460639481621 39025280108100209092475701)
                    ·
                      refine ⟨3658620010134394602419597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39025280108100209092475701 3658620010134394602419597)
                      ·
                        rfl

theorem cell23_7125137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_7125137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125137 prefixEnd_7125137 := by exact prefixLift 7125137
  have htrace : WordTrace (prefixWord ++ tailWord_7125137) baseStart_7125137 baseEnd_7125137 := by
    simpa [prefixWord, tailWord_7125137, baseEnd_7125137] using wordTrace_append hprefix tailTrace_7125137
  have hstable : (prefixWord ++ tailWord_7125137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125137).length < 2 ^ (prefixWord ++ tailWord_7125137).sum := by decide
  have hdescent : baseEnd_7125137 < baseStart_7125137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125159 : List Nat := [1, 1, 6, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_7125159 : Nat := 118140960795 + 7125159 * 2 ^ 59
def prefixEnd_7125159 : Nat := 4983230072969 + 3 ^ 40 * 7125159 * 2
def baseEnd_7125159 : Nat := 3658631306708793516344497

theorem tailTrace_7125159 : CollatzResearch.WordTrace tailWord_7125159 prefixEnd_7125159 3658631306708793516344497 := by
  unfold tailWord_7125159
  simp only [CollatzResearch.WordTrace]
  refine ⟨259875898393773298121522531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173250598929182198747681687 259875898393773298121522531)
  ·
    refine ⟨389813847590659947182283797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259875898393773298121522531 389813847590659947182283797)
    ·
      refine ⟨18272524105812185024169553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 389813847590659947182283797 18272524105812185024169553)
      ·
        refine ⟨13704393079359138768127165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18272524105812185024169553 13704393079359138768127165)
        ·
          refine ⟨5139147404759677038047687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13704393079359138768127165 5139147404759677038047687)
          ·
            refine ⟨7708721107139515557071531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5139147404759677038047687 7708721107139515557071531)
            ·
              refine ⟨11563081660709273335607297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7708721107139515557071531 11563081660709273335607297)
              ·
                refine ⟨8672311245531955001705473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11563081660709273335607297 8672311245531955001705473)
                ·
                  refine ⟨6504233434148966251279105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8672311245531955001705473 6504233434148966251279105)
                  ·
                    refine ⟨4878175075611724688459329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6504233434148966251279105 4878175075611724688459329)
                    ·
                      refine ⟨3658631306708793516344497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4878175075611724688459329 3658631306708793516344497)
                      ·
                        rfl

theorem cell23_7125159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_7125159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125159 prefixEnd_7125159 := by exact prefixLift 7125159
  have htrace : WordTrace (prefixWord ++ tailWord_7125159) baseStart_7125159 baseEnd_7125159 := by
    simpa [prefixWord, tailWord_7125159, baseEnd_7125159] using wordTrace_append hprefix tailTrace_7125159
  have hstable : (prefixWord ++ tailWord_7125159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125159).length < 2 ^ (prefixWord ++ tailWord_7125159).sum := by decide
  have hdescent : baseEnd_7125159 < baseStart_7125159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125194 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_7125194 : Nat := 118140960795 + 7125194 * 2 ^ 59
def prefixEnd_7125194 : Nat := 4983230072969 + 3 ^ 40 * 7125194 * 2
def baseEnd_7125194 : Nat := 3658649278531700879406835

theorem tailTrace_7125194 : CollatzResearch.WordTrace tailWord_7125194 prefixEnd_7125194 3658649278531700879406835 := by
  unfold tailWord_7125194
  simp only [CollatzResearch.WordTrace]
  refine ⟨64969293737161624774761659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173251449965764332732697757 64969293737161624774761659)
  ·
    refine ⟨97453940605742437162142489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64969293737161624774761659 97453940605742437162142489)
    ·
      refine ⟨73090455454306827871606867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97453940605742437162142489 73090455454306827871606867)
      ·
        refine ⟨109635683181460241807410301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73090455454306827871606867 109635683181460241807410301)
        ·
          refine ⟨41113381193047590677778863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109635683181460241807410301 41113381193047590677778863)
          ·
            refine ⟨61670071789571386016668295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41113381193047590677778863 61670071789571386016668295)
            ·
              refine ⟨92505107684357079025002443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61670071789571386016668295 92505107684357079025002443)
              ·
                refine ⟨138757661526535618537503665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92505107684357079025002443 138757661526535618537503665)
                ·
                  refine ⟨104068246144901713903127749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138757661526535618537503665 104068246144901713903127749)
                  ·
                    refine ⟨19512796152169071356836453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104068246144901713903127749 19512796152169071356836453)
                    ·
                      refine ⟨3658649278531700879406835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19512796152169071356836453 3658649278531700879406835)
                      ·
                        rfl

theorem cell23_7125194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_7125194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125194 prefixEnd_7125194 := by exact prefixLift 7125194
  have htrace : WordTrace (prefixWord ++ tailWord_7125194) baseStart_7125194 baseEnd_7125194 := by
    simpa [prefixWord, tailWord_7125194, baseEnd_7125194] using wordTrace_append hprefix tailTrace_7125194
  have hstable : (prefixWord ++ tailWord_7125194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125194).length < 2 ^ (prefixWord ++ tailWord_7125194).sum := by decide
  have hdescent : baseEnd_7125194 < baseStart_7125194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125238 : List Nat := [5, 1, 1, 1, 1, 1, 6, 1, 6]
def baseStart_7125238 : Nat := 118140960795 + 7125238 * 2 ^ 59
def prefixEnd_7125238 : Nat := 4983230072969 + 3 ^ 40 * 7125238 * 2
def baseEnd_7125238 : Nat := 406519096853388745250737

theorem tailTrace_7125238 : CollatzResearch.WordTrace tailWord_7125238 prefixEnd_7125238 406519096853388745250737 := by
  unfold tailWord_7125238
  simp only [CollatzResearch.WordTrace]
  refine ⟨16242423735030443413353023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173252519840324729742432245 16242423735030443413353023)
  ·
    refine ⟨24363635602545665120029535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16242423735030443413353023 24363635602545665120029535)
    ·
      refine ⟨36545453403818497680044303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24363635602545665120029535 36545453403818497680044303)
      ·
        refine ⟨54818180105727746520066455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36545453403818497680044303 54818180105727746520066455)
        ·
          refine ⟨82227270158591619780099683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54818180105727746520066455 82227270158591619780099683)
          ·
            refine ⟨123340905237887429670149525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82227270158591619780099683 123340905237887429670149525)
            ·
              refine ⟨5781604933025973265788259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123340905237887429670149525 5781604933025973265788259)
              ·
                refine ⟨8672407399538959898682389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5781604933025973265788259 8672407399538959898682389)
                ·
                  refine ⟨406519096853388745250737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8672407399538959898682389 406519096853388745250737)
                  ·
                    rfl

theorem cell23_7125238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_7125238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125238 prefixEnd_7125238 := by exact prefixLift 7125238
  have htrace : WordTrace (prefixWord ++ tailWord_7125238) baseStart_7125238 baseEnd_7125238 := by
    simpa [prefixWord, tailWord_7125238, baseEnd_7125238] using wordTrace_append hprefix tailTrace_7125238
  have hstable : (prefixWord ++ tailWord_7125238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125238).length < 2 ^ (prefixWord ++ tailWord_7125238).sum := by decide
  have hdescent : baseEnd_7125238 < baseStart_7125238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125241 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 1, 5, 2]
def baseStart_7125241 : Nat := 118140960795 + 7125241 * 2 ^ 59
def prefixEnd_7125241 : Nat := 4983230072969 + 3 ^ 40 * 7125241 * 2
def baseEnd_7125241 : Nat := 3658673412122462195519119

theorem tailTrace_7125241 : CollatzResearch.WordTrace tailWord_7125241 prefixEnd_7125241 3658673412122462195519119 := by
  unfold tailWord_7125241
  simp only [CollatzResearch.WordTrace]
  refine ⟨259878889179476226126007577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173252592786317484084005051 259878889179476226126007577)
  ·
    refine ⟨194909166884607169594505683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259878889179476226126007577 194909166884607169594505683)
    ·
      refine ⟨292363750326910754391758525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194909166884607169594505683 292363750326910754391758525)
      ·
        refine ⟨109636406372591532896909447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292363750326910754391758525 109636406372591532896909447)
        ·
          refine ⟨164454609558887299345364171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109636406372591532896909447 164454609558887299345364171)
          ·
            refine ⟨246681914338330949018046257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164454609558887299345364171 246681914338330949018046257)
            ·
              refine ⟨185011435753748211763534693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246681914338330949018046257 185011435753748211763534693)
              ·
                refine ⟨34689644203827789705662755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185011435753748211763534693 34689644203827789705662755)
                ·
                  refine ⟨52034466305741684558494133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34689644203827789705662755 52034466305741684558494133)
                  ·
                    refine ⟨4878231216163282927358825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52034466305741684558494133 4878231216163282927358825)
                    ·
                      refine ⟨3658673412122462195519119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4878231216163282927358825 3658673412122462195519119)
                      ·
                        rfl

theorem cell23_7125241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_7125241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125241 prefixEnd_7125241 := by exact prefixLift 7125241
  have htrace : WordTrace (prefixWord ++ tailWord_7125241) baseStart_7125241 baseEnd_7125241 := by
    simpa [prefixWord, tailWord_7125241, baseEnd_7125241] using wordTrace_append hprefix tailTrace_7125241
  have hstable : (prefixWord ++ tailWord_7125241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125241).length < 2 ^ (prefixWord ++ tailWord_7125241).sum := by decide
  have hdescent : baseEnd_7125241 < baseStart_7125241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125258 : List Nat := [3, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2]
def baseStart_7125258 : Nat := 118140960795 + 7125258 * 2 ^ 59
def prefixEnd_7125258 : Nat := 4983230072969 + 3 ^ 40 * 7125258 * 2
def baseEnd_7125258 : Nat := 3658682141293588629006541

theorem tailTrace_7125258 : CollatzResearch.WordTrace tailWord_7125258 prefixEnd_7125258 3658682141293588629006541 := by
  unfold tailWord_7125258
  simp only [CollatzResearch.WordTrace]
  refine ⟨64969877305103659507344107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173253006146943092019584285 64969877305103659507344107)
  ·
    refine ⟨97454815957655489261016161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64969877305103659507344107 97454815957655489261016161)
    ·
      refine ⟨73091111968241616945762121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97454815957655489261016161 73091111968241616945762121)
      ·
        refine ⟨54818333976181212709321591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73091111968241616945762121 54818333976181212709321591)
        ·
          refine ⟨82227500964271819063982387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54818333976181212709321591 82227500964271819063982387)
          ·
            refine ⟨123341251446407728595973581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82227500964271819063982387 123341251446407728595973581)
            ·
              refine ⟨46252969292402898223490093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123341251446407728595973581 46252969292402898223490093)
              ·
                refine ⟨17344863484651086833808785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46252969292402898223490093 17344863484651086833808785)
                ·
                  refine ⟨13008647613488315125356589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17344863484651086833808785 13008647613488315125356589)
                  ·
                    refine ⟨4878242855058118172008721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13008647613488315125356589 4878242855058118172008721)
                    ·
                      refine ⟨3658682141293588629006541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4878242855058118172008721 3658682141293588629006541)
                      ·
                        rfl

theorem cell23_7125258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_7125258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125258 prefixEnd_7125258 := by exact prefixLift 7125258
  have htrace : WordTrace (prefixWord ++ tailWord_7125258) baseStart_7125258 baseEnd_7125258 := by
    simpa [prefixWord, tailWord_7125258, baseEnd_7125258] using wordTrace_append hprefix tailTrace_7125258
  have hstable : (prefixWord ++ tailWord_7125258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125258).length < 2 ^ (prefixWord ++ tailWord_7125258).sum := by decide
  have hdescent : baseEnd_7125258 < baseStart_7125258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125281 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 4, 4]
def baseStart_7125281 : Nat := 118140960795 + 7125281 * 2 ^ 59
def prefixEnd_7125281 : Nat := 4983230072969 + 3 ^ 40 * 7125281 * 2
def baseEnd_7125281 : Nat := 1219564650449547346339645

theorem tailTrace_7125281 : CollatzResearch.WordTrace tailWord_7125281 prefixEnd_7125281 1219564650449547346339645 := by
  unfold tailWord_7125281
  simp only [CollatzResearch.WordTrace]
  refine ⟨259880348099331312957463697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173253565399554208638309131 259880348099331312957463697)
  ·
    refine ⟨194910261074498484718097773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259880348099331312957463697 194910261074498484718097773)
    ·
      refine ⟨73091347902936931769286665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194910261074498484718097773 73091347902936931769286665)
      ·
        refine ⟨54818510927202698826964999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73091347902936931769286665 54818510927202698826964999)
        ·
          refine ⟨82227766390804048240447499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54818510927202698826964999 82227766390804048240447499)
          ·
            refine ⟨123341649586206072360671249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82227766390804048240447499 123341649586206072360671249)
            ·
              refine ⟨92506237189654554270503437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123341649586206072360671249 92506237189654554270503437)
              ·
                refine ⟨34689838946120457851438789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92506237189654554270503437 34689838946120457851438789)
                ·
                  refine ⟨6504344802397585847144773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34689838946120457851438789 6504344802397585847144773)
                  ·
                    refine ⟨1219564650449547346339645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6504344802397585847144773 1219564650449547346339645)
                    ·
                      rfl

theorem cell23_7125281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_7125281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125281 prefixEnd_7125281 := by exact prefixLift 7125281
  have htrace : WordTrace (prefixWord ++ tailWord_7125281) baseStart_7125281 baseEnd_7125281 := by
    simpa [prefixWord, tailWord_7125281, baseEnd_7125281] using wordTrace_append hprefix tailTrace_7125281
  have hstable : (prefixWord ++ tailWord_7125281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125281).length < 2 ^ (prefixWord ++ tailWord_7125281).sum := by decide
  have hdescent : baseEnd_7125281 < baseStart_7125281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125282 : List Nat := [3, 3, 1, 1, 3, 2, 1, 4, 1, 1, 3]
def baseStart_7125282 : Nat := 118140960795 + 7125282 * 2 ^ 59
def prefixEnd_7125282 : Nat := 4983230072969 + 3 ^ 40 * 7125282 * 2
def baseEnd_7125282 : Nat := 3658694464829296535106431

theorem tailTrace_7125282 : CollatzResearch.WordTrace tailWord_7125282 prefixEnd_7125282 3658694464829296535106431 := by
  unfold tailWord_7125282
  simp only [CollatzResearch.WordTrace]
  refine ⟨64970096143081922532062525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173253589714885126752166733 64970096143081922532062525)
  ·
    refine ⟨24363786053655720949523447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64970096143081922532062525 24363786053655720949523447)
    ·
      refine ⟨36545679080483581424285171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24363786053655720949523447 36545679080483581424285171)
      ·
        refine ⟨54818518620725372136427757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36545679080483581424285171 54818518620725372136427757)
        ·
          refine ⟨20556944482772014551160409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54818518620725372136427757 20556944482772014551160409)
          ·
            refine ⟨15417708362079010913370307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20556944482772014551160409 15417708362079010913370307)
            ·
              refine ⟨23126562543118516370055461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15417708362079010913370307 23126562543118516370055461)
              ·
                refine ⟨4336230476834721819385399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23126562543118516370055461 4336230476834721819385399)
                ·
                  refine ⟨6504345715252082729078099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4336230476834721819385399 6504345715252082729078099)
                  ·
                    refine ⟨9756518572878124093617149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6504345715252082729078099 9756518572878124093617149)
                    ·
                      refine ⟨3658694464829296535106431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9756518572878124093617149 3658694464829296535106431)
                      ·
                        rfl

theorem cell23_7125282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_7125282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125282 prefixEnd_7125282 := by exact prefixLift 7125282
  have htrace : WordTrace (prefixWord ++ tailWord_7125282) baseStart_7125282 baseEnd_7125282 := by
    simpa [prefixWord, tailWord_7125282, baseEnd_7125282] using wordTrace_append hprefix tailTrace_7125282
  have hstable : (prefixWord ++ tailWord_7125282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125282).length < 2 ^ (prefixWord ++ tailWord_7125282).sum := by decide
  have hdescent : baseEnd_7125282 < baseStart_7125282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125298 : List Nat := [3, 2, 1, 1, 5, 1, 2, 1, 1, 6]
def baseStart_7125298 : Nat := 118140960795 + 7125298 * 2 ^ 59
def prefixEnd_7125298 : Nat := 4983230072969 + 3 ^ 40 * 7125298 * 2
def baseEnd_7125298 : Nat := 1219567560173256157502119

theorem tailTrace_7125298 : CollatzResearch.WordTrace tailWord_7125298 prefixEnd_7125298 1219567560173256157502119 := by
  unfold tailWord_7125298
  simp only [CollatzResearch.WordTrace]
  refine ⟨64970242035067431215208137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173253978760179816573888365 64970242035067431215208137)
  ·
    refine ⟨48727681526300573411406103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64970242035067431215208137 48727681526300573411406103)
    ·
      refine ⟨73091522289450860117109155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48727681526300573411406103 73091522289450860117109155)
      ·
        refine ⟨109637283434176290175663733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73091522289450860117109155 109637283434176290175663733)
        ·
          refine ⟨10278495321954027203968475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109637283434176290175663733 10278495321954027203968475)
          ·
            refine ⟨15417742982931040805952713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10278495321954027203968475 15417742982931040805952713)
            ·
              refine ⟨11563307237198280604464535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15417742982931040805952713 11563307237198280604464535)
              ·
                refine ⟨17344960855797420906696803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11563307237198280604464535 17344960855797420906696803)
                ·
                  refine ⟨26017441283696131360045205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17344960855797420906696803 26017441283696131360045205)
                  ·
                    refine ⟨1219567560173256157502119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26017441283696131360045205 1219567560173256157502119)
                    ·
                      rfl

theorem cell23_7125298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_7125298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125298 prefixEnd_7125298 := by exact prefixLift 7125298
  have htrace : WordTrace (prefixWord ++ tailWord_7125298) baseStart_7125298 baseEnd_7125298 := by
    simpa [prefixWord, tailWord_7125298, baseEnd_7125298] using wordTrace_append hprefix tailTrace_7125298
  have hstable : (prefixWord ++ tailWord_7125298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125298).length < 2 ^ (prefixWord ++ tailWord_7125298).sum := by decide
  have hdescent : baseEnd_7125298 < baseStart_7125298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125305 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 5, 2, 2]
def baseStart_7125305 : Nat := 118140960795 + 7125305 * 2 ^ 59
def prefixEnd_7125305 : Nat := 4983230072969 + 3 ^ 40 * 7125305 * 2
def baseEnd_7125305 : Nat := 3658706274884349945118825

theorem tailTrace_7125305 : CollatzResearch.WordTrace tailWord_7125305 prefixEnd_7125305 3658706274884349945118825 := by
  unfold tailWord_7125305
  simp only [CollatzResearch.WordTrace]
  refine ⟨259881223451244365056337369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173254148967496243370891579 259881223451244365056337369)
  ·
    refine ⟨194910917588433273792253027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259881223451244365056337369 194910917588433273792253027)
    ·
      refine ⟨292366376382649910688379541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194910917588433273792253027 292366376382649910688379541)
      ·
        refine ⟨13704673892936714563517791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 292366376382649910688379541 13704673892936714563517791)
        ·
          refine ⟨20557010839405071845276687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13704673892936714563517791 20557010839405071845276687)
          ·
            refine ⟨30835516259107607767915031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20557010839405071845276687 30835516259107607767915031)
            ·
              refine ⟨46253274388661411651872547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30835516259107607767915031 46253274388661411651872547)
              ·
                refine ⟨69379911582992117477808821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46253274388661411651872547 69379911582992117477808821)
                ·
                  refine ⟨6504366710905511013544577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69379911582992117477808821 6504366710905511013544577)
                  ·
                    refine ⟨4878275033179133260158433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6504366710905511013544577 4878275033179133260158433)
                    ·
                      refine ⟨3658706274884349945118825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4878275033179133260158433 3658706274884349945118825)
                      ·
                        rfl

theorem cell23_7125305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_7125305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125305 prefixEnd_7125305 := by exact prefixLift 7125305
  have htrace : WordTrace (prefixWord ++ tailWord_7125305) baseStart_7125305 baseEnd_7125305 := by
    simpa [prefixWord, tailWord_7125305, baseEnd_7125305] using wordTrace_append hprefix tailTrace_7125305
  have hstable : (prefixWord ++ tailWord_7125305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125305).length < 2 ^ (prefixWord ++ tailWord_7125305).sum := by decide
  have hdescent : baseEnd_7125305 < baseStart_7125305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125308 : List Nat := [2, 2, 2, 2, 1, 2, 2, 4, 1, 2, 3]
def baseStart_7125308 : Nat := 118140960795 + 7125308 * 2 ^ 59
def prefixEnd_7125308 : Nat := 4983230072969 + 3 ^ 40 * 7125308 * 2
def baseEnd_7125308 : Nat := 3658707815326313433381311

theorem tailTrace_7125308 : CollatzResearch.WordTrace tailWord_7125308 prefixEnd_7125308 3658707815326313433381311 := by
  unfold tailWord_7125308
  simp only [CollatzResearch.WordTrace]
  refine ⟨129940666435116748284348289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173254221913488997712464385 129940666435116748284348289)
  ·
    refine ⟨97455499826337561213261217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129940666435116748284348289 97455499826337561213261217)
    ·
      refine ⟨73091624869753170909945913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97455499826337561213261217 73091624869753170909945913)
      ·
        refine ⟨54818718652314878182459435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73091624869753170909945913 54818718652314878182459435)
        ·
          refine ⟨82228077978472317273689153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54818718652314878182459435 82228077978472317273689153)
          ·
            refine ⟨61671058483854237955266865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82228077978472317273689153 61671058483854237955266865)
            ·
              refine ⟨46253293862890678466450149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61671058483854237955266865 46253293862890678466450149)
              ·
                refine ⟨8672492599292002212459403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46253293862890678466450149 8672492599292002212459403)
                ·
                  refine ⟨13008738898938003318689105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8672492599292002212459403 13008738898938003318689105)
                  ·
                    refine ⟨9756554174203502489016829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13008738898938003318689105 9756554174203502489016829)
                    ·
                      refine ⟨3658707815326313433381311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9756554174203502489016829 3658707815326313433381311)
                      ·
                        rfl

theorem cell23_7125308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_7125308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125308 prefixEnd_7125308 := by exact prefixLift 7125308
  have htrace : WordTrace (prefixWord ++ tailWord_7125308) baseStart_7125308 baseEnd_7125308 := by
    simpa [prefixWord, tailWord_7125308, baseEnd_7125308] using wordTrace_append hprefix tailTrace_7125308
  have hstable : (prefixWord ++ tailWord_7125308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125308).length < 2 ^ (prefixWord ++ tailWord_7125308).sum := by decide
  have hdescent : baseEnd_7125308 < baseStart_7125308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125311 : List Nat := [1, 1, 2, 2, 4, 1, 5, 7]
def baseStart_7125311 : Nat := 118140960795 + 7125311 * 2 ^ 59
def prefixEnd_7125311 : Nat := 4983230072969 + 3 ^ 40 * 7125311 * 2
def baseEnd_7125311 : Nat := 135507753917343589690511

theorem tailTrace_7125311 : CollatzResearch.WordTrace tailWord_7125311 prefixEnd_7125311 135507753917343589690511 := by
  unfold tailWord_7125311
  simp only [CollatzResearch.WordTrace]
  refine ⟨259881442289222628081055787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173254294859481752054037191 259881442289222628081055787)
  ·
    refine ⟨389822163433833942121583681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259881442289222628081055787 389822163433833942121583681)
    ·
      refine ⟨292366622575375456591187761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389822163433833942121583681 292366622575375456591187761)
      ·
        refine ⟨219274966931531592443390821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292366622575375456591187761 219274966931531592443390821)
        ·
          refine ⟨41114056299662173583135779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219274966931531592443390821 41114056299662173583135779)
          ·
            refine ⟨61671084449493260374703669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41114056299662173583135779 61671084449493260374703669)
            ·
              refine ⟨5781664167139993160128469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61671084449493260374703669 5781664167139993160128469)
              ·
                refine ⟨135507753917343589690511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5781664167139993160128469 135507753917343589690511)
                ·
                  rfl

theorem cell23_7125311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 7].length) (baseStart_7125311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125311 prefixEnd_7125311 := by exact prefixLift 7125311
  have htrace : WordTrace (prefixWord ++ tailWord_7125311) baseStart_7125311 baseEnd_7125311 := by
    simpa [prefixWord, tailWord_7125311, baseEnd_7125311] using wordTrace_append hprefix tailTrace_7125311
  have hstable : (prefixWord ++ tailWord_7125311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125311).length < 2 ^ (prefixWord ++ tailWord_7125311).sum := by decide
  have hdescent : baseEnd_7125311 < baseStart_7125311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125381 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 1, 6, 3]
def baseStart_7125381 : Nat := 118140960795 + 7125381 * 2 ^ 59
def prefixEnd_7125381 : Nat := 4983230072969 + 3 ^ 40 * 7125381 * 2
def baseEnd_7125381 : Nat := 3658745299414091647768475

theorem tailTrace_7125381 : CollatzResearch.WordTrace tailWord_7125381 prefixEnd_7125381 3658745299414091647768475 := by
  unfold tailWord_7125381
  simp only [CollatzResearch.WordTrace]
  refine ⟨259883995398969030036103997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173255996932646020024069331 259883995398969030036103997)
  ·
    refine ⟨97456498274613386263538999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259883995398969030036103997 97456498274613386263538999)
    ·
      refine ⟨146184747411920079395308499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97456498274613386263538999 146184747411920079395308499)
      ·
        refine ⟨219277121117880119092962749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146184747411920079395308499 219277121117880119092962749)
        ·
          refine ⟨82228920419205044659861031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219277121117880119092962749 82228920419205044659861031)
          ·
            refine ⟨123343380628807566989791547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82228920419205044659861031 123343380628807566989791547)
            ·
              refine ⟨185015070943211350484687321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123343380628807566989791547 185015070943211350484687321)
              ·
                refine ⟨138761303207408512863515491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185015070943211350484687321 138761303207408512863515491)
                ·
                  refine ⟨208141954811112769295273237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138761303207408512863515491 208141954811112769295273237)
                  ·
                    refine ⟨9756654131770911060715933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 208141954811112769295273237 9756654131770911060715933)
                    ·
                      refine ⟨3658745299414091647768475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9756654131770911060715933 3658745299414091647768475)
                      ·
                        rfl

theorem cell23_7125381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_7125381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125381 prefixEnd_7125381 := by exact prefixLift 7125381
  have htrace : WordTrace (prefixWord ++ tailWord_7125381) baseStart_7125381 baseEnd_7125381 := by
    simpa [prefixWord, tailWord_7125381, baseEnd_7125381] using wordTrace_append hprefix tailTrace_7125381
  have hstable : (prefixWord ++ tailWord_7125381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125381).length < 2 ^ (prefixWord ++ tailWord_7125381).sum := by decide
  have hdescent : baseEnd_7125381 < baseStart_7125381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125406 : List Nat := [4, 3, 1, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_7125406 : Nat := 118140960795 + 7125406 * 2 ^ 59
def prefixEnd_7125406 : Nat := 4983230072969 + 3 ^ 40 * 7125406 * 2
def baseEnd_7125406 : Nat := 3658758136430454049955861

theorem tailTrace_7125406 : CollatzResearch.WordTrace tailWord_7125406 prefixEnd_7125406 3658758136430454049955861 := by
  unfold tailWord_7125406
  simp only [CollatzResearch.WordTrace]
  refine ⟨32485613402984807413220509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173256604815918972870509381 32485613402984807413220509)
  ·
    refine ⟨12182105026119302779957691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32485613402984807413220509 12182105026119302779957691)
    ·
      refine ⟨18273157539178954169936537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12182105026119302779957691 18273157539178954169936537)
      ·
        refine ⟨13704868154384215627452403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18273157539178954169936537 13704868154384215627452403)
        ·
          refine ⟨20557302231576323441178605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13704868154384215627452403 20557302231576323441178605)
          ·
            refine ⟨7708988336841121290441977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20557302231576323441178605 7708988336841121290441977)
            ·
              refine ⟨5781741252630840967831483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7708988336841121290441977 5781741252630840967831483)
              ·
                refine ⟨8672611878946261451747225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5781741252630840967831483 8672611878946261451747225)
                ·
                  refine ⟨6504458909209696088810419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8672611878946261451747225 6504458909209696088810419)
                  ·
                    refine ⟨9756688363814544133215629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6504458909209696088810419 9756688363814544133215629)
                    ·
                      refine ⟨3658758136430454049955861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9756688363814544133215629 3658758136430454049955861)
                      ·
                        rfl

theorem cell23_7125406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_7125406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125406 prefixEnd_7125406 := by exact prefixLift 7125406
  have htrace : WordTrace (prefixWord ++ tailWord_7125406) baseStart_7125406 baseEnd_7125406 := by
    simpa [prefixWord, tailWord_7125406, baseEnd_7125406] using wordTrace_append hprefix tailTrace_7125406
  have hstable : (prefixWord ++ tailWord_7125406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125406).length < 2 ^ (prefixWord ++ tailWord_7125406).sum := by decide
  have hdescent : baseEnd_7125406 < baseStart_7125406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125448 : List Nat := [2, 1, 3, 1, 3, 2, 2, 2, 2, 5]
def baseStart_7125448 : Nat := 118140960795 + 7125448 * 2 ^ 59
def prefixEnd_7125448 : Nat := 4983230072969 + 3 ^ 40 * 7125448 * 2
def baseEnd_7125448 : Nat := 1219593234205980961876889

theorem tailTrace_7125448 : CollatzResearch.WordTrace tailWord_7125448 prefixEnd_7125448 1219593234205980961876889 := by
  unfold tailWord_7125448
  simp only [CollatzResearch.WordTrace]
  refine ⟨129943219544863150239396499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173257626059817533652528665 129943219544863150239396499)
  ·
    refine ⟨194914829317294725359094749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129943219544863150239396499 194914829317294725359094749)
    ·
      refine ⟨73093060993985522009660531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194914829317294725359094749 73093060993985522009660531)
      ·
        refine ⟨109639591490978283014490797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73093060993985522009660531 109639591490978283014490797)
        ·
          refine ⟨41114846809116856130434049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109639591490978283014490797 41114846809116856130434049)
          ·
            refine ⟨30836135106837642097825537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41114846809116856130434049 30836135106837642097825537)
            ·
              refine ⟨23127101330128231573369153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30836135106837642097825537 23127101330128231573369153)
              ·
                refine ⟨17345325997596173680026865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23127101330128231573369153 17345325997596173680026865)
                ·
                  refine ⟨13008994498197130260020149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17345325997596173680026865 13008994498197130260020149)
                  ·
                    refine ⟨1219593234205980961876889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13008994498197130260020149 1219593234205980961876889)
                    ·
                      rfl

theorem cell23_7125448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_7125448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125448 prefixEnd_7125448 := by exact prefixLift 7125448
  have htrace : WordTrace (prefixWord ++ tailWord_7125448) baseStart_7125448 baseEnd_7125448 := by
    simpa [prefixWord, tailWord_7125448, baseEnd_7125448] using wordTrace_append hprefix tailTrace_7125448
  have hstable : (prefixWord ++ tailWord_7125448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125448).length < 2 ^ (prefixWord ++ tailWord_7125448).sum := by decide
  have hdescent : baseEnd_7125448 < baseStart_7125448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125451 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 4]
def baseStart_7125451 : Nat := 118140960795 + 7125451 * 2 ^ 59
def prefixEnd_7125451 : Nat := 4983230072969 + 3 ^ 40 * 7125451 * 2
def baseEnd_7125451 : Nat := 3658781243059906373893153

theorem tailTrace_7125451 : CollatzResearch.WordTrace tailWord_7125451 prefixEnd_7125451 3658781243059906373893153 := by
  unfold tailWord_7125451
  simp only [CollatzResearch.WordTrace]
  refine ⟨259886548508715431991152207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173257699005810287994101471 259886548508715431991152207)
  ·
    refine ⟨389829822763073147986728311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259886548508715431991152207 389829822763073147986728311)
    ·
      refine ⟨584744734144609721980092467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389829822763073147986728311 584744734144609721980092467)
      ·
        refine ⟨877117101216914582970138701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584744734144609721980092467 877117101216914582970138701)
        ·
          refine ⟨328918912956342968613802013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 877117101216914582970138701 328918912956342968613802013)
          ·
            refine ⟨123344592358628613230175755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328918912956342968613802013 123344592358628613230175755)
            ·
              refine ⟨185016888537942919845263633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123344592358628613230175755 185016888537942919845263633)
              ·
                refine ⟨138762666403457189883947725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185016888537942919845263633 138762666403457189883947725)
                ·
                  refine ⟨52035999901296446206480397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138762666403457189883947725 52035999901296446206480397)
                  ·
                    refine ⟨19513499962986167327430149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52035999901296446206480397 19513499962986167327430149)
                    ·
                      refine ⟨3658781243059906373893153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19513499962986167327430149 3658781243059906373893153)
                      ·
                        rfl

theorem cell23_7125451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 4].length) (baseStart_7125451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125451 prefixEnd_7125451 := by exact prefixLift 7125451
  have htrace : WordTrace (prefixWord ++ tailWord_7125451) baseStart_7125451 baseEnd_7125451 := by
    simpa [prefixWord, tailWord_7125451, baseEnd_7125451] using wordTrace_append hprefix tailTrace_7125451
  have hstable : (prefixWord ++ tailWord_7125451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125451).length < 2 ^ (prefixWord ++ tailWord_7125451).sum := by decide
  have hdescent : baseEnd_7125451 < baseStart_7125451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125481 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 1, 6, 4]
def baseStart_7125481 : Nat := 118140960795 + 7125481 * 2 ^ 59
def prefixEnd_7125481 : Nat := 4983230072969 + 3 ^ 40 * 7125481 * 2
def baseEnd_7125481 : Nat := 3658796647479541256518015

theorem tailTrace_7125481 : CollatzResearch.WordTrace tailWord_7125481 prefixEnd_7125481 3658796647479541256518015 := by
  unfold tailWord_7125481
  simp only [CollatzResearch.WordTrace]
  refine ⟨259887642698606747114744297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173258428465737831409829531 259887642698606747114744297)
  ·
    refine ⟨194915732023955060336058223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259887642698606747114744297 194915732023955060336058223)
    ·
      refine ⟨292373598035932590504087335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194915732023955060336058223 292373598035932590504087335)
      ·
        refine ⟨438560397053898885756131003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292373598035932590504087335 438560397053898885756131003)
        ·
          refine ⟨657840595580848328634196505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438560397053898885756131003 657840595580848328634196505)
          ·
            refine ⟨493380446685636246475647379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657840595580848328634196505 493380446685636246475647379)
            ·
              refine ⟨740070670028454369713471069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493380446685636246475647379 740070670028454369713471069)
              ·
                refine ⟨277526501260670388642551651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 740070670028454369713471069 277526501260670388642551651)
                ·
                  refine ⟨416289751891005582963827477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277526501260670388642551651 416289751891005582963827477)
                  ·
                    refine ⟨19513582119890886701429413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 416289751891005582963827477 19513582119890886701429413)
                    ·
                      refine ⟨3658796647479541256518015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19513582119890886701429413 3658796647479541256518015)
                      ·
                        rfl

theorem cell23_7125481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_7125481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125481 prefixEnd_7125481 := by exact prefixLift 7125481
  have htrace : WordTrace (prefixWord ++ tailWord_7125481) baseStart_7125481 baseEnd_7125481 := by
    simpa [prefixWord, tailWord_7125481, baseEnd_7125481] using wordTrace_append hprefix tailTrace_7125481
  have hstable : (prefixWord ++ tailWord_7125481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125481).length < 2 ^ (prefixWord ++ tailWord_7125481).sum := by decide
  have hdescent : baseEnd_7125481 < baseStart_7125481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125485 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_7125485 : Nat := 118140960795 + 7125485 * 2 ^ 59
def prefixEnd_7125485 : Nat := 4983230072969 + 3 ^ 40 * 7125485 * 2
def baseEnd_7125485 : Nat := 3658798701402159240867997

theorem tailTrace_7125485 : CollatzResearch.WordTrace tailWord_7125485 prefixEnd_7125485 3658798701402159240867997 := by
  unfold tailWord_7125485
  simp only [CollatzResearch.WordTrace]
  refine ⟨259887788590592255797889909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173258525727061503865259939 259887788590592255797889909)
  ·
    refine ⟨24364480180368023981052179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 259887788590592255797889909 24364480180368023981052179)
    ·
      refine ⟨36546720270552035971578269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24364480180368023981052179 36546720270552035971578269)
      ·
        refine ⟨13705020101457013489341851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36546720270552035971578269 13705020101457013489341851)
        ·
          refine ⟨20557530152185520234012777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13705020101457013489341851 20557530152185520234012777)
          ·
            refine ⟨15418147614139140175509583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20557530152185520234012777 15418147614139140175509583)
            ·
              refine ⟨23127221421208710263264375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15418147614139140175509583 23127221421208710263264375)
              ·
                refine ⟨34690832131813065394896563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23127221421208710263264375 34690832131813065394896563)
                ·
                  refine ⟨52036248197719598092344845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34690832131813065394896563 52036248197719598092344845)
                  ·
                    refine ⟨19513593074144849284629317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52036248197719598092344845 19513593074144849284629317)
                    ·
                      refine ⟨3658798701402159240867997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19513593074144849284629317 3658798701402159240867997)
                      ·
                        rfl

theorem cell23_7125485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_7125485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125485 prefixEnd_7125485 := by exact prefixLift 7125485
  have htrace : WordTrace (prefixWord ++ tailWord_7125485) baseStart_7125485 baseEnd_7125485 := by
    simpa [prefixWord, tailWord_7125485, baseEnd_7125485] using wordTrace_append hprefix tailTrace_7125485
  have hstable : (prefixWord ++ tailWord_7125485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125485).length < 2 ^ (prefixWord ++ tailWord_7125485).sum := by decide
  have hdescent : baseEnd_7125485 < baseStart_7125485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125488 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 3]
def baseStart_7125488 : Nat := 118140960795 + 7125488 * 2 ^ 59
def prefixEnd_7125488 : Nat := 4983230072969 + 3 ^ 40 * 7125488 * 2
def baseEnd_7125488 : Nat := 3658800241844122729130483

theorem tailTrace_7125488 : CollatzResearch.WordTrace tailWord_7125488 prefixEnd_7125488 3658800241844122729130483 := by
  unfold tailWord_7125488
  simp only [CollatzResearch.WordTrace]
  refine ⟨129943949004790693655124559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173258598673054258206832745 129943949004790693655124559)
  ·
    refine ⟨194915923507186040482686839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129943949004790693655124559 194915923507186040482686839)
    ·
      refine ⟨292373885260779060724030259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194915923507186040482686839 292373885260779060724030259)
      ·
        refine ⟨438560827891168591086045389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292373885260779060724030259 438560827891168591086045389)
        ·
          refine ⟨164460310459188221657267021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 438560827891168591086045389 164460310459188221657267021)
          ·
            refine ⟨61672616422195583121475133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164460310459188221657267021 61672616422195583121475133)
            ·
              refine ⟨23127231158323343670553175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61672616422195583121475133 23127231158323343670553175)
              ·
                refine ⟨34690846737485015505829763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23127231158323343670553175 34690846737485015505829763)
                ·
                  refine ⟨52036270106227523258744645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34690846737485015505829763 52036270106227523258744645)
                  ·
                    refine ⟨9756800644917660611014621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52036270106227523258744645 9756800644917660611014621)
                    ·
                      refine ⟨3658800241844122729130483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9756800644917660611014621 3658800241844122729130483)
                      ·
                        rfl

theorem cell23_7125488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 3].length) (baseStart_7125488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125488 prefixEnd_7125488 := by exact prefixLift 7125488
  have htrace : WordTrace (prefixWord ++ tailWord_7125488) baseStart_7125488 baseEnd_7125488 := by
    simpa [prefixWord, tailWord_7125488, baseEnd_7125488] using wordTrace_append hprefix tailTrace_7125488
  have hstable : (prefixWord ++ tailWord_7125488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125488).length < 2 ^ (prefixWord ++ tailWord_7125488).sum := by decide
  have hdescent : baseEnd_7125488 < baseStart_7125488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125491 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 8]
def baseStart_7125491 : Nat := 118140960795 + 7125491 * 2 ^ 59
def prefixEnd_7125491 : Nat := 4983230072969 + 3 ^ 40 * 7125491 * 2
def baseEnd_7125491 : Nat := 406533531365120690821441

theorem tailTrace_7125491 : CollatzResearch.WordTrace tailWord_7125491 prefixEnd_7125491 406533531365120690821441 := by
  unfold tailWord_7125491
  simp only [CollatzResearch.WordTrace]
  refine ⟨259888007428570518822608327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173258671619047012548405551 259888007428570518822608327)
  ·
    refine ⟨389832011142855778233912491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259888007428570518822608327 389832011142855778233912491)
    ·
      refine ⟨584748016714283667350868737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389832011142855778233912491 584748016714283667350868737)
      ·
        refine ⟨438561012535712750513151553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 584748016714283667350868737 438561012535712750513151553)
        ·
          refine ⟨328920759401784562884863665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438561012535712750513151553 328920759401784562884863665)
          ·
            refine ⟨246690569551338422163647749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328920759401784562884863665 246690569551338422163647749)
            ·
              refine ⟨46254481790875954155683953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246690569551338422163647749 46254481790875954155683953)
              ·
                refine ⟨34690861343156965616762965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46254481790875954155683953 34690861343156965616762965)
                ·
                  refine ⟨406533531365120690821441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34690861343156965616762965 406533531365120690821441)
                  ·
                    rfl

theorem cell23_7125491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 8].length) (baseStart_7125491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125491 prefixEnd_7125491 := by exact prefixLift 7125491
  have htrace : WordTrace (prefixWord ++ tailWord_7125491) baseStart_7125491 baseEnd_7125491 := by
    simpa [prefixWord, tailWord_7125491, baseEnd_7125491] using wordTrace_append hprefix tailTrace_7125491
  have hstable : (prefixWord ++ tailWord_7125491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125491).length < 2 ^ (prefixWord ++ tailWord_7125491).sum := by decide
  have hdescent : baseEnd_7125491 < baseStart_7125491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125521 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 2, 9]
def baseStart_7125521 : Nat := 118140960795 + 7125521 * 2 ^ 59
def prefixEnd_7125521 : Nat := 4983230072969 + 3 ^ 40 * 7125521 * 2
def baseEnd_7125521 : Nat := 1219605728901907033339277

theorem tailTrace_7125521 : CollatzResearch.WordTrace tailWord_7125521 prefixEnd_7125521 1219605728901907033339277 := by
  unfold tailWord_7125521
  simp only [CollatzResearch.WordTrace]
  refine ⟨259889101618461833946200417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173259401078974555964133611 259889101618461833946200417)
  ·
    refine ⟨194916826213846375459650313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259889101618461833946200417 194916826213846375459650313)
    ·
      refine ⟨146187619660384781594737735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194916826213846375459650313 146187619660384781594737735)
      ·
        refine ⟨219281429490577172392106603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146187619660384781594737735 219281429490577172392106603)
        ·
          refine ⟨328922144235865758588159905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219281429490577172392106603 328922144235865758588159905)
          ·
            refine ⟨246691608176899318941119929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328922144235865758588159905 246691608176899318941119929)
            ·
              refine ⟨185018706132674489205839947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246691608176899318941119929 185018706132674489205839947)
              ·
                refine ⟨277528059199011733808759921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185018706132674489205839947 277528059199011733808759921)
                ·
                  refine ⟨208146044399258800356569941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277528059199011733808759921 208146044399258800356569941)
                  ·
                    refine ⟨1219605728901907033339277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 208146044399258800356569941 1219605728901907033339277)
                    ·
                      rfl

theorem cell23_7125521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_7125521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125521 prefixEnd_7125521 := by exact prefixLift 7125521
  have htrace : WordTrace (prefixWord ++ tailWord_7125521) baseStart_7125521 baseEnd_7125521 := by
    simpa [prefixWord, tailWord_7125521, baseEnd_7125521] using wordTrace_append hprefix tailTrace_7125521
  have hstable : (prefixWord ++ tailWord_7125521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125521).length < 2 ^ (prefixWord ++ tailWord_7125521).sum := by decide
  have hdescent : baseEnd_7125521 < baseStart_7125521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125525 : List Nat := [1, 3, 2, 1, 3, 1, 5, 1, 6]
def baseStart_7125525 : Nat := 118140960795 + 7125525 * 2 ^ 59
def prefixEnd_7125525 : Nat := 4983230072969 + 3 ^ 40 * 7125525 * 2
def baseEnd_7125525 : Nat := 406535471180926564929757

theorem tailTrace_7125525 : CollatzResearch.WordTrace tailWord_7125525 prefixEnd_7125525 406535471180926564929757 := by
  unfold tailWord_7125525
  simp only [CollatzResearch.WordTrace]
  refine ⟨259889247510447342629346029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173259498340298228419564019 259889247510447342629346029)
  ·
    refine ⟨97458467816417753486004761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259889247510447342629346029 97458467816417753486004761)
    ·
      refine ⟨73093850862313315114503571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97458467816417753486004761 73093850862313315114503571)
      ·
        refine ⟨109640776293469972671755357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73093850862313315114503571 109640776293469972671755357)
        ·
          refine ⟨41115291110051239751908259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109640776293469972671755357 41115291110051239751908259)
          ·
            refine ⟨61672936665076859627862389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41115291110051239751908259 61672936665076859627862389)
            ·
              refine ⟨5781837812350955590112099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61672936665076859627862389 5781837812350955590112099)
              ·
                refine ⟨8672756718526433385168149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5781837812350955590112099 8672756718526433385168149)
                ·
                  refine ⟨406535471180926564929757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8672756718526433385168149 406535471180926564929757)
                  ·
                    rfl

theorem cell23_7125525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 6].length) (baseStart_7125525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125525 prefixEnd_7125525 := by exact prefixLift 7125525
  have htrace : WordTrace (prefixWord ++ tailWord_7125525) baseStart_7125525 baseEnd_7125525 := by
    simpa [prefixWord, tailWord_7125525, baseEnd_7125525] using wordTrace_append hprefix tailTrace_7125525
  have hstable : (prefixWord ++ tailWord_7125525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125525).length < 2 ^ (prefixWord ++ tailWord_7125525).sum := by decide
  have hdescent : baseEnd_7125525 < baseStart_7125525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125562 : List Nat := [3, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2]
def baseStart_7125562 : Nat := 118140960795 + 7125562 * 2 ^ 59
def prefixEnd_7125562 : Nat := 4983230072969 + 3 ^ 40 * 7125562 * 2
def baseEnd_7125562 : Nat := 3658838239412555439605143

theorem tailTrace_7125562 : CollatzResearch.WordTrace tailWord_7125562 prefixEnd_7125562 3658838239412555439605143 := by
  unfold tailWord_7125562
  simp only [CollatzResearch.WordTrace]
  refine ⟨64972649252828324487110735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173260398007542198632295293 64972649252828324487110735)
  ·
    refine ⟨97458973879242486730666103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64972649252828324487110735 97458973879242486730666103)
    ·
      refine ⟨146188460818863730095999155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97458973879242486730666103 146188460818863730095999155)
      ·
        refine ⟨219282691228295595143998733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146188460818863730095999155 219282691228295595143998733)
        ·
          refine ⟨82231009210610848178999525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219282691228295595143998733 82231009210610848178999525)
          ·
            refine ⟨15418314226989534033562411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82231009210610848178999525 15418314226989534033562411)
            ·
              refine ⟨23127471340484301050343617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15418314226989534033562411 23127471340484301050343617)
              ·
                refine ⟨17345603505363225787757713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23127471340484301050343617 17345603505363225787757713)
                ·
                  refine ⟨13009202629022419340818285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17345603505363225787757713 13009202629022419340818285)
                  ·
                    refine ⟨4878450985883407252806857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13009202629022419340818285 4878450985883407252806857)
                    ·
                      refine ⟨3658838239412555439605143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4878450985883407252806857 3658838239412555439605143)
                      ·
                        rfl

theorem cell23_7125562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2].length) (baseStart_7125562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125562 prefixEnd_7125562 := by exact prefixLift 7125562
  have htrace : WordTrace (prefixWord ++ tailWord_7125562) baseStart_7125562 baseEnd_7125562 := by
    simpa [prefixWord, tailWord_7125562, baseEnd_7125562] using wordTrace_append hprefix tailTrace_7125562
  have hstable : (prefixWord ++ tailWord_7125562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125562).length < 2 ^ (prefixWord ++ tailWord_7125562).sum := by decide
  have hdescent : baseEnd_7125562 < baseStart_7125562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125569 : List Nat := [1, 2, 5, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_7125569 : Nat := 118140960795 + 7125569 * 2 ^ 59
def prefixEnd_7125569 : Nat := 4983230072969 + 3 ^ 40 * 7125569 * 2
def baseEnd_7125569 : Nat := 3658841833777136912217611

theorem tailTrace_7125569 : CollatzResearch.WordTrace tailWord_7125569 prefixEnd_7125569 3658841833777136912217611 := by
  unfold tailWord_7125569
  simp only [CollatzResearch.WordTrace]
  refine ⟨259890852322287938143947761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173260568214858625429298507 259890852322287938143947761)
  ·
    refine ⟨194918139241715953607960821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259890852322287938143947761 194918139241715953607960821)
    ·
      refine ⟨18273575553910870650746327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194918139241715953607960821 18273575553910870650746327)
      ·
        refine ⟨27410363330866305976119491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18273575553910870650746327 27410363330866305976119491)
        ·
          refine ⟨41115544996299458964179237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27410363330866305976119491 41115544996299458964179237)
          ·
            refine ⟨7709164686806148555783607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41115544996299458964179237 7709164686806148555783607)
            ·
              refine ⟨11563747030209222833675411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7709164686806148555783607 11563747030209222833675411)
              ·
                refine ⟨17345620545313834250513117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11563747030209222833675411 17345620545313834250513117)
                ·
                  refine ⟨6504607704492687843942419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17345620545313834250513117 6504607704492687843942419)
                  ·
                    refine ⟨9756911556739031765913629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6504607704492687843942419 9756911556739031765913629)
                    ·
                      refine ⟨3658841833777136912217611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9756911556739031765913629 3658841833777136912217611)
                      ·
                        rfl

theorem cell23_7125569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_7125569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125569 prefixEnd_7125569 := by exact prefixLift 7125569
  have htrace : WordTrace (prefixWord ++ tailWord_7125569) baseStart_7125569 baseEnd_7125569 := by
    simpa [prefixWord, tailWord_7125569, baseEnd_7125569] using wordTrace_append hprefix tailTrace_7125569
  have hstable : (prefixWord ++ tailWord_7125569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125569).length < 2 ^ (prefixWord ++ tailWord_7125569).sum := by decide
  have hdescent : baseEnd_7125569 < baseStart_7125569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125592 : List Nat := [2, 1, 2, 2, 1, 2, 2, 4, 3, 2, 2]
def baseStart_7125592 : Nat := 118140960795 + 7125592 * 2 ^ 59
def prefixEnd_7125592 : Nat := 4983230072969 + 3 ^ 40 * 7125592 * 2
def baseEnd_7125592 : Nat := 3658853643832190322230005

theorem tailTrace_7125592 : CollatzResearch.WordTrace tailWord_7125592 prefixEnd_7125592 3658853643832190322230005 := by
  unfold tailWord_7125592
  simp only [CollatzResearch.WordTrace]
  refine ⟨129945845600602306536017515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173261127467469742048023353 129945845600602306536017515)
  ·
    refine ⟨194918768400903459804026273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129945845600602306536017515 194918768400903459804026273)
    ·
      refine ⟨146189076300677594853019705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194918768400903459804026273 146189076300677594853019705)
      ·
        refine ⟨109641807225508196139764779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146189076300677594853019705 109641807225508196139764779)
        ·
          refine ⟨164462710838262294209647169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109641807225508196139764779 164462710838262294209647169)
          ·
            refine ⟨123347033128696720657235377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164462710838262294209647169 123347033128696720657235377)
            ·
              refine ⟨92510274846522540492926533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123347033128696720657235377 92510274846522540492926533)
              ·
                refine ⟨17345676533722976342423725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92510274846522540492926533 17345676533722976342423725)
                ·
                  refine ⟨6504628700146116128408897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17345676533722976342423725 6504628700146116128408897)
                  ·
                    refine ⟨4878471525109587096306673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6504628700146116128408897 4878471525109587096306673)
                    ·
                      refine ⟨3658853643832190322230005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4878471525109587096306673 3658853643832190322230005)
                      ·
                        rfl

theorem cell23_7125592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_7125592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125592 prefixEnd_7125592 := by exact prefixLift 7125592
  have htrace : WordTrace (prefixWord ++ tailWord_7125592) baseStart_7125592 baseEnd_7125592 := by
    simpa [prefixWord, tailWord_7125592, baseEnd_7125592] using wordTrace_append hprefix tailTrace_7125592
  have hstable : (prefixWord ++ tailWord_7125592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125592).length < 2 ^ (prefixWord ++ tailWord_7125592).sum := by decide
  have hdescent : baseEnd_7125592 < baseStart_7125592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125609 : List Nat := [1, 2, 1, 1, 1, 4, 1, 7, 1, 2, 2]
def baseStart_7125609 : Nat := 118140960795 + 7125609 * 2 ^ 59
def prefixEnd_7125609 : Nat := 4983230072969 + 3 ^ 40 * 7125609 * 2
def baseEnd_7125609 : Nat := 3658862373003316755717427

theorem tailTrace_7125609 : CollatzResearch.WordTrace tailWord_7125609 prefixEnd_7125609 3658862373003316755717427 := by
  unfold tailWord_7125609
  simp only [CollatzResearch.WordTrace]
  refine ⟨259892311242143024975403881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173261540828095349983602587 259892311242143024975403881)
  ·
    refine ⟨194919233431607268731552911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259892311242143024975403881 194919233431607268731552911)
    ·
      refine ⟨292378850147410903097329367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194919233431607268731552911 292378850147410903097329367)
      ·
        refine ⟨438568275221116354645994051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292378850147410903097329367 438568275221116354645994051)
        ·
          refine ⟨657852412831674531968991077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438568275221116354645994051 657852412831674531968991077)
          ·
            refine ⟨123347327405938974744185827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 657852412831674531968991077 123347327405938974744185827)
            ·
              refine ⟨185020991108908462116278741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123347327405938974744185827 185020991108908462116278741)
              ·
                refine ⟨4336429479115042080850283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 185020991108908462116278741 4336429479115042080850283)
                ·
                  refine ⟨6504644218672563121275425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4336429479115042080850283 6504644218672563121275425)
                  ·
                    refine ⟨4878483164004422340956569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6504644218672563121275425 4878483164004422340956569)
                    ·
                      refine ⟨3658862373003316755717427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4878483164004422340956569 3658862373003316755717427)
                      ·
                        rfl

theorem cell23_7125609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 1, 2, 2].length) (baseStart_7125609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125609 prefixEnd_7125609 := by exact prefixLift 7125609
  have htrace : WordTrace (prefixWord ++ tailWord_7125609) baseStart_7125609 baseEnd_7125609 := by
    simpa [prefixWord, tailWord_7125609, baseEnd_7125609] using wordTrace_append hprefix tailTrace_7125609
  have hstable : (prefixWord ++ tailWord_7125609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125609).length < 2 ^ (prefixWord ++ tailWord_7125609).sum := by decide
  have hdescent : baseEnd_7125609 < baseStart_7125609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125628 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 2, 7]
def baseStart_7125628 : Nat := 118140960795 + 7125628 * 2 ^ 59
def prefixEnd_7125628 : Nat := 4983230072969 + 3 ^ 40 * 7125628 * 2
def baseEnd_7125628 : Nat := 1219624043045250727126613

theorem tailTrace_7125628 : CollatzResearch.WordTrace tailWord_7125628 prefixEnd_7125628 1219624043045250727126613 := by
  unfold tailWord_7125628
  simp only [CollatzResearch.WordTrace]
  refine ⟨129946502114537095610172769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173262002819382794146897025 129946502114537095610172769)
  ·
    refine ⟨97459876585902821707629577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129946502114537095610172769 97459876585902821707629577)
    ·
      refine ⟨73094907439427116280722183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97459876585902821707629577 73094907439427116280722183)
      ·
        refine ⟨109642361159140674421083275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73094907439427116280722183 109642361159140674421083275)
        ·
          refine ⟨164463541738711011631624913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109642361159140674421083275 164463541738711011631624913)
          ·
            refine ⟨123347656304033258723718685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164463541738711011631624913 123347656304033258723718685)
            ·
              refine ⟨46255371114012472021394507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123347656304033258723718685 46255371114012472021394507)
              ·
                refine ⟨69383056671018708032091761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46255371114012472021394507 69383056671018708032091761)
                ·
                  refine ⟨52037292503264031024068821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69383056671018708032091761 52037292503264031024068821)
                  ·
                    refine ⟨1219624043045250727126613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52037292503264031024068821 1219624043045250727126613)
                    ·
                      rfl

theorem cell23_7125628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_7125628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125628 prefixEnd_7125628 := by exact prefixLift 7125628
  have htrace : WordTrace (prefixWord ++ tailWord_7125628) baseStart_7125628 baseEnd_7125628 := by
    simpa [prefixWord, tailWord_7125628, baseEnd_7125628] using wordTrace_append hprefix tailTrace_7125628
  have hstable : (prefixWord ++ tailWord_7125628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125628).length < 2 ^ (prefixWord ++ tailWord_7125628).sum := by decide
  have hdescent : baseEnd_7125628 < baseStart_7125628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125695 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 4]
def baseStart_7125695 : Nat := 118140960795 + 7125695 * 2 ^ 59
def prefixEnd_7125695 : Nat := 4983230072969 + 3 ^ 40 * 7125695 * 2
def baseEnd_7125695 : Nat := 3658906532339603419242031

theorem tailTrace_7125695 : CollatzResearch.WordTrace tailWord_7125695 prefixEnd_7125695 3658906532339603419242031 := by
  unfold tailWord_7125695
  simp only [CollatzResearch.WordTrace]
  refine ⟨259895447919831461663034539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173263631946554307775356359 259895447919831461663034539)
  ·
    refine ⟨389843171879747192494551809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259895447919831461663034539 389843171879747192494551809)
    ·
      refine ⟨292382378909810394370913857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389843171879747192494551809 292382378909810394370913857)
      ·
        refine ⟨219286784182357795778185393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292382378909810394370913857 219286784182357795778185393)
        ·
          refine ⟨164465088136768346833639045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219286784182357795778185393 164465088136768346833639045)
          ·
            refine ⟨30837204025644065031307321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164465088136768346833639045 30837204025644065031307321)
            ·
              refine ⟨23127903019233048773480491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30837204025644065031307321 23127903019233048773480491)
              ·
                refine ⟨34691854528849573160220737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23127903019233048773480491 34691854528849573160220737)
                ·
                  refine ⟨26018890896637179870165553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34691854528849573160220737 26018890896637179870165553)
                  ·
                    refine ⟨19514168172477884902624165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26018890896637179870165553 19514168172477884902624165)
                    ·
                      refine ⟨3658906532339603419242031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19514168172477884902624165 3658906532339603419242031)
                      ·
                        rfl

theorem cell23_7125695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_7125695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125695 prefixEnd_7125695 := by exact prefixLift 7125695
  have htrace : WordTrace (prefixWord ++ tailWord_7125695) baseStart_7125695 baseEnd_7125695 := by
    simpa [prefixWord, tailWord_7125695, baseEnd_7125695] using wordTrace_append hprefix tailTrace_7125695
  have hstable : (prefixWord ++ tailWord_7125695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125695).length < 2 ^ (prefixWord ++ tailWord_7125695).sum := by decide
  have hdescent : baseEnd_7125695 < baseStart_7125695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125745 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 1, 2, 5]
def baseStart_7125745 : Nat := 118140960795 + 7125745 * 2 ^ 59
def prefixEnd_7125745 : Nat := 4983230072969 + 3 ^ 40 * 7125745 * 2
def baseEnd_7125745 : Nat := 3658932206372328223616801

theorem tailTrace_7125745 : CollatzResearch.WordTrace tailWord_7125745 prefixEnd_7125745 3658932206372328223616801 := by
  unfold tailWord_7125745
  simp only [CollatzResearch.WordTrace]
  refine ⟨259897271569650320202354689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173264847713100213468236459 259897271569650320202354689)
  ·
    refine ⟨194922953677237740151766017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259897271569650320202354689 194922953677237740151766017)
    ·
      refine ⟨146192215257928305113824513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194922953677237740151766017 146192215257928305113824513)
      ·
        refine ⟨109644161443446228835368385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146192215257928305113824513 109644161443446228835368385)
        ·
          refine ⟨82233121082584671626526289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109644161443446228835368385 82233121082584671626526289)
          ·
            refine ⟨61674840811938503719894717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82233121082584671626526289 61674840811938503719894717)
            ·
              refine ⟨23128065304476938894960519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61674840811938503719894717 23128065304476938894960519)
              ·
                refine ⟨34692097956715408342440779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23128065304476938894960519 34692097956715408342440779)
                ·
                  refine ⟨52038146935073112513661169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34692097956715408342440779 52038146935073112513661169)
                  ·
                    refine ⟨39028610201304834385245877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52038146935073112513661169 39028610201304834385245877)
                    ·
                      refine ⟨3658932206372328223616801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39028610201304834385245877 3658932206372328223616801)
                      ·
                        rfl

theorem cell23_7125745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_7125745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125745 prefixEnd_7125745 := by exact prefixLift 7125745
  have htrace : WordTrace (prefixWord ++ tailWord_7125745) baseStart_7125745 baseEnd_7125745 := by
    simpa [prefixWord, tailWord_7125745, baseEnd_7125745] using wordTrace_append hprefix tailTrace_7125745
  have hstable : (prefixWord ++ tailWord_7125745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125745).length < 2 ^ (prefixWord ++ tailWord_7125745).sum := by decide
  have hdescent : baseEnd_7125745 < baseStart_7125745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125772 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 4, 4, 2]
def baseStart_7125772 : Nat := 118140960795 + 7125772 * 2 ^ 59
def prefixEnd_7125772 : Nat := 4983230072969 + 3 ^ 40 * 7125772 * 2
def baseEnd_7125772 : Nat := 3658946070349999617979177

theorem tailTrace_7125772 : CollatzResearch.WordTrace tailWord_7125772 prefixEnd_7125772 3658946070349999617979177 := by
  unfold tailWord_7125772
  simp only [CollatzResearch.WordTrace]
  refine ⟨129949128170276251906793785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173265504227035002542391713 129949128170276251906793785)
  ·
    refine ⟨97461846127707188930095339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129949128170276251906793785 97461846127707188930095339)
    ·
      refine ⟨146192769191560783395143009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97461846127707188930095339 146192769191560783395143009)
      ·
        refine ⟨109644576893670587546357257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146192769191560783395143009 109644576893670587546357257)
        ·
          refine ⟨82233432670252940659767943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109644576893670587546357257 82233432670252940659767943)
          ·
            refine ⟨123350149005379410989651915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82233432670252940659767943 123350149005379410989651915)
            ·
              refine ⟨185025223508069116484477873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123350149005379410989651915 185025223508069116484477873)
              ·
                refine ⟨138768917631051837363358405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185025223508069116484477873 138768917631051837363358405)
                ·
                  refine ⟨26019172055822219505629701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138768917631051837363358405 26019172055822219505629701)
                  ·
                    refine ⟨4878594760466666157305569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26019172055822219505629701 4878594760466666157305569)
                    ·
                      refine ⟨3658946070349999617979177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4878594760466666157305569 3658946070349999617979177)
                      ·
                        rfl

theorem cell23_7125772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_7125772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125772 prefixEnd_7125772 := by exact prefixLift 7125772
  have htrace : WordTrace (prefixWord ++ tailWord_7125772) baseStart_7125772 baseEnd_7125772 := by
    simpa [prefixWord, tailWord_7125772, baseEnd_7125772] using wordTrace_append hprefix tailTrace_7125772
  have hstable : (prefixWord ++ tailWord_7125772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125772).length < 2 ^ (prefixWord ++ tailWord_7125772).sum := by decide
  have hdescent : baseEnd_7125772 < baseStart_7125772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125806 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_7125806 : Nat := 118140960795 + 7125806 * 2 ^ 59
def prefixEnd_7125806 : Nat := 4983230072969 + 3 ^ 40 * 7125806 * 2
def baseEnd_7125806 : Nat := 3658963528692252484954021

theorem tailTrace_7125806 : CollatzResearch.WordTrace tailWord_7125806 prefixEnd_7125806 3658963528692252484954021 := by
  unfold tailWord_7125806
  simp only [CollatzResearch.WordTrace]
  refine ⟨32487437052803665952540659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173266330948286218413550181 32487437052803665952540659)
  ·
    refine ⟨48731155579205498928810989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32487437052803665952540659 48731155579205498928810989)
    ·
      refine ⟨18274183342202062098304121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48731155579205498928810989 18274183342202062098304121)
      ·
        refine ⟨13705637506651546573728091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18274183342202062098304121 13705637506651546573728091)
        ·
          refine ⟨20558456259977319860592137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13705637506651546573728091 20558456259977319860592137)
          ·
            refine ⟨15418842194982989895444103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20558456259977319860592137 15418842194982989895444103)
            ·
              refine ⟨23128263292474484843166155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15418842194982989895444103 23128263292474484843166155)
              ·
                refine ⟨34692394938711727264749233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23128263292474484843166155 34692394938711727264749233)
                ·
                  refine ⟨26019296204033795448561925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34692394938711727264749233 26019296204033795448561925)
                  ·
                    refine ⟨4878618038256336646605361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26019296204033795448561925 4878618038256336646605361)
                    ·
                      refine ⟨3658963528692252484954021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4878618038256336646605361 3658963528692252484954021)
                      ·
                        rfl

theorem cell23_7125806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_7125806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125806 prefixEnd_7125806 := by exact prefixLift 7125806
  have htrace : WordTrace (prefixWord ++ tailWord_7125806) baseStart_7125806 baseEnd_7125806 := by
    simpa [prefixWord, tailWord_7125806, baseEnd_7125806] using wordTrace_append hprefix tailTrace_7125806
  have hstable : (prefixWord ++ tailWord_7125806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125806).length < 2 ^ (prefixWord ++ tailWord_7125806).sum := by decide
  have hdescent : baseEnd_7125806 < baseStart_7125806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125856 : List Nat := [2, 1, 1, 3, 3, 1, 1, 6, 1, 1, 3]
def baseStart_7125856 : Nat := 118140960795 + 7125856 * 2 ^ 59
def prefixEnd_7125856 : Nat := 4983230072969 + 3 ^ 40 * 7125856 * 2
def baseEnd_7125856 : Nat := 3658989202724977289328791

theorem tailTrace_7125856 : CollatzResearch.WordTrace tailWord_7125856 prefixEnd_7125856 3658989202724977289328791 := by
  unfold tailWord_7125856
  simp only [CollatzResearch.WordTrace]
  refine ⟨129950660036124093079822711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173267546714832124106430281 129950660036124093079822711)
  ·
    refine ⟨194925990054186139619734067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129950660036124093079822711 194925990054186139619734067)
    ·
      refine ⟨292388985081279209429601101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194925990054186139619734067 292388985081279209429601101)
      ·
        refine ⟨109645869405479703536100413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292388985081279209429601101 109645869405479703536100413)
        ·
          refine ⟨41117201027054888826037655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109645869405479703536100413 41117201027054888826037655)
          ·
            refine ⟨61675801540582333239056483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41117201027054888826037655 61675801540582333239056483)
            ·
              refine ⟨92513702310873499858584725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61675801540582333239056483 92513702310873499858584725)
              ·
                refine ⟨4336579795822195305871159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92513702310873499858584725 4336579795822195305871159)
                ·
                  refine ⟨6504869693733292958806739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4336579795822195305871159 6504869693733292958806739)
                  ·
                    refine ⟨9757304540599939438210109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6504869693733292958806739 9757304540599939438210109)
                    ·
                      refine ⟨3658989202724977289328791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9757304540599939438210109 3658989202724977289328791)
                      ·
                        rfl

theorem cell23_7125856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 1, 1, 3].length) (baseStart_7125856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125856 prefixEnd_7125856 := by exact prefixLift 7125856
  have htrace : WordTrace (prefixWord ++ tailWord_7125856) baseStart_7125856 baseEnd_7125856 := by
    simpa [prefixWord, tailWord_7125856, baseEnd_7125856] using wordTrace_append hprefix tailTrace_7125856
  have hstable : (prefixWord ++ tailWord_7125856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125856).length < 2 ^ (prefixWord ++ tailWord_7125856).sum := by decide
  have hdescent : baseEnd_7125856 < baseStart_7125856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125872 : List Nat := [2, 1, 1, 1, 4, 1, 5, 1, 1, 6]
def baseStart_7125872 : Nat := 118140960795 + 7125872 * 2 ^ 59
def prefixEnd_7125872 : Nat := 4983230072969 + 3 ^ 40 * 7125872 * 2
def baseEnd_7125872 : Nat := 1219665806138483075576239

theorem tailTrace_7125872 : CollatzResearch.WordTrace tailWord_7125872 prefixEnd_7125872 1219665806138483075576239 := by
  unfold tailWord_7125872
  simp only [CollatzResearch.WordTrace]
  refine ⟨129950951820095110446113935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173267935760126813928151913 129950951820095110446113935)
  ·
    refine ⟨194926427730142665669170903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129950951820095110446113935 194926427730142665669170903)
    ·
      refine ⟨292389641595213998503756355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194926427730142665669170903 292389641595213998503756355)
      ·
        refine ⟨438584462392820997755634533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292389641595213998503756355 438584462392820997755634533)
        ·
          refine ⟨82234586698653937079181475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 438584462392820997755634533 82234586698653937079181475)
          ·
            refine ⟨123351880047980905618772213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82234586698653937079181475 123351880047980905618772213)
            ·
              refine ⟨11564238754498209901759895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123351880047980905618772213 11564238754498209901759895)
              ·
                refine ⟨17346358131747314852639843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11564238754498209901759895 17346358131747314852639843)
                ·
                  refine ⟨26019537197620972278959765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17346358131747314852639843 26019537197620972278959765)
                  ·
                    refine ⟨1219665806138483075576239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26019537197620972278959765 1219665806138483075576239)
                    ·
                      rfl

theorem cell23_7125872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 1, 6].length) (baseStart_7125872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125872 prefixEnd_7125872 := by exact prefixLift 7125872
  have htrace : WordTrace (prefixWord ++ tailWord_7125872) baseStart_7125872 baseEnd_7125872 := by
    simpa [prefixWord, tailWord_7125872, baseEnd_7125872] using wordTrace_append hprefix tailTrace_7125872
  have hstable : (prefixWord ++ tailWord_7125872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125872).length < 2 ^ (prefixWord ++ tailWord_7125872).sum := by decide
  have hdescent : baseEnd_7125872 < baseStart_7125872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125892 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_7125892 : Nat := 118140960795 + 7125892 * 2 ^ 59
def prefixEnd_7125892 : Nat := 4983230072969 + 3 ^ 40 * 7125892 * 2
def baseEnd_7125892 : Nat := 3659007688028539148478625

theorem tailTrace_7125892 : CollatzResearch.WordTrace tailWord_7125892 prefixEnd_7125892 3659007688028539148478625 := by
  unfold tailWord_7125892
  simp only [CollatzResearch.WordTrace]
  refine ⟨129951316550058882153977965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173268422066745176205303953 129951316550058882153977965)
  ·
    refine ⟨48731743706272080807741737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129951316550058882153977965 48731743706272080807741737)
    ·
      refine ⟨36548807779704060605806303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48731743706272080807741737 36548807779704060605806303)
      ·
        refine ⟨54823211669556090908709455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36548807779704060605806303 54823211669556090908709455)
        ·
          refine ⟨82234817504334136363064183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54823211669556090908709455 82234817504334136363064183)
          ·
            refine ⟨123352226256501204544596275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82234817504334136363064183 123352226256501204544596275)
            ·
              refine ⟨185028339384751806816894413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123352226256501204544596275 185028339384751806816894413)
              ·
                refine ⟨69385627269281927556335405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185028339384751806816894413 69385627269281927556335405)
                ·
                  refine ⟨26019610225980722833625777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69385627269281927556335405 26019610225980722833625777)
                  ·
                    refine ⟨19514707669485542125219333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26019610225980722833625777 19514707669485542125219333)
                    ·
                      refine ⟨3659007688028539148478625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19514707669485542125219333 3659007688028539148478625)
                      ·
                        rfl

theorem cell23_7125892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_7125892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125892 prefixEnd_7125892 := by exact prefixLift 7125892
  have htrace : WordTrace (prefixWord ++ tailWord_7125892) baseStart_7125892 baseEnd_7125892 := by
    simpa [prefixWord, tailWord_7125892, baseEnd_7125892] using wordTrace_append hprefix tailTrace_7125892
  have hstable : (prefixWord ++ tailWord_7125892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125892).length < 2 ^ (prefixWord ++ tailWord_7125892).sum := by decide
  have hdescent : baseEnd_7125892 < baseStart_7125892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125899 : List Nat := [1, 1, 1, 1, 4, 2, 4, 3, 1, 2, 3]
def baseStart_7125899 : Nat := 118140960795 + 7125899 * 2 ^ 59
def prefixEnd_7125899 : Nat := 4983230072969 + 3 ^ 40 * 7125899 * 2
def baseEnd_7125899 : Nat := 3659011282393120621091093

theorem tailTrace_7125899 : CollatzResearch.WordTrace tailWord_7125899 prefixEnd_7125899 3659011282393120621091093 := by
  unfold tailWord_7125899
  simp only [CollatzResearch.WordTrace]
  refine ⟨259902888411092404503460751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173268592274061603002307167 259902888411092404503460751)
  ·
    refine ⟨389854332616638606755191127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259902888411092404503460751 389854332616638606755191127)
    ·
      refine ⟨584781498924957910132786691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389854332616638606755191127 584781498924957910132786691)
      ·
        refine ⟨877172248387436865199180037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584781498924957910132786691 877172248387436865199180037)
        ·
          refine ⟨164469796572644412224846257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 877172248387436865199180037 164469796572644412224846257)
          ·
            refine ⟨123352347429483309168634693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164469796572644412224846257 123352347429483309168634693)
            ·
              refine ⟨23128565143028120469119005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123352347429483309168634693 23128565143028120469119005)
              ·
                refine ⟨8673211928635545175919627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23128565143028120469119005 8673211928635545175919627)
                ·
                  refine ⟨13009817892953317763879441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8673211928635545175919627 13009817892953317763879441)
                  ·
                    refine ⟨9757363419714988322909581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13009817892953317763879441 9757363419714988322909581)
                    ·
                      refine ⟨3659011282393120621091093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9757363419714988322909581 3659011282393120621091093)
                      ·
                        rfl

theorem cell23_7125899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 2, 3].length) (baseStart_7125899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125899 prefixEnd_7125899 := by exact prefixLift 7125899
  have htrace : WordTrace (prefixWord ++ tailWord_7125899) baseStart_7125899 baseEnd_7125899 := by
    simpa [prefixWord, tailWord_7125899, baseEnd_7125899] using wordTrace_append hprefix tailTrace_7125899
  have hstable : (prefixWord ++ tailWord_7125899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125899).length < 2 ^ (prefixWord ++ tailWord_7125899).sum := by decide
  have hdescent : baseEnd_7125899 < baseStart_7125899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125933 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_7125933 : Nat := 118140960795 + 7125933 * 2 ^ 59
def prefixEnd_7125933 : Nat := 4983230072969 + 3 ^ 40 * 7125933 * 2
def baseEnd_7125933 : Nat := 3659028740735373488065937

theorem tailTrace_7125933 : CollatzResearch.WordTrace tailWord_7125933 prefixEnd_7125933 3659028740735373488065937 := by
  unfold tailWord_7125933
  simp only [CollatzResearch.WordTrace]
  refine ⟨259904128492969228310198453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173269418995312818873465635 259904128492969228310198453)
  ·
    refine ⟨24366012046215865154081105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 259904128492969228310198453 24366012046215865154081105)
    ·
      refine ⟨18274509034661898865560829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24366012046215865154081105 18274509034661898865560829)
      ·
        refine ⟨6852940887998212074585311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18274509034661898865560829 6852940887998212074585311)
        ·
          refine ⟨10279411331997318111877967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6852940887998212074585311 10279411331997318111877967)
          ·
            refine ⟨15419116997995977167816951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10279411331997318111877967 15419116997995977167816951)
            ·
              refine ⟨23128675496993965751725427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15419116997995977167816951 23128675496993965751725427)
              ·
                refine ⟨34693013245490948627588141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23128675496993965751725427 34693013245490948627588141)
                ·
                  refine ⟨13009879967059105735345553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34693013245490948627588141 13009879967059105735345553)
                  ·
                    refine ⟨9757409975294329301509165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13009879967059105735345553 9757409975294329301509165)
                    ·
                      refine ⟨3659028740735373488065937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9757409975294329301509165 3659028740735373488065937)
                      ·
                        rfl

theorem cell23_7125933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_7125933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125933 prefixEnd_7125933 := by exact prefixLift 7125933
  have htrace : WordTrace (prefixWord ++ tailWord_7125933) baseStart_7125933 baseEnd_7125933 := by
    simpa [prefixWord, tailWord_7125933, baseEnd_7125933] using wordTrace_append hprefix tailTrace_7125933
  have hstable : (prefixWord ++ tailWord_7125933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125933).length < 2 ^ (prefixWord ++ tailWord_7125933).sum := by decide
  have hdescent : baseEnd_7125933 < baseStart_7125933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125958 : List Nat := [6, 1, 3, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_7125958 : Nat := 118140960795 + 7125958 * 2 ^ 59
def prefixEnd_7125958 : Nat := 4983230072969 + 3 ^ 40 * 7125958 * 2
def baseEnd_7125958 : Nat := 3659041577751735890253323

theorem tailTrace_7125958 : CollatzResearch.WordTrace tailWord_7125958 prefixEnd_7125958 3659041577751735890253323 := by
  unfold tailWord_7125958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8122032509933708049370579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 173270026878585771719905685 8122032509933708049370579)
  ·
    refine ⟨12183048764900562074055869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8122032509933708049370579 12183048764900562074055869)
    ·
      refine ⟨4568643286837710777770951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12183048764900562074055869 4568643286837710777770951)
      ·
        refine ⟨6852964930256566166656427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4568643286837710777770951 6852964930256566166656427)
        ·
          refine ⟨10279447395384849249984641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6852964930256566166656427 10279447395384849249984641)
          ·
            refine ⟨7709585546538636937488481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10279447395384849249984641 7709585546538636937488481)
            ·
              refine ⟨5782189159903977703116361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7709585546538636937488481 5782189159903977703116361)
              ·
                refine ⟨4336641869927983277337271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5782189159903977703116361 4336641869927983277337271)
                ·
                  refine ⟨6504962804891974916005907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4336641869927983277337271 6504962804891974916005907)
                  ·
                    refine ⟨9757444207337962374008861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6504962804891974916005907 9757444207337962374008861)
                    ·
                      refine ⟨3659041577751735890253323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9757444207337962374008861 3659041577751735890253323)
                      ·
                        rfl

theorem cell23_7125958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_7125958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125958 prefixEnd_7125958 := by exact prefixLift 7125958
  have htrace : WordTrace (prefixWord ++ tailWord_7125958) baseStart_7125958 baseEnd_7125958 := by
    simpa [prefixWord, tailWord_7125958, baseEnd_7125958] using wordTrace_append hprefix tailTrace_7125958
  have hstable : (prefixWord ++ tailWord_7125958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125958).length < 2 ^ (prefixWord ++ tailWord_7125958).sum := by decide
  have hdescent : baseEnd_7125958 < baseStart_7125958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125962 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 2, 6]
def baseStart_7125962 : Nat := 118140960795 + 7125962 * 2 ^ 59
def prefixEnd_7125962 : Nat := 4983230072969 + 3 ^ 40 * 7125962 * 2
def baseEnd_7125962 : Nat := 1219681210558117958201101

theorem tailTrace_7125962 : CollatzResearch.WordTrace tailWord_7125962 prefixEnd_7125962 1219681210558117958201101 := by
  unfold tailWord_7125962
  simp only [CollatzResearch.WordTrace]
  refine ⟨64976296552466041565751035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173270124139909444175336093 64976296552466041565751035)
  ·
    refine ⟨97464444828699062348626553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64976296552466041565751035 97464444828699062348626553)
    ·
      refine ⟨73098333621524296761469915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97464444828699062348626553 73098333621524296761469915)
      ·
        refine ⟨109647500432286445142204873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73098333621524296761469915 109647500432286445142204873)
        ·
          refine ⟨82235625324214833856653655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109647500432286445142204873 82235625324214833856653655)
          ·
            refine ⟨123353437986322250784980483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82235625324214833856653655 123353437986322250784980483)
            ·
              refine ⟨185030156979483376177470725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123353437986322250784980483 185030156979483376177470725)
              ·
                refine ⟨34693154433653133033275761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185030156979483376177470725 34693154433653133033275761)
                ·
                  refine ⟨26019865825239849774956821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34693154433653133033275761 26019865825239849774956821)
                  ·
                    refine ⟨1219681210558117958201101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26019865825239849774956821 1219681210558117958201101)
                    ·
                      rfl

theorem cell23_7125962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_7125962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125962 prefixEnd_7125962 := by exact prefixLift 7125962
  have htrace : WordTrace (prefixWord ++ tailWord_7125962) baseStart_7125962 baseEnd_7125962 := by
    simpa [prefixWord, tailWord_7125962, baseEnd_7125962] using wordTrace_append hprefix tailTrace_7125962
  have hstable : (prefixWord ++ tailWord_7125962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125962).length < 2 ^ (prefixWord ++ tailWord_7125962).sum := by decide
  have hdescent : baseEnd_7125962 < baseStart_7125962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125969 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 3, 4, 2]
def baseStart_7125969 : Nat := 118140960795 + 7125969 * 2 ^ 59
def prefixEnd_7125969 : Nat := 4983230072969 + 3 ^ 40 * 7125969 * 2
def baseEnd_7125969 : Nat := 3659047226038935347215771

theorem tailTrace_7125969 : CollatzResearch.WordTrace tailWord_7125969 prefixEnd_7125969 3659047226038935347215771 := by
  unfold tailWord_7125969
  simp only [CollatzResearch.WordTrace]
  refine ⟨259905441520838806458508961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173270294347225870972339307 259905441520838806458508961)
  ·
    refine ⟨194929081140629104843881721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259905441520838806458508961 194929081140629104843881721)
    ·
      refine ⟨146196810855471828632911291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194929081140629104843881721 146196810855471828632911291)
      ·
        refine ⟨219295216283207742949366937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146196810855471828632911291 219295216283207742949366937)
        ·
          refine ⟨164471412212405807212025203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219295216283207742949366937 164471412212405807212025203)
          ·
            refine ⟨246707118318608710818037805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164471412212405807212025203 246707118318608710818037805)
            ·
              refine ⟨92515169369478266556764177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246707118318608710818037805 92515169369478266556764177)
              ·
                refine ⟨69386377027108699917573133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92515169369478266556764177 69386377027108699917573133)
                ·
                  refine ⟨26019891385165762469089925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69386377027108699917573133 26019891385165762469089925)
                  ·
                    refine ⟨4878729634718580462954361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26019891385165762469089925 4878729634718580462954361)
                    ·
                      refine ⟨3659047226038935347215771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4878729634718580462954361 3659047226038935347215771)
                      ·
                        rfl

theorem cell23_7125969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 4, 2].length) (baseStart_7125969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125969 prefixEnd_7125969 := by exact prefixLift 7125969
  have htrace : WordTrace (prefixWord ++ tailWord_7125969) baseStart_7125969 baseEnd_7125969 := by
    simpa [prefixWord, tailWord_7125969, baseEnd_7125969] using wordTrace_append hprefix tailTrace_7125969
  have hstable : (prefixWord ++ tailWord_7125969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125969).length < 2 ^ (prefixWord ++ tailWord_7125969).sum := by decide
  have hdescent : baseEnd_7125969 < baseStart_7125969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7125992 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 9]
def baseStart_7125992 : Nat := 118140960795 + 7125992 * 2 ^ 59
def prefixEnd_7125992 : Nat := 4983230072969 + 3 ^ 40 * 7125992 * 2
def baseEnd_7125992 : Nat := 406562115121554306358685

theorem tailTrace_7125992 : CollatzResearch.WordTrace tailWord_7125992 prefixEnd_7125992 406562115121554306358685 := by
  unfold tailWord_7125992
  simp only [CollatzResearch.WordTrace]
  refine ⟨129953140199877740693298115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173270853599836987591064153 129953140199877740693298115)
  ·
    refine ⟨194929710299816611039947173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129953140199877740693298115 194929710299816611039947173)
    ·
      refine ⟨36549320681215614569990095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194929710299816611039947173 36549320681215614569990095)
      ·
        refine ⟨54823981021823421854985143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36549320681215614569990095 54823981021823421854985143)
        ·
          refine ⟨82235971532735132782477715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54823981021823421854985143 82235971532735132782477715)
          ·
            refine ⟨123353957299102699173716573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82235971532735132782477715 123353957299102699173716573)
            ·
              refine ⟨46257733987163512190143715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123353957299102699173716573 46257733987163512190143715)
              ·
                refine ⟨69386600980745268285215573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46257733987163512190143715 69386600980745268285215573)
                ·
                  refine ⟨406562115121554306358685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69386600980745268285215573 406562115121554306358685)
                  ·
                    rfl

theorem cell23_7125992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 9].length) (baseStart_7125992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7125992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7125992 prefixEnd_7125992 := by exact prefixLift 7125992
  have htrace : WordTrace (prefixWord ++ tailWord_7125992) baseStart_7125992 baseEnd_7125992 := by
    simpa [prefixWord, tailWord_7125992, baseEnd_7125992] using wordTrace_append hprefix tailTrace_7125992
  have hstable : (prefixWord ++ tailWord_7125992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7125992).length < 2 ^ (prefixWord ++ tailWord_7125992).sum := by decide
  have hdescent : baseEnd_7125992 < baseStart_7125992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7125992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126026 : List Nat := [3, 1, 2, 2, 3, 1, 2, 4, 5]
def baseStart_7126026 : Nat := 118140960795 + 7126026 * 2 ^ 59
def prefixEnd_7126026 : Nat := 4983230072969 + 3 ^ 40 * 7126026 * 2
def baseEnd_7126026 : Nat := 406564054937360180467001

theorem tailTrace_7126026 : CollatzResearch.WordTrace tailWord_7126026 prefixEnd_7126026 406564054937360180467001 := by
  unfold tailWord_7126026
  simp only [CollatzResearch.WordTrace]
  refine ⟨64976880120408076298333483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173271680321088203462222621 64976880120408076298333483)
  ·
    refine ⟨97465320180612114447500225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64976880120408076298333483 97465320180612114447500225)
    ·
      refine ⟨73098990135459085835625169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97465320180612114447500225 73098990135459085835625169)
      ·
        refine ⟨54824242601594314376718877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73098990135459085835625169 54824242601594314376718877)
        ·
          refine ⟨20559090975597867891269579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54824242601594314376718877 20559090975597867891269579)
          ·
            refine ⟨30838636463396801836904369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20559090975597867891269579 30838636463396801836904369)
            ·
              refine ⟨23128977347547601377678277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30838636463396801836904369 23128977347547601377678277)
              ·
                refine ⟨4336683252665175258314677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23128977347547601377678277 4336683252665175258314677)
                ·
                  refine ⟨406564054937360180467001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4336683252665175258314677 406564054937360180467001)
                  ·
                    rfl

theorem cell23_7126026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 5].length) (baseStart_7126026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126026 prefixEnd_7126026 := by exact prefixLift 7126026
  have htrace : WordTrace (prefixWord ++ tailWord_7126026) baseStart_7126026 baseEnd_7126026 := by
    simpa [prefixWord, tailWord_7126026, baseEnd_7126026] using wordTrace_append hprefix tailTrace_7126026
  have hstable : (prefixWord ++ tailWord_7126026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126026).length < 2 ^ (prefixWord ++ tailWord_7126026).sum := by decide
  have hdescent : baseEnd_7126026 < baseStart_7126026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126039 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 1, 7]
def baseStart_7126039 : Nat := 118140960795 + 7126039 * 2 ^ 59
def prefixEnd_7126039 : Nat := 4983230072969 + 3 ^ 40 * 7126039 * 2
def baseEnd_7126039 : Nat := 1219694389894916691113483

theorem tailTrace_7126039 : CollatzResearch.WordTrace tailWord_7126039 prefixEnd_7126039 1219694389894916691113483 := by
  unfold tailWord_7126039
  simp only [CollatzResearch.WordTrace]
  refine ⟨259907994630585208413557171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173271996420390138942371447 259907994630585208413557171)
  ·
    refine ⟨389861991945877812620335757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259907994630585208413557171 389861991945877812620335757)
    ·
      refine ⟨146198246979704179732625909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389861991945877812620335757 146198246979704179732625909)
      ·
        refine ⟨13706085654347266849933679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146198246979704179732625909 13706085654347266849933679)
        ·
          refine ⟨20559128481520900274900519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13706085654347266849933679 20559128481520900274900519)
          ·
            refine ⟨30838692722281350412350779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20559128481520900274900519 30838692722281350412350779)
            ·
              refine ⟨46258039083422025618526169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30838692722281350412350779 46258039083422025618526169)
              ·
                refine ⟨34693529312566519213894627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46258039083422025618526169 34693529312566519213894627)
                ·
                  refine ⟨52040293968849778820841941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34693529312566519213894627 52040293968849778820841941)
                  ·
                    refine ⟨1219694389894916691113483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52040293968849778820841941 1219694389894916691113483)
                    ·
                      rfl

theorem cell23_7126039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_7126039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126039 prefixEnd_7126039 := by exact prefixLift 7126039
  have htrace : WordTrace (prefixWord ++ tailWord_7126039) baseStart_7126039 baseEnd_7126039 := by
    simpa [prefixWord, tailWord_7126039, baseEnd_7126039] using wordTrace_append hprefix tailTrace_7126039
  have hstable : (prefixWord ++ tailWord_7126039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126039).length < 2 ^ (prefixWord ++ tailWord_7126039).sum := by decide
  have hdescent : baseEnd_7126039 < baseStart_7126039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126059 : List Nat := [1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 4]
def baseStart_7126059 : Nat := 118140960795 + 7126059 * 2 ^ 59
def prefixEnd_7126059 : Nat := 4983230072969 + 3 ^ 40 * 7126059 * 2
def baseEnd_7126059 : Nat := 3659093439297839995090357

theorem tailTrace_7126059 : CollatzResearch.WordTrace tailWord_7126059 prefixEnd_7126059 3659093439297839995090357 := by
  unfold tailWord_7126059
  simp only [CollatzResearch.WordTrace]
  refine ⟨259908724090512751829285231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173272482727008501219523487 259908724090512751829285231)
  ·
    refine ⟨389863086135769127743927847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259908724090512751829285231 389863086135769127743927847)
    ·
      refine ⟨584794629203653691615891771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389863086135769127743927847 584794629203653691615891771)
      ·
        refine ⟨877191943805480537423837657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584794629203653691615891771 877191943805480537423837657)
        ·
          refine ⟨657893957854110403067878243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 877191943805480537423837657 657893957854110403067878243)
          ·
            refine ⟨986840936781165604601817365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657893957854110403067878243 986840936781165604601817365)
            ·
              refine ⟨46258168911617137715710189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 986840936781165604601817365 46258168911617137715710189)
              ·
                refine ⟨17346813341856426643391321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46258168911617137715710189 17346813341856426643391321)
                ·
                  refine ⟨13010110006392319982543491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17346813341856426643391321 13010110006392319982543491)
                  ·
                    refine ⟨19515165009588479973815237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13010110006392319982543491 19515165009588479973815237)
                    ·
                      refine ⟨3659093439297839995090357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19515165009588479973815237 3659093439297839995090357)
                      ·
                        rfl

theorem cell23_7126059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 4].length) (baseStart_7126059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126059 prefixEnd_7126059 := by exact prefixLift 7126059
  have htrace : WordTrace (prefixWord ++ tailWord_7126059) baseStart_7126059 baseEnd_7126059 := by
    simpa [prefixWord, tailWord_7126059, baseEnd_7126059] using wordTrace_append hprefix tailTrace_7126059
  have hstable : (prefixWord ++ tailWord_7126059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126059).length < 2 ^ (prefixWord ++ tailWord_7126059).sum := by decide
  have hdescent : baseEnd_7126059 < baseStart_7126059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126076 : List Nat := [2, 2, 2, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_7126076 : Nat := 118140960795 + 7126076 * 2 ^ 59
def prefixEnd_7126076 : Nat := 4983230072969 + 3 ^ 40 * 7126076 * 2
def baseEnd_7126076 : Nat := 3659102168468966428577779

theorem tailTrace_7126076 : CollatzResearch.WordTrace tailWord_7126076 prefixEnd_7126076 3659102168468966428577779 := by
  unfold tailWord_7126076
  simp only [CollatzResearch.WordTrace]
  refine ⟨129954672065725581866327041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173272896087634109155102721 129954672065725581866327041)
  ·
    refine ⟨97466004049294186399745281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129954672065725581866327041 97466004049294186399745281)
    ·
      refine ⟨73099503036970639799808961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97466004049294186399745281 73099503036970639799808961)
      ·
        refine ⟨54824627277727979849856721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73099503036970639799808961 54824627277727979849856721)
        ·
          refine ⟨41118470458295984887392541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54824627277727979849856721 41118470458295984887392541)
          ·
            refine ⟨15419426421860994332772203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41118470458295984887392541 15419426421860994332772203)
            ·
              refine ⟨23129139632791491499158305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15419426421860994332772203 23129139632791491499158305)
              ·
                refine ⟨17346854724593618624368729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23129139632791491499158305 17346854724593618624368729)
                ·
                  refine ⟨13010141043445213968276547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17346854724593618624368729 13010141043445213968276547)
                  ·
                    refine ⟨19515211565167820952414821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13010141043445213968276547 19515211565167820952414821)
                    ·
                      refine ⟨3659102168468966428577779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19515211565167820952414821 3659102168468966428577779)
                      ·
                        rfl

theorem cell23_7126076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_7126076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126076 prefixEnd_7126076 := by exact prefixLift 7126076
  have htrace : WordTrace (prefixWord ++ tailWord_7126076) baseStart_7126076 baseEnd_7126076 := by
    simpa [prefixWord, tailWord_7126076, baseEnd_7126076] using wordTrace_append hprefix tailTrace_7126076
  have hstable : (prefixWord ++ tailWord_7126076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126076).length < 2 ^ (prefixWord ++ tailWord_7126076).sum := by decide
  have hdescent : baseEnd_7126076 < baseStart_7126076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126110 : List Nat := [4, 4, 1, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_7126110 : Nat := 118140960795 + 7126110 * 2 ^ 59
def prefixEnd_7126110 : Nat := 4983230072969 + 3 ^ 40 * 7126110 * 2
def baseEnd_7126110 : Nat := 3659119626811219295552623

theorem tailTrace_7126110 : CollatzResearch.WordTrace tailWord_7126110 prefixEnd_7126110 3659119626811219295552623 := by
  unfold tailWord_7126110
  simp only [CollatzResearch.WordTrace]
  refine ⟨32488823026665998442423973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173273722808885325026261189 32488823026665998442423973)
  ·
    refine ⟨6091654317499874707954495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32488823026665998442423973 6091654317499874707954495)
    ·
      refine ⟨9137481476249812061931743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6091654317499874707954495 9137481476249812061931743)
      ·
        refine ⟨13706222214374718092897615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9137481476249812061931743 13706222214374718092897615)
        ·
          refine ⟨20559333321562077139346423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13706222214374718092897615 20559333321562077139346423)
          ·
            refine ⟨30838999982343115709019635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20559333321562077139346423 30838999982343115709019635)
            ·
              refine ⟨46258499973514673563529453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30838999982343115709019635 46258499973514673563529453)
              ·
                refine ⟨17346937490068002586323545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46258499973514673563529453 17346937490068002586323545)
                ·
                  refine ⟨13010203117551001939742659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17346937490068002586323545 13010203117551001939742659)
                  ·
                    refine ⟨19515304676326502909613989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13010203117551001939742659 19515304676326502909613989)
                    ·
                      refine ⟨3659119626811219295552623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19515304676326502909613989 3659119626811219295552623)
                      ·
                        rfl

theorem cell23_7126110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_7126110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126110 prefixEnd_7126110 := by exact prefixLift 7126110
  have htrace : WordTrace (prefixWord ++ tailWord_7126110) baseStart_7126110 baseEnd_7126110 := by
    simpa [prefixWord, tailWord_7126110, baseEnd_7126110] using wordTrace_append hprefix tailTrace_7126110
  have hstable : (prefixWord ++ tailWord_7126110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126110).length < 2 ^ (prefixWord ++ tailWord_7126110).sum := by decide
  have hdescent : baseEnd_7126110 < baseStart_7126110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126137 : List Nat := [1, 2, 1, 3, 5, 2, 2, 2, 1, 4]
def baseStart_7126137 : Nat := 118140960795 + 7126137 * 2 ^ 59
def prefixEnd_7126137 : Nat := 4983230072969 + 3 ^ 40 * 7126137 * 2
def baseEnd_7126137 : Nat := 1219711163596296896638333

theorem tailTrace_7126137 : CollatzResearch.WordTrace tailWord_7126137 prefixEnd_7126137 1219711163596296896638333 := by
  unfold tailWord_7126137
  simp only [CollatzResearch.WordTrace]
  refine ⟨259911568984230171150624665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173274379322820114100416443 259911568984230171150624665)
  ·
    refine ⟨194933676738172628362968499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259911568984230171150624665 194933676738172628362968499)
    ·
      refine ⟨292400515107258942544452749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194933676738172628362968499 292400515107258942544452749)
      ·
        refine ⟨109650193165222103454169781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292400515107258942544452749 109650193165222103454169781)
        ·
          refine ⟨10279705609239572198828417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109650193165222103454169781 10279705609239572198828417)
          ·
            refine ⟨7709779206929679149121313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10279705609239572198828417 7709779206929679149121313)
            ·
              refine ⟨5782334405197259361840985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7709779206929679149121313 5782334405197259361840985)
              ·
                refine ⟨4336750803897944521380739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5782334405197259361840985 4336750803897944521380739)
                ·
                  refine ⟨6505126205846916782071109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4336750803897944521380739 6505126205846916782071109)
                  ·
                    refine ⟨1219711163596296896638333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6505126205846916782071109 1219711163596296896638333)
                    ·
                      rfl

theorem cell23_7126137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 1, 4].length) (baseStart_7126137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126137 prefixEnd_7126137 := by exact prefixLift 7126137
  have htrace : WordTrace (prefixWord ++ tailWord_7126137) baseStart_7126137 baseEnd_7126137 := by
    simpa [prefixWord, tailWord_7126137, baseEnd_7126137] using wordTrace_append hprefix tailTrace_7126137
  have hstable : (prefixWord ++ tailWord_7126137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126137).length < 2 ^ (prefixWord ++ tailWord_7126137).sum := by decide
  have hdescent : baseEnd_7126137 < baseStart_7126137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126170 : List Nat := [3, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2]
def baseStart_7126170 : Nat := 118140960795 + 7126170 * 2 ^ 59
def prefixEnd_7126170 : Nat := 4983230072969 + 3 ^ 40 * 7126170 * 2
def baseEnd_7126170 : Nat := 3659150435650489060802347

theorem tailTrace_7126170 : CollatzResearch.WordTrace tailWord_7126170 prefixEnd_7126170 3659150435650489060802347 := by
  unfold tailWord_7126170
  simp only [CollatzResearch.WordTrace]
  refine ⟨64978193148277654446643991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173275181728740411857717309 64978193148277654446643991)
  ·
    refine ⟨97467289722416481669965987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64978193148277654446643991 97467289722416481669965987)
    ·
      refine ⟨146200934583624722504948981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97467289722416481669965987 146200934583624722504948981)
      ·
        refine ⟨13706337617214817734838967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146200934583624722504948981 13706337617214817734838967)
        ·
          refine ⟨20559506425822226602258451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13706337617214817734838967 20559506425822226602258451)
          ·
            refine ⟨30839259638733339903387677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20559506425822226602258451 30839259638733339903387677)
            ·
              refine ⟨11564722364525002463770379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30839259638733339903387677 11564722364525002463770379)
              ·
                refine ⟨17347083546787503695655569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11564722364525002463770379 17347083546787503695655569)
                ·
                  refine ⟨13010312660090627771741677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17347083546787503695655569 13010312660090627771741677)
                  ·
                    refine ⟨4878867247533985414403129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13010312660090627771741677 4878867247533985414403129)
                    ·
                      refine ⟨3659150435650489060802347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4878867247533985414403129 3659150435650489060802347)
                      ·
                        rfl

theorem cell23_7126170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_7126170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126170 prefixEnd_7126170 := by exact prefixLift 7126170
  have htrace : WordTrace (prefixWord ++ tailWord_7126170) baseStart_7126170 baseEnd_7126170 := by
    simpa [prefixWord, tailWord_7126170, baseEnd_7126170] using wordTrace_append hprefix tailTrace_7126170
  have hstable : (prefixWord ++ tailWord_7126170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126170).length < 2 ^ (prefixWord ++ tailWord_7126170).sum := by decide
  have hdescent : baseEnd_7126170 < baseStart_7126170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126176 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 4, 4]
def baseStart_7126176 : Nat := 118140960795 + 7126176 * 2 ^ 59
def prefixEnd_7126176 : Nat := 4983230072969 + 3 ^ 40 * 7126176 * 2
def baseEnd_7126176 : Nat := 1219717838844805345775773

theorem tailTrace_7126176 : CollatzResearch.WordTrace tailWord_7126176 prefixEnd_7126176 1219717838844805345775773 := by
  unfold tailWord_7126176
  simp only [CollatzResearch.WordTrace]
  refine ⟨129956495715544440405647191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173275327620725920540862921 129956495715544440405647191)
  ·
    refine ⟨194934743573316660608470787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129956495715544440405647191 194934743573316660608470787)
    ·
      refine ⟨292402115359974990912706181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194934743573316660608470787 292402115359974990912706181)
      ·
        refine ⟨54825396629995310796132409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292402115359974990912706181 54825396629995310796132409)
        ·
          refine ⟨41119047472496483097099307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54825396629995310796132409 41119047472496483097099307)
          ·
            refine ⟨61678571208744724645648961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41119047472496483097099307 61678571208744724645648961)
            ·
              refine ⟨46258928406558543484236721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61678571208744724645648961 46258928406558543484236721)
              ·
                refine ⟨34694196304918907613177541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46258928406558543484236721 34694196304918907613177541)
                ·
                  refine ⟨6505161807172295177470789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34694196304918907613177541 6505161807172295177470789)
                  ·
                    refine ⟨1219717838844805345775773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6505161807172295177470789 1219717838844805345775773)
                    ·
                      rfl

theorem cell23_7126176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 4, 4].length) (baseStart_7126176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126176 prefixEnd_7126176 := by exact prefixLift 7126176
  have htrace : WordTrace (prefixWord ++ tailWord_7126176) baseStart_7126176 baseEnd_7126176 := by
    simpa [prefixWord, tailWord_7126176, baseEnd_7126176] using wordTrace_append hprefix tailTrace_7126176
  have hstable : (prefixWord ++ tailWord_7126176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126176).length < 2 ^ (prefixWord ++ tailWord_7126176).sum := by decide
  have hdescent : baseEnd_7126176 < baseStart_7126176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126180 : List Nat := [2, 3, 1, 2, 3, 3, 2, 1, 1, 5]
def baseStart_7126180 : Nat := 118140960795 + 7126180 * 2 ^ 59
def prefixEnd_7126180 : Nat := 4983230072969 + 3 ^ 40 * 7126180 * 2
def baseEnd_7126180 : Nat := 1219718523485678007225767

theorem tailTrace_7126180 : CollatzResearch.WordTrace tailWord_7126180 prefixEnd_7126180 1219718523485678007225767 := by
  unfold tailWord_7126180
  simp only [CollatzResearch.WordTrace]
  refine ⟨129956568661537194747219997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173275424882049592996293329 129956568661537194747219997)
  ·
    refine ⟨48733713248076448030207499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129956568661537194747219997 48733713248076448030207499)
    ·
      refine ⟨73100569872114672045311249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48733713248076448030207499 73100569872114672045311249)
      ·
        refine ⟨54825427404086004033983437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73100569872114672045311249 54825427404086004033983437)
        ·
          refine ⟨20559535276532251512743789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54825427404086004033983437 20559535276532251512743789)
          ·
            refine ⟨7709825728699594317278921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20559535276532251512743789 7709825728699594317278921)
            ·
              refine ⟨5782369296524695737959191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7709825728699594317278921 5782369296524695737959191)
              ·
                refine ⟨8673553944787043606938787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5782369296524695737959191 8673553944787043606938787)
                ·
                  refine ⟨13010330917180565410408181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8673553944787043606938787 13010330917180565410408181)
                  ·
                    refine ⟨1219718523485678007225767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13010330917180565410408181 1219718523485678007225767)
                    ·
                      rfl

theorem cell23_7126180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_7126180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126180 prefixEnd_7126180 := by exact prefixLift 7126180
  have htrace : WordTrace (prefixWord ++ tailWord_7126180) baseStart_7126180 baseEnd_7126180 := by
    simpa [prefixWord, tailWord_7126180, baseEnd_7126180] using wordTrace_append hprefix tailTrace_7126180
  have hstable : (prefixWord ++ tailWord_7126180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126180).length < 2 ^ (prefixWord ++ tailWord_7126180).sum := by decide
  have hdescent : baseEnd_7126180 < baseStart_7126180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126193 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 4, 4]
def baseStart_7126193 : Nat := 118140960795 + 7126193 * 2 ^ 59
def prefixEnd_7126193 : Nat := 4983230072969 + 3 ^ 40 * 7126193 * 2
def baseEnd_7126193 : Nat := 1219720748568514156938247

theorem tailTrace_7126193 : CollatzResearch.WordTrace tailWord_7126193 prefixEnd_7126193 1219720748568514156938247 := by
  unfold tailWord_7126193
  simp only [CollatzResearch.WordTrace]
  refine ⟨259913611472027292714663233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173275740981351528476442155 259913611472027292714663233)
  ·
    refine ⟨194935208604020469535997425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259913611472027292714663233 194935208604020469535997425)
    ·
      refine ⟨146201406453015352151998069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194935208604020469535997425 146201406453015352151998069)
      ·
        refine ⟨13706381854970189264249819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146201406453015352151998069 13706381854970189264249819)
        ·
          refine ⟨20559572782455283896374729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13706381854970189264249819 20559572782455283896374729)
          ·
            refine ⟨15419679586841462922281047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20559572782455283896374729 15419679586841462922281047)
            ·
              refine ⟨23129519380262194383421571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15419679586841462922281047 23129519380262194383421571)
              ·
                refine ⟨34694279070393291575132357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23129519380262194383421571 34694279070393291575132357)
                ·
                  refine ⟨6505177325698742170337317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34694279070393291575132357 6505177325698742170337317)
                  ·
                    refine ⟨1219720748568514156938247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6505177325698742170337317 1219720748568514156938247)
                    ·
                      rfl

theorem cell23_7126193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_7126193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126193 prefixEnd_7126193 := by exact prefixLift 7126193
  have htrace : WordTrace (prefixWord ++ tailWord_7126193) baseStart_7126193 baseEnd_7126193 := by
    simpa [prefixWord, tailWord_7126193, baseEnd_7126193] using wordTrace_append hprefix tailTrace_7126193
  have hstable : (prefixWord ++ tailWord_7126193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126193).length < 2 ^ (prefixWord ++ tailWord_7126193).sum := by decide
  have hdescent : baseEnd_7126193 < baseStart_7126193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126214 : List Nat := [6, 1, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_7126214 : Nat := 118140960795 + 7126214 * 2 ^ 59
def prefixEnd_7126214 : Nat := 4983230072969 + 3 ^ 40 * 7126214 * 2
def baseEnd_7126214 : Nat := 1219724342933095629550715

theorem tailTrace_7126214 : CollatzResearch.WordTrace tailWord_7126214 prefixEnd_7126214 1219724342933095629550715 := by
  unfold tailWord_7126214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8122324293904725415661803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 173276251603300808867451797 8122324293904725415661803)
  ·
    refine ⟨12183486440857088123492705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8122324293904725415661803 12183486440857088123492705)
    ·
      refine ⟨9137614830642816092619529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12183486440857088123492705 9137614830642816092619529)
      ·
        refine ⟨6853211122982112069464647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9137614830642816092619529 6853211122982112069464647)
        ·
          refine ⟨10279816684473168104196971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6853211122982112069464647 10279816684473168104196971)
          ·
            refine ⟨15419725026709752156295457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10279816684473168104196971 15419725026709752156295457)
            ·
              refine ⟨11564793770032314117221593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15419725026709752156295457 11564793770032314117221593)
              ·
                refine ⟨8673595327524235587916195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11564793770032314117221593 8673595327524235587916195)
                ·
                  refine ⟨13010392991286353381874293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8673595327524235587916195 13010392991286353381874293)
                  ·
                    refine ⟨1219724342933095629550715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13010392991286353381874293 1219724342933095629550715)
                    ·
                      rfl

theorem cell23_7126214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_7126214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126214 prefixEnd_7126214 := by exact prefixLift 7126214
  have htrace : WordTrace (prefixWord ++ tailWord_7126214) baseStart_7126214 baseEnd_7126214 := by
    simpa [prefixWord, tailWord_7126214, baseEnd_7126214] using wordTrace_append hprefix tailTrace_7126214
  have hstable : (prefixWord ++ tailWord_7126214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126214).length < 2 ^ (prefixWord ++ tailWord_7126214).sum := by decide
  have hdescent : baseEnd_7126214 < baseStart_7126214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126307 : List Nat := [1, 1, 1, 4, 2, 4, 2, 2, 2, 2, 2]
def baseStart_7126307 : Nat := 118140960795 + 7126307 * 2 ^ 59
def prefixEnd_7126307 : Nat := 4983230072969 + 3 ^ 40 * 7126307 * 2
def baseEnd_7126307 : Nat := 3659220782500155024789217

theorem tailTrace_7126307 : CollatzResearch.WordTrace tailWord_7126307 prefixEnd_7126307 3659220782500155024789217 := by
  unfold tailWord_7126307
  simp only [CollatzResearch.WordTrace]
  refine ⟨259917769393614290184313175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173278512929076193456208783 259917769393614290184313175)
  ·
    refine ⟨389876654090421435276469763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259917769393614290184313175 389876654090421435276469763)
    ·
      refine ⟨584814981135632152914704645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389876654090421435276469763 584814981135632152914704645)
      ·
        refine ⟨109652808962931028671507121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 584814981135632152914704645 109652808962931028671507121)
        ·
          refine ⟨82239606722198271503630341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109652808962931028671507121 82239606722198271503630341)
          ·
            refine ⟨15419926260412175906930689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82239606722198271503630341 15419926260412175906930689)
            ·
              refine ⟨11564944695309131930198017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15419926260412175906930689 11564944695309131930198017)
              ·
                refine ⟨8673708521481848947648513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11564944695309131930198017 8673708521481848947648513)
                ·
                  refine ⟨6505281391111386710736385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8673708521481848947648513 6505281391111386710736385)
                  ·
                    refine ⟨4878961043333540033052289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6505281391111386710736385 4878961043333540033052289)
                    ·
                      refine ⟨3659220782500155024789217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4878961043333540033052289 3659220782500155024789217)
                      ·
                        rfl

theorem cell23_7126307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_7126307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126307 prefixEnd_7126307 := by exact prefixLift 7126307
  have htrace : WordTrace (prefixWord ++ tailWord_7126307) baseStart_7126307 baseEnd_7126307 := by
    simpa [prefixWord, tailWord_7126307, baseEnd_7126307] using wordTrace_append hprefix tailTrace_7126307
  have hstable : (prefixWord ++ tailWord_7126307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126307).length < 2 ^ (prefixWord ++ tailWord_7126307).sum := by decide
  have hdescent : baseEnd_7126307 < baseStart_7126307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126323 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 3]
def baseStart_7126323 : Nat := 118140960795 + 7126323 * 2 ^ 59
def prefixEnd_7126323 : Nat := 4983230072969 + 3 ^ 40 * 7126323 * 2
def baseEnd_7126323 : Nat := 3659228998190626962189143

theorem tailTrace_7126323 : CollatzResearch.WordTrace tailWord_7126323 prefixEnd_7126323 3659228998190626962189143 := by
  unfold tailWord_7126323
  simp only [CollatzResearch.WordTrace]
  refine ⟨259918352961556324916895623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173278901974370883277930415 259918352961556324916895623)
  ·
    refine ⟨389877529442334487375343435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259918352961556324916895623 389877529442334487375343435)
    ·
      refine ⟨584816294163501731063015153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389877529442334487375343435 584816294163501731063015153)
      ·
        refine ⟨438612220622626298297261365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 584816294163501731063015153 438612220622626298297261365)
        ·
          refine ⟨41119895683371215465368253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 438612220622626298297261365 41119895683371215465368253)
          ·
            refine ⟨15419960881264205799513095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41119895683371215465368253 15419960881264205799513095)
            ·
              refine ⟨23129941321896308699269643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15419960881264205799513095 23129941321896308699269643)
              ·
                refine ⟨34694911982844463048904465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23129941321896308699269643 34694911982844463048904465)
                ·
                  refine ⟨26021183987133347286678349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34694911982844463048904465 26021183987133347286678349)
                  ·
                    refine ⟨9757943995175005232504381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26021183987133347286678349 9757943995175005232504381)
                    ·
                      refine ⟨3659228998190626962189143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9757943995175005232504381 3659228998190626962189143)
                      ·
                        rfl

theorem cell23_7126323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 3].length) (baseStart_7126323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126323 prefixEnd_7126323 := by exact prefixLift 7126323
  have htrace : WordTrace (prefixWord ++ tailWord_7126323) baseStart_7126323 baseEnd_7126323 := by
    simpa [prefixWord, tailWord_7126323, baseEnd_7126323] using wordTrace_append hprefix tailTrace_7126323
  have hstable : (prefixWord ++ tailWord_7126323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126323).length < 2 ^ (prefixWord ++ tailWord_7126323).sum := by decide
  have hdescent : baseEnd_7126323 < baseStart_7126323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126343 : List Nat := [1, 1, 4, 1, 2, 3, 3, 1, 2, 5]
def baseStart_7126343 : Nat := 118140960795 + 7126343 * 2 ^ 59
def prefixEnd_7126343 : Nat := 4983230072969 + 3 ^ 40 * 7126343 * 2
def baseEnd_7126343 : Nat := 1219746422601238961313017

theorem tailTrace_7126343 : CollatzResearch.WordTrace tailWord_7126343 prefixEnd_7126343 1219746422601238961313017 := by
  unfold tailWord_7126343
  simp only [CollatzResearch.WordTrace]
  refine ⟨259919082421483868332623683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173279388280989245555082455 259919082421483868332623683)
  ·
    refine ⟨389878623632225802498935525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259919082421483868332623683 389878623632225802498935525)
    ·
      refine ⟨73102241931042337968550411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389878623632225802498935525 73102241931042337968550411)
      ·
        refine ⟨109653362896563506952825617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73102241931042337968550411 109653362896563506952825617)
        ·
          refine ⟨82240022172422630214619213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109653362896563506952825617 82240022172422630214619213)
          ·
            refine ⟨30840008314658486330482205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82240022172422630214619213 30840008314658486330482205)
            ·
              refine ⟨11565003117996932373930827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30840008314658486330482205 11565003117996932373930827)
              ·
                refine ⟨17347504676995398560896241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11565003117996932373930827 17347504676995398560896241)
                ·
                  refine ⟨13010628507746548920672181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17347504676995398560896241 13010628507746548920672181)
                  ·
                    refine ⟨1219746422601238961313017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13010628507746548920672181 1219746422601238961313017)
                    ·
                      rfl

theorem cell23_7126343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_7126343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126343 prefixEnd_7126343 := by exact prefixLift 7126343
  have htrace : WordTrace (prefixWord ++ tailWord_7126343) baseStart_7126343 baseEnd_7126343 := by
    simpa [prefixWord, tailWord_7126343, baseEnd_7126343] using wordTrace_append hprefix tailTrace_7126343
  have hstable : (prefixWord ++ tailWord_7126343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126343).length < 2 ^ (prefixWord ++ tailWord_7126343).sum := by decide
  have hdescent : baseEnd_7126343 < baseStart_7126343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126358 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_7126358 : Nat := 118140960795 + 7126358 * 2 ^ 59
def prefixEnd_7126358 : Nat := 4983230072969 + 3 ^ 40 * 7126358 * 2
def baseEnd_7126358 : Nat := 3659246970013534325251483

theorem tailTrace_7126358 : CollatzResearch.WordTrace tailWord_7126358 prefixEnd_7126358 3659246970013534325251483 := by
  unfold tailWord_7126358
  simp only [CollatzResearch.WordTrace]
  refine ⟨16244976844776845368401233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173279753010953017262946485 16244976844776845368401233)
  ·
    refine ⟨12183732633582634026300925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16244976844776845368401233 12183732633582634026300925)
    ·
      refine ⟨4568899737593487759862847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12183732633582634026300925 4568899737593487759862847)
      ·
        refine ⟨6853349606390231639794271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4568899737593487759862847 6853349606390231639794271)
        ·
          refine ⟨10280024409585347459691407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6853349606390231639794271 10280024409585347459691407)
          ·
            refine ⟨15420036614378021189537111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10280024409585347459691407 15420036614378021189537111)
            ·
              refine ⟨23130054921567031784305667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15420036614378021189537111 23130054921567031784305667)
              ·
                refine ⟨34695082382350547676458501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23130054921567031784305667 34695082382350547676458501)
                ·
                  refine ⟨6505327946690727689335969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34695082382350547676458501 6505327946690727689335969)
                  ·
                    refine ⟨4878995960018045767001977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6505327946690727689335969 4878995960018045767001977)
                    ·
                      refine ⟨3659246970013534325251483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4878995960018045767001977 3659246970013534325251483)
                      ·
                        rfl

theorem cell23_7126358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_7126358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126358 prefixEnd_7126358 := by exact prefixLift 7126358
  have htrace : WordTrace (prefixWord ++ tailWord_7126358) baseStart_7126358 baseEnd_7126358 := by
    simpa [prefixWord, tailWord_7126358, baseEnd_7126358] using wordTrace_append hprefix tailTrace_7126358
  have hstable : (prefixWord ++ tailWord_7126358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126358).length < 2 ^ (prefixWord ++ tailWord_7126358).sum := by decide
  have hdescent : baseEnd_7126358 < baseStart_7126358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126380 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 2, 4, 2]
def baseStart_7126380 : Nat := 118140960795 + 7126380 * 2 ^ 59
def prefixEnd_7126380 : Nat := 4983230072969 + 3 ^ 40 * 7126380 * 2
def baseEnd_7126380 : Nat := 3659258266587933239176381

theorem tailTrace_7126380 : CollatzResearch.WordTrace tailWord_7126380 prefixEnd_7126380 3659258266587933239176381 := by
  unfold tailWord_7126380
  simp only [CollatzResearch.WordTrace]
  refine ⟨129960215961174911825860297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173280287948233215767813729 129960215961174911825860297)
  ·
    refine ⟨97470161970881183869395223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129960215961174911825860297 97470161970881183869395223)
    ·
      refine ⟨146205242956321775804092835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97470161970881183869395223 146205242956321775804092835)
      ·
        refine ⟨219307864434482663706139253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146205242956321775804092835 219307864434482663706139253)
        ·
          refine ⟨20560112290732749722450555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219307864434482663706139253 20560112290732749722450555)
          ·
            refine ⟨30840168436099124583675833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20560112290732749722450555 30840168436099124583675833)
            ·
              refine ⟨23130126327074343437756875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30840168436099124583675833 23130126327074343437756875)
              ·
                refine ⟨34695189490611515156635313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23130126327074343437756875 34695189490611515156635313)
                ·
                  refine ⟨26021392117958636367476485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34695189490611515156635313 26021392117958636367476485)
                  ·
                    refine ⟨4879011022117244318901841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26021392117958636367476485 4879011022117244318901841)
                    ·
                      refine ⟨3659258266587933239176381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4879011022117244318901841 3659258266587933239176381)
                      ·
                        rfl

theorem cell23_7126380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 4, 2].length) (baseStart_7126380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126380 prefixEnd_7126380 := by exact prefixLift 7126380
  have htrace : WordTrace (prefixWord ++ tailWord_7126380) baseStart_7126380 baseEnd_7126380 := by
    simpa [prefixWord, tailWord_7126380, baseEnd_7126380] using wordTrace_append hprefix tailTrace_7126380
  have hstable : (prefixWord ++ tailWord_7126380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126380).length < 2 ^ (prefixWord ++ tailWord_7126380).sum := by decide
  have hdescent : baseEnd_7126380 < baseStart_7126380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126407 : List Nat := [1, 1, 4, 2, 2, 2, 3, 3, 1, 4]
def baseStart_7126407 : Nat := 118140960795 + 7126407 * 2 ^ 59
def prefixEnd_7126407 : Nat := 4983230072969 + 3 ^ 40 * 7126407 * 2
def baseEnd_7126407 : Nat := 1219757376855201544512919

theorem tailTrace_7126407 : CollatzResearch.WordTrace tailWord_7126407 prefixEnd_7126407 1219757376855201544512919 := by
  unfold tailWord_7126407
  simp only [CollatzResearch.WordTrace]
  refine ⟨259921416693252007262953475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173280944462168004841968983 259921416693252007262953475)
  ·
    refine ⟨389882125039878010894430213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259921416693252007262953475 389882125039878010894430213)
    ·
      refine ⟨73102898444977127042705665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389882125039878010894430213 73102898444977127042705665)
      ·
        refine ⟨54827173833732845282029249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73102898444977127042705665 54827173833732845282029249)
        ·
          refine ⟨41120380375299633961521937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54827173833732845282029249 41120380375299633961521937)
          ·
            refine ⟨30840285281474725471141453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41120380375299633961521937 30840285281474725471141453)
            ·
              refine ⟨11565106980553022051678045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30840285281474725471141453 11565106980553022051678045)
              ·
                refine ⟨4336915117707383269379267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11565106980553022051678045 4336915117707383269379267)
                ·
                  refine ⟨6505372676561074904068901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4336915117707383269379267 6505372676561074904068901)
                  ·
                    refine ⟨1219757376855201544512919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6505372676561074904068901 1219757376855201544512919)
                    ·
                      rfl

theorem cell23_7126407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_7126407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126407 prefixEnd_7126407 := by exact prefixLift 7126407
  have htrace : WordTrace (prefixWord ++ tailWord_7126407) baseStart_7126407 baseEnd_7126407 := by
    simpa [prefixWord, tailWord_7126407, baseEnd_7126407] using wordTrace_append hprefix tailTrace_7126407
  have hstable : (prefixWord ++ tailWord_7126407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126407).length < 2 ^ (prefixWord ++ tailWord_7126407).sum := by decide
  have hdescent : baseEnd_7126407 < baseStart_7126407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7126424 : List Nat := [2, 1, 2, 5, 3, 1, 1, 1, 3, 4]
def baseStart_7126424 : Nat := 118140960795 + 7126424 * 2 ^ 59
def prefixEnd_7126424 : Nat := 4983230072969 + 3 ^ 40 * 7126424 * 2
def baseEnd_7126424 : Nat := 1219760286578910355675393

theorem tailTrace_7126424 : CollatzResearch.WordTrace tailWord_7126424 prefixEnd_7126424 1219760286578910355675393 := by
  unfold tailWord_7126424
  simp only [CollatzResearch.WordTrace]
  refine ⟨129961018367095209583161163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173281357822793612777548217 129961018367095209583161163)
  ·
    refine ⟨194941527550642814374741745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129961018367095209583161163 194941527550642814374741745)
    ·
      refine ⟨146206145662982110781056309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194941527550642814374741745 146206145662982110781056309)
      ·
        refine ⟨13706826155904572885724029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146206145662982110781056309 13706826155904572885724029)
        ·
          refine ⟨5140059808464214832146511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13706826155904572885724029 5140059808464214832146511)
          ·
            refine ⟨7710089712696322248219767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5140059808464214832146511 7710089712696322248219767)
            ·
              refine ⟨11565134569044483372329651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7710089712696322248219767 11565134569044483372329651)
              ·
                refine ⟨17347701853566725058494477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11565134569044483372329651 17347701853566725058494477)
                ·
                  refine ⟨6505388195087521896935429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17347701853566725058494477 6505388195087521896935429)
                  ·
                    refine ⟨1219760286578910355675393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6505388195087521896935429 1219760286578910355675393)
                    ·
                      rfl

theorem cell23_7126424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 3, 4].length) (baseStart_7126424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7126424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7126424 prefixEnd_7126424 := by exact prefixLift 7126424
  have htrace : WordTrace (prefixWord ++ tailWord_7126424) baseStart_7126424 baseEnd_7126424 := by
    simpa [prefixWord, tailWord_7126424, baseEnd_7126424] using wordTrace_append hprefix tailTrace_7126424
  have hstable : (prefixWord ++ tailWord_7126424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7126424).length < 2 ^ (prefixWord ++ tailWord_7126424).sum := by decide
  have hdescent : baseEnd_7126424 < baseStart_7126424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7126424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
