import V185TrunkScan22Chunk462

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4127960 : List Nat := [2, 1, 2, 2, 6, 1, 8]
def baseStart_4127960 : Nat := 118140960795 + 4127960 * 2 ^ 59
def prefixEnd_4127960 : Nat := 4983230072969 + 3 ^ 40 * 4127960 * 2
def baseEnd_4127960 : Nat := 52336484013179619042367

theorem tailTrace_4127960 : CollatzResearch.WordTrace tailWord_4127960 prefixEnd_4127960 52336484013179619042367 := by
  unfold tailWord_4127960
  simp only [CollatzResearch.WordTrace]
  refine ⟨75279535062556697142618667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100372713416742262856824889 75279535062556697142618667)
  ·
    refine ⟨112919302593835045713928001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75279535062556697142618667 112919302593835045713928001)
    ·
      refine ⟨84689476945376284285446001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112919302593835045713928001 84689476945376284285446001)
      ·
        refine ⟨63517107709032213214084501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84689476945376284285446001 63517107709032213214084501)
        ·
          refine ⟨2977364423860884994410211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63517107709032213214084501 2977364423860884994410211)
          ·
            refine ⟨4466046635791327491615317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2977364423860884994410211 4466046635791327491615317)
            ·
              refine ⟨52336484013179619042367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4466046635791327491615317 52336484013179619042367)
              ·
                rfl

theorem cell22_4127960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 8].length) (baseStart_4127960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4127960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4127960 prefixEnd_4127960 := by exact prefixLift 4127960
  have htrace : WordTrace (prefixWord ++ tailWord_4127960) baseStart_4127960 baseEnd_4127960 := by
    simpa [prefixWord, tailWord_4127960, baseEnd_4127960] using wordTrace_append hprefix tailTrace_4127960
  have hstable : (prefixWord ++ tailWord_4127960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4127960).length < 2 ^ (prefixWord ++ tailWord_4127960).sum := by decide
  have hdescent : baseEnd_4127960 < baseStart_4127960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4127960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128026 : List Nat := [3, 1, 1, 3, 3, 3, 2, 2, 1, 3]
def baseStart_4128026 : Nat := 118140960795 + 4128026 * 2 ^ 59
def prefixEnd_4128026 : Nat := 4983230072969 + 3 ^ 40 * 4128026 * 2
def baseEnd_4128026 : Nat := 1413107661504647541993707

theorem tailTrace_4128026 : CollatzResearch.WordTrace tailWord_4128026 prefixEnd_4128026 1413107661504647541993707 := by
  unfold tailWord_4128026
  simp only [CollatzResearch.WordTrace]
  refine ⟨37640369335718571889284983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100374318228582858371426621 37640369335718571889284983)
  ·
    refine ⟨56460554003577857833927475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37640369335718571889284983 56460554003577857833927475)
    ·
      refine ⟨84690831005366786750891213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56460554003577857833927475 84690831005366786750891213)
      ·
        refine ⟨31759061627012545031584205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84690831005366786750891213 31759061627012545031584205)
        ·
          refine ⟨11909648110129704386844077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31759061627012545031584205 11909648110129704386844077)
          ·
            refine ⟨4466118041298639145066529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11909648110129704386844077 4466118041298639145066529)
            ·
              refine ⟨3349588530973979358799897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4466118041298639145066529 3349588530973979358799897)
              ·
                refine ⟨2512191398230484519099923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3349588530973979358799897 2512191398230484519099923)
                ·
                  refine ⟨3768287097345726778649885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2512191398230484519099923 3768287097345726778649885)
                  ·
                    refine ⟨1413107661504647541993707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3768287097345726778649885 1413107661504647541993707)
                    ·
                      rfl

theorem cell22_4128026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 1, 3].length) (baseStart_4128026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128026 prefixEnd_4128026 := by exact prefixLift 4128026
  have htrace : WordTrace (prefixWord ++ tailWord_4128026) baseStart_4128026 baseEnd_4128026 := by
    simpa [prefixWord, tailWord_4128026, baseEnd_4128026] using wordTrace_append hprefix tailTrace_4128026
  have hstable : (prefixWord ++ tailWord_4128026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128026).length < 2 ^ (prefixWord ++ tailWord_4128026).sum := by decide
  have hdescent : baseEnd_4128026 < baseStart_4128026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128033 : List Nat := [1, 2, 3, 2, 1, 1, 1, 5, 6]
def baseStart_4128033 : Nat := 118140960795 + 4128033 * 2 ^ 59
def prefixEnd_4128033 : Nat := 4983230072969 + 3 ^ 40 * 4128033 * 2
def baseEnd_4128033 : Nat := 471036685915900619022895

theorem tailTrace_4128033 : CollatzResearch.WordTrace tailWord_4128033 prefixEnd_4128033 471036685915900619022895 := by
  unfold tailWord_4128033
  simp only [CollatzResearch.WordTrace]
  refine ⟨150561732653848927752644753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100374488435899285168429835 150561732653848927752644753)
  ·
    refine ⟨112921299490386695814483565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150561732653848927752644753 112921299490386695814483565)
    ·
      refine ⟨42345487308895010930431337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112921299490386695814483565 42345487308895010930431337)
      ·
        refine ⟨31759115481671258197823503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42345487308895010930431337 31759115481671258197823503)
        ·
          refine ⟨47638673222506887296735255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31759115481671258197823503 47638673222506887296735255)
          ·
            refine ⟨71458009833760330945102883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47638673222506887296735255 71458009833760330945102883)
            ·
              refine ⟨107187014750640496417654325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71458009833760330945102883 107187014750640496417654325)
              ·
                refine ⟨10048782632872546539155093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107187014750640496417654325 10048782632872546539155093)
                ·
                  refine ⟨471036685915900619022895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10048782632872546539155093 471036685915900619022895)
                  ·
                    rfl

theorem cell22_4128033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 6].length) (baseStart_4128033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128033 prefixEnd_4128033 := by exact prefixLift 4128033
  have htrace : WordTrace (prefixWord ++ tailWord_4128033) baseStart_4128033 baseEnd_4128033 := by
    simpa [prefixWord, tailWord_4128033, baseEnd_4128033] using wordTrace_append hprefix tailTrace_4128033
  have hstable : (prefixWord ++ tailWord_4128033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128033).length < 2 ^ (prefixWord ++ tailWord_4128033).sum := by decide
  have hdescent : baseEnd_4128033 < baseStart_4128033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128050 : List Nat := [3, 2, 1, 1, 4, 2, 1, 2, 6]
def baseStart_4128050 : Nat := 118140960795 + 4128050 * 2 ^ 59
def prefixEnd_4128050 : Nat := 4983230072969 + 3 ^ 40 * 4128050 * 2
def baseEnd_4128050 : Nat := 471038625731706493131211

theorem tailTrace_4128050 : CollatzResearch.WordTrace tailWord_4128050 prefixEnd_4128050 471038625731706493131211 := by
  unfold tailWord_4128050
  simp only [CollatzResearch.WordTrace]
  refine ⟨37640588173696834914003401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100374901796524893104009069 37640588173696834914003401)
  ·
    refine ⟨28230441130272626185502551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37640588173696834914003401 28230441130272626185502551)
    ·
      refine ⟨42345661695408939278253827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28230441130272626185502551 42345661695408939278253827)
      ·
        refine ⟨63518492543113408917380741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42345661695408939278253827 63518492543113408917380741)
        ·
          refine ⟨11909717351833764172008889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63518492543113408917380741 11909717351833764172008889)
          ·
            refine ⟨8932288013875323129006667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11909717351833764172008889 8932288013875323129006667)
            ·
              refine ⟨13398432020812984693510001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8932288013875323129006667 13398432020812984693510001)
              ·
                refine ⟨10048824015609738520132501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13398432020812984693510001 10048824015609738520132501)
                ·
                  refine ⟨471038625731706493131211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10048824015609738520132501 471038625731706493131211)
                  ·
                    rfl

theorem cell22_4128050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_4128050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128050 prefixEnd_4128050 := by exact prefixLift 4128050
  have htrace : WordTrace (prefixWord ++ tailWord_4128050) baseStart_4128050 baseEnd_4128050 := by
    simpa [prefixWord, tailWord_4128050, baseEnd_4128050] using wordTrace_append hprefix tailTrace_4128050
  have hstable : (prefixWord ++ tailWord_4128050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128050).length < 2 ^ (prefixWord ++ tailWord_4128050).sum := by decide
  have hdescent : baseEnd_4128050 < baseStart_4128050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128052 : List Nat := [2, 5, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_4128052 : Nat := 118140960795 + 4128052 * 2 ^ 59
def prefixEnd_4128052 : Nat := 4983230072969 + 3 ^ 40 * 4128052 * 2
def baseEnd_4128052 : Nat := 1413116561835992140843627

theorem tailTrace_4128052 : CollatzResearch.WordTrace tailWord_4128052 prefixEnd_4128052 1413116561835992140843627 := by
  unfold tailWord_4128052
  simp only [CollatzResearch.WordTrace]
  refine ⟨75281212820390046998793205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100374950427186729331724273 75281212820390046998793205)
  ·
    refine ⟨7057613701911566906136863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75281212820390046998793205 7057613701911566906136863)
    ·
      refine ⟨10586420552867350359205295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7057613701911566906136863 10586420552867350359205295)
      ·
        refine ⟨15879630829301025538807943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10586420552867350359205295 15879630829301025538807943)
        ·
          refine ⟨23819446243951538308211915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15879630829301025538807943 23819446243951538308211915)
          ·
            refine ⟨35729169365927307462317873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23819446243951538308211915 35729169365927307462317873)
            ·
              refine ⟨26796877024445480596738405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35729169365927307462317873 26796877024445480596738405)
              ·
                refine ⟨5024414442083527611888451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26796877024445480596738405 5024414442083527611888451)
                ·
                  refine ⟨7536621663125291417832677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5024414442083527611888451 7536621663125291417832677)
                  ·
                    refine ⟨1413116561835992140843627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7536621663125291417832677 1413116561835992140843627)
                    ·
                      rfl

theorem cell22_4128052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_4128052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128052 prefixEnd_4128052 := by exact prefixLift 4128052
  have htrace : WordTrace (prefixWord ++ tailWord_4128052) baseStart_4128052 baseEnd_4128052 := by
    simpa [prefixWord, tailWord_4128052, baseEnd_4128052] using wordTrace_append hprefix tailTrace_4128052
  have hstable : (prefixWord ++ tailWord_4128052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128052).length < 2 ^ (prefixWord ++ tailWord_4128052).sum := by decide
  have hdescent : baseEnd_4128052 < baseStart_4128052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128078 : List Nat := [4, 1, 1, 1, 1, 1, 13]
def baseStart_4128078 : Nat := 118140960795 + 4128078 * 2 ^ 59
def prefixEnd_4128078 : Nat := 4983230072969 + 3 ^ 40 * 4128078 * 2
def baseEnd_4128078 : Nat := 52337980080271731099761

theorem tailTrace_4128078 : CollatzResearch.WordTrace tailWord_4128078 prefixEnd_4128078 52337980080271731099761 := by
  unfold tailWord_4128078
  simp only [CollatzResearch.WordTrace]
  refine ⟨18820421742335737554754111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100375582625790600292021925 18820421742335737554754111)
  ·
    refine ⟨28230632613503606332131167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18820421742335737554754111 28230632613503606332131167)
    ·
      refine ⟨42345948920255409498196751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28230632613503606332131167 42345948920255409498196751)
      ·
        refine ⟨63518923380383114247295127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42345948920255409498196751 63518923380383114247295127)
        ·
          refine ⟨95278385070574671370942691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63518923380383114247295127 95278385070574671370942691)
          ·
            refine ⟨142917577605862007056414037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95278385070574671370942691 142917577605862007056414037)
            ·
              refine ⟨52337980080271731099761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 142917577605862007056414037 52337980080271731099761)
              ·
                rfl

theorem cell22_4128078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 13].length) (baseStart_4128078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128078 prefixEnd_4128078 := by exact prefixLift 4128078
  have htrace : WordTrace (prefixWord ++ tailWord_4128078) baseStart_4128078 baseEnd_4128078 := by
    simpa [prefixWord, tailWord_4128078, baseEnd_4128078] using wordTrace_append hprefix tailTrace_4128078
  have hstable : (prefixWord ++ tailWord_4128078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128078).length < 2 ^ (prefixWord ++ tailWord_4128078).sum := by decide
  have hdescent : baseEnd_4128078 < baseStart_4128078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128099 : List Nat := [1, 1, 1, 5, 2, 3, 3, 1, 2, 3]
def baseStart_4128099 : Nat := 118140960795 + 4128099 * 2 ^ 59
def prefixEnd_4128099 : Nat := 4983230072969 + 3 ^ 40 * 4128099 * 2
def baseEnd_4128099 : Nat := 1413132650896499684918483

theorem tailTrace_4128099 : CollatzResearch.WordTrace tailWord_4128099 prefixEnd_4128099 1413132650896499684918483 := by
  unfold tailWord_4128099
  simp only [CollatzResearch.WordTrace]
  refine ⟨150564139871609821024547351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100376093247739880683031567 150564139871609821024547351)
  ·
    refine ⟨225846209807414731536821027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150564139871609821024547351 225846209807414731536821027)
    ·
      refine ⟨338769314711122097305231541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225846209807414731536821027 338769314711122097305231541)
      ·
        refine ⟨31759623254167696622365457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 338769314711122097305231541 31759623254167696622365457)
        ·
          refine ⟨23819717440625772466774093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31759623254167696622365457 23819717440625772466774093)
          ·
            refine ⟨8932394040234664675040285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23819717440625772466774093 8932394040234664675040285)
            ·
              refine ⟨3349647765087999253140107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8932394040234664675040285 3349647765087999253140107)
              ·
                refine ⟨5024471647631998879710161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3349647765087999253140107 5024471647631998879710161)
                ·
                  refine ⟨3768353735723999159782621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5024471647631998879710161 3768353735723999159782621)
                  ·
                    refine ⟨1413132650896499684918483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3768353735723999159782621 1413132650896499684918483)
                    ·
                      rfl

theorem cell22_4128099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 2, 3].length) (baseStart_4128099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128099 prefixEnd_4128099 := by exact prefixLift 4128099
  have htrace : WordTrace (prefixWord ++ tailWord_4128099) baseStart_4128099 baseEnd_4128099 := by
    simpa [prefixWord, tailWord_4128099, baseEnd_4128099] using wordTrace_append hprefix tailTrace_4128099
  have hstable : (prefixWord ++ tailWord_4128099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128099).length < 2 ^ (prefixWord ++ tailWord_4128099).sum := by decide
  have hdescent : baseEnd_4128099 < baseStart_4128099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128123 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 9]
def baseStart_4128123 : Nat := 118140960795 + 4128123 * 2 ^ 59
def prefixEnd_4128123 : Nat := 4983230072969 + 3 ^ 40 * 4128123 * 2
def baseEnd_4128123 : Nat := 471046955528990540772803

theorem tailTrace_4128123 : CollatzResearch.WordTrace tailWord_4128123 prefixEnd_4128123 471046955528990540772803 := by
  unfold tailWord_4128123
  simp only [CollatzResearch.WordTrace]
  refine ⟨150565015223522873123421023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100376676815681915415614015 150565015223522873123421023)
  ·
    refine ⟨225847522835284309685131535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150565015223522873123421023 225847522835284309685131535)
    ·
      refine ⟨338771284252926464527697303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225847522835284309685131535 338771284252926464527697303)
      ·
        refine ⟨508156926379389696791545955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338771284252926464527697303 508156926379389696791545955)
        ·
          refine ⟨762235389569084545187318933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508156926379389696791545955 762235389569084545187318933)
          ·
            refine ⟨35729783886050838055655575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 762235389569084545187318933 35729783886050838055655575)
            ·
              refine ⟨53594675829076257083483363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35729783886050838055655575 53594675829076257083483363)
              ·
                refine ⟨80392013743614385625225045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53594675829076257083483363 80392013743614385625225045)
                ·
                  refine ⟨471046955528990540772803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80392013743614385625225045 471046955528990540772803)
                  ·
                    rfl

theorem cell22_4128123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 9].length) (baseStart_4128123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128123 prefixEnd_4128123 := by exact prefixLift 4128123
  have htrace : WordTrace (prefixWord ++ tailWord_4128123) baseStart_4128123 baseEnd_4128123 := by
    simpa [prefixWord, tailWord_4128123, baseEnd_4128123] using wordTrace_append hprefix tailTrace_4128123
  have hstable : (prefixWord ++ tailWord_4128123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128123).length < 2 ^ (prefixWord ++ tailWord_4128123).sum := by decide
  have hdescent : baseEnd_4128123 < baseStart_4128123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128140 : List Nat := [2, 2, 1, 2, 1, 3, 2, 4, 5]
def baseStart_4128140 : Nat := 118140960795 + 4128140 * 2 ^ 59
def prefixEnd_4128140 : Nat := 4983230072969 + 3 ^ 40 * 4128140 * 2
def baseEnd_4128140 : Nat := 471048895344796414881119

theorem tailTrace_4128140 : CollatzResearch.WordTrace tailWord_4128140 prefixEnd_4128140 471048895344796414881119 := by
  unfold tailWord_4128140
  simp only [CollatzResearch.WordTrace]
  refine ⟨75282817632230642513394937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100377090176307523351193249 75282817632230642513394937)
  ·
    refine ⟨56462113224172981885046203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75282817632230642513394937 56462113224172981885046203)
    ·
      refine ⟨84693169836259472827569305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56462113224172981885046203 84693169836259472827569305)
      ·
        refine ⟨63519877377194604620676979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84693169836259472827569305 63519877377194604620676979)
        ·
          refine ⟨95279816065791906931015469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63519877377194604620676979 95279816065791906931015469)
          ·
            refine ⟨35729931024671965099130801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95279816065791906931015469 35729931024671965099130801)
            ·
              refine ⟨26797448268503973824348101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35729931024671965099130801 26797448268503973824348101)
              ·
                refine ⟨5024521550344495092065269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26797448268503973824348101 5024521550344495092065269)
                ·
                  refine ⟨471048895344796414881119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5024521550344495092065269 471048895344796414881119)
                  ·
                    rfl

theorem cell22_4128140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_4128140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128140 prefixEnd_4128140 := by exact prefixLift 4128140
  have htrace : WordTrace (prefixWord ++ tailWord_4128140) baseStart_4128140 baseEnd_4128140 := by
    simpa [prefixWord, tailWord_4128140, baseEnd_4128140] using wordTrace_append hprefix tailTrace_4128140
  have hstable : (prefixWord ++ tailWord_4128140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128140).length < 2 ^ (prefixWord ++ tailWord_4128140).sum := by decide
  have hdescent : baseEnd_4128140 < baseStart_4128140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128157 : List Nat := [1, 4, 2, 1, 3, 2, 1, 3, 5]
def baseStart_4128157 : Nat := 118140960795 + 4128157 * 2 ^ 59
def prefixEnd_4128157 : Nat := 4983230072969 + 3 ^ 40 * 4128157 * 2
def baseEnd_4128157 : Nat := 471050835160602288989435

theorem tailTrace_4128157 : CollatzResearch.WordTrace tailWord_4128157 prefixEnd_4128157 471050835160602288989435 := by
  unfold tailWord_4128157
  simp only [CollatzResearch.WordTrace]
  refine ⟨150566255305399696930158725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100377503536933131286772483 150566255305399696930158725)
  ·
    refine ⟨28231172869762443174404761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150566255305399696930158725 28231172869762443174404761)
    ·
      refine ⟨21173379652321832380803571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28231172869762443174404761 21173379652321832380803571)
      ·
        refine ⟨31760069478482748571205357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21173379652321832380803571 31760069478482748571205357)
        ·
          refine ⟨11910026054431030714202009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31760069478482748571205357 11910026054431030714202009)
          ·
            refine ⟨8932519540823273035651507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11910026054431030714202009 8932519540823273035651507)
            ·
              refine ⟨13398779311234909553477261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8932519540823273035651507 13398779311234909553477261)
              ·
                refine ⟨5024542241713091082553973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13398779311234909553477261 5024542241713091082553973)
                ·
                  refine ⟨471050835160602288989435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5024542241713091082553973 471050835160602288989435)
                  ·
                    rfl

theorem cell22_4128157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_4128157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128157 prefixEnd_4128157 := by exact prefixLift 4128157
  have htrace : WordTrace (prefixWord ++ tailWord_4128157) baseStart_4128157 baseEnd_4128157 := by
    simpa [prefixWord, tailWord_4128157, baseEnd_4128157] using wordTrace_append hprefix tailTrace_4128157
  have hstable : (prefixWord ++ tailWord_4128157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128157).length < 2 ^ (prefixWord ++ tailWord_4128157).sum := by decide
  have hdescent : baseEnd_4128157 < baseStart_4128157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128200 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 3, 5]
def baseStart_4128200 : Nat := 118140960795 + 4128200 * 2 ^ 59
def prefixEnd_4128200 : Nat := 4983230072969 + 3 ^ 40 * 4128200 * 2
def baseEnd_4128200 : Nat := 1413167225260569088143173

theorem tailTrace_4128200 : CollatzResearch.WordTrace tailWord_4128200 prefixEnd_4128200 1413167225260569088143173 := by
  unfold tailWord_4128200
  simp only [CollatzResearch.WordTrace]
  refine ⟨75283911822121957636987027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100378549096162610182649369 75283911822121957636987027)
  ·
    refine ⟨112925867733182936455480541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75283911822121957636987027 112925867733182936455480541)
    ·
      refine ⟨42347200399943601170805203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112925867733182936455480541 42347200399943601170805203)
      ·
        refine ⟨63520800599915401756207805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42347200399943601170805203 63520800599915401756207805)
        ·
          refine ⟨23820300224968275658577927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63520800599915401756207805 23820300224968275658577927)
          ·
            refine ⟨35730450337452413487866891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23820300224968275658577927 35730450337452413487866891)
            ·
              refine ⟨53595675506178620231800337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35730450337452413487866891 53595675506178620231800337)
              ·
                refine ⟨40196756629633965173850253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53595675506178620231800337 40196756629633965173850253)
                ·
                  refine ⟨15073783736112736940193845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40196756629633965173850253 15073783736112736940193845)
                  ·
                    refine ⟨1413167225260569088143173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15073783736112736940193845 1413167225260569088143173)
                    ·
                      rfl

theorem cell22_4128200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_4128200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128200 prefixEnd_4128200 := by exact prefixLift 4128200
  have htrace : WordTrace (prefixWord ++ tailWord_4128200) baseStart_4128200 baseEnd_4128200 := by
    simpa [prefixWord, tailWord_4128200, baseEnd_4128200] using wordTrace_append hprefix tailTrace_4128200
  have hstable : (prefixWord ++ tailWord_4128200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128200).length < 2 ^ (prefixWord ++ tailWord_4128200).sum := by decide
  have hdescent : baseEnd_4128200 < baseStart_4128200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128215 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 4, 4]
def baseStart_4128215 : Nat := 118140960795 + 4128215 * 2 ^ 59
def prefixEnd_4128215 : Nat := 4983230072969 + 3 ^ 40 * 4128215 * 2
def baseEnd_4128215 : Nat := 1413172360067114049018127

theorem tailTrace_4128215 : CollatzResearch.WordTrace tailWord_4128215 prefixEnd_4128215 1413172360067114049018127 := by
  unfold tailWord_4128215
  simp only [CollatzResearch.WordTrace]
  refine ⟨150568370739189572835770099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100378913826126381890513399 150568370739189572835770099)
  ·
    refine ⟨225852556108784359253655149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150568370739189572835770099 225852556108784359253655149)
    ·
      refine ⟨84694708540794134720120681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225852556108784359253655149 84694708540794134720120681)
      ·
        refine ⟨63521031405595601040090511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84694708540794134720120681 63521031405595601040090511)
        ·
          refine ⟨95281547108393401560135767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63521031405595601040090511 95281547108393401560135767)
          ·
            refine ⟨142922320662590102340203651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95281547108393401560135767 142922320662590102340203651)
            ·
              refine ⟨214383480993885153510305477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142922320662590102340203651 214383480993885153510305477)
              ·
                refine ⟨40196902686353466283182277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214383480993885153510305477 40196902686353466283182277)
                ·
                  refine ⟨7536919253691274928096677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40196902686353466283182277 7536919253691274928096677)
                  ·
                    refine ⟨1413172360067114049018127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7536919253691274928096677 1413172360067114049018127)
                    ·
                      rfl

theorem cell22_4128215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_4128215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128215 prefixEnd_4128215 := by exact prefixLift 4128215
  have htrace : WordTrace (prefixWord ++ tailWord_4128215) baseStart_4128215 baseEnd_4128215 := by
    simpa [prefixWord, tailWord_4128215, baseEnd_4128215] using wordTrace_append hprefix tailTrace_4128215
  have hstable : (prefixWord ++ tailWord_4128215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128215).length < 2 ^ (prefixWord ++ tailWord_4128215).sum := by decide
  have hdescent : baseEnd_4128215 < baseStart_4128215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128217 : List Nat := [1, 2, 1, 2, 4, 3, 2, 1, 1, 5]
def baseStart_4128217 : Nat := 118140960795 + 4128217 * 2 ^ 59
def prefixEnd_4128217 : Nat := 4983230072969 + 3 ^ 40 * 4128217 * 2
def baseEnd_4128217 : Nat := 1413173044707986710468121

theorem tailTrace_4128217 : CollatzResearch.WordTrace tailWord_4128217 prefixEnd_4128217 1413173044707986710468121 := by
  unfold tailWord_4128217
  simp only [CollatzResearch.WordTrace]
  refine ⟨150568443685182327177342905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100378962456788218118228603 150568443685182327177342905)
  ·
    refine ⟨112926332763886745383007179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150568443685182327177342905 112926332763886745383007179)
    ·
      refine ⟨169389499145830118074510769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112926332763886745383007179 169389499145830118074510769)
      ·
        refine ⟨127042124359372588555883077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169389499145830118074510769 127042124359372588555883077)
        ·
          refine ⟨23820398317382360354228077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127042124359372588555883077 23820398317382360354228077)
          ·
            refine ⟨8932649369018385132835529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23820398317382360354228077 8932649369018385132835529)
            ·
              refine ⟨6699487026763788849626647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8932649369018385132835529 6699487026763788849626647)
              ·
                refine ⟨10049230540145683274439971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6699487026763788849626647 10049230540145683274439971)
                ·
                  refine ⟨15073845810218524911659957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10049230540145683274439971 15073845810218524911659957)
                  ·
                    refine ⟨1413173044707986710468121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15073845810218524911659957 1413173044707986710468121)
                    ·
                      rfl

theorem cell22_4128217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 5].length) (baseStart_4128217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128217 prefixEnd_4128217 := by exact prefixLift 4128217
  have htrace : WordTrace (prefixWord ++ tailWord_4128217) baseStart_4128217 baseEnd_4128217 := by
    simpa [prefixWord, tailWord_4128217, baseEnd_4128217] using wordTrace_append hprefix tailTrace_4128217
  have hstable : (prefixWord ++ tailWord_4128217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128217).length < 2 ^ (prefixWord ++ tailWord_4128217).sum := by decide
  have hdescent : baseEnd_4128217 < baseStart_4128217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128313 : List Nat := [1, 2, 1, 5, 1, 3, 3, 2, 1, 3]
def baseStart_4128313 : Nat := 118140960795 + 4128313 * 2 ^ 59
def prefixEnd_4128313 : Nat := 4983230072969 + 3 ^ 40 * 4128313 * 2
def baseEnd_4128313 : Nat := 1413205907469874460067827

theorem tailTrace_4128313 : CollatzResearch.WordTrace tailWord_4128313 prefixEnd_4128313 1413205907469874460067827 := by
  unfold tailWord_4128313
  simp only [CollatzResearch.WordTrace]
  refine ⟨150571945092834535572837593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100381296728556357048558395 150571945092834535572837593)
  ·
    refine ⟨112928958819625901679628195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150571945092834535572837593 112928958819625901679628195)
    ·
      refine ⟨169393438229438852519442293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112928958819625901679628195 169393438229438852519442293)
      ·
        refine ⟨15880634834009892423697715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169393438229438852519442293 15880634834009892423697715)
        ·
          refine ⟨23820952251014838635546573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15880634834009892423697715 23820952251014838635546573)
          ·
            refine ⟨8932857094130564488329965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23820952251014838635546573 8932857094130564488329965)
            ·
              refine ⟨3349821410298961683123737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8932857094130564488329965 3349821410298961683123737)
              ·
                refine ⟨2512366057724221262342803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3349821410298961683123737 2512366057724221262342803)
                ·
                  refine ⟨3768549086586331893514205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2512366057724221262342803 3768549086586331893514205)
                  ·
                    refine ⟨1413205907469874460067827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3768549086586331893514205 1413205907469874460067827)
                    ·
                      rfl

theorem cell22_4128313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 1, 3].length) (baseStart_4128313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128313 prefixEnd_4128313 := by exact prefixLift 4128313
  have htrace : WordTrace (prefixWord ++ tailWord_4128313) baseStart_4128313 baseEnd_4128313 := by
    simpa [prefixWord, tailWord_4128313, baseEnd_4128313] using wordTrace_append hprefix tailTrace_4128313
  have hstable : (prefixWord ++ tailWord_4128313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128313).length < 2 ^ (prefixWord ++ tailWord_4128313).sum := by decide
  have hdescent : baseEnd_4128313 < baseStart_4128313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128356 : List Nat := [2, 3, 1, 1, 2, 4, 3, 1, 1, 4]
def baseStart_4128356 : Nat := 118140960795 + 4128356 * 2 ^ 59
def prefixEnd_4128356 : Nat := 4983230072969 + 3 ^ 40 * 4128356 * 2
def baseEnd_4128356 : Nat := 1413220627248636681242695

theorem tailTrace_4128356 : CollatzResearch.WordTrace tailWord_4128356 prefixEnd_4128356 1413220627248636681242695 := by
  unfold tailWord_4128356
  simp only [CollatzResearch.WordTrace]
  refine ⟨75286756715839376958326461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100382342287785835944435281 75286756715839376958326461)
  ·
    refine ⟨28232533768439766359372423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75286756715839376958326461 28232533768439766359372423)
    ·
      refine ⟨42348800652659649539058635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28232533768439766359372423 42348800652659649539058635)
      ·
        refine ⟨63523200978989474308587953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42348800652659649539058635 63523200978989474308587953)
        ·
          refine ⟨47642400734242105731440965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63523200978989474308587953 47642400734242105731440965)
          ·
            refine ⟨8932950137670394824645181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47642400734242105731440965 8932950137670394824645181)
            ·
              refine ⟨3349856301626398059241943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8932950137670394824645181 3349856301626398059241943)
              ·
                refine ⟨5024784452439597088862915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3349856301626398059241943 5024784452439597088862915)
                ·
                  refine ⟨7537176678659395633294373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5024784452439597088862915 7537176678659395633294373)
                  ·
                    refine ⟨1413220627248636681242695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7537176678659395633294373 1413220627248636681242695)
                    ·
                      rfl

theorem cell22_4128356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_4128356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128356 prefixEnd_4128356 := by exact prefixLift 4128356
  have htrace : WordTrace (prefixWord ++ tailWord_4128356) baseStart_4128356 baseEnd_4128356 := by
    simpa [prefixWord, tailWord_4128356, baseEnd_4128356] using wordTrace_append hprefix tailTrace_4128356
  have hstable : (prefixWord ++ tailWord_4128356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128356).length < 2 ^ (prefixWord ++ tailWord_4128356).sum := by decide
  have hdescent : baseEnd_4128356 < baseStart_4128356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128431 : List Nat := [1, 1, 2, 1, 2, 4, 1, 6, 1, 3]
def baseStart_4128431 : Nat := 118140960795 + 4128431 * 2 ^ 59
def prefixEnd_4128431 : Nat := 4983230072969 + 3 ^ 40 * 4128431 * 2
def baseEnd_4128431 : Nat := 1413246301281361485617465

theorem tailTrace_4128431 : CollatzResearch.WordTrace tailWord_4128431 prefixEnd_4128431 1413246301281361485617465 := by
  unfold tailWord_4128431
  simp only [CollatzResearch.WordTrace]
  refine ⟨150576248906407041725633147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100384165937604694483755431 150576248906407041725633147)
  ·
    refine ⟨225864373359610562588449721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150576248906407041725633147 225864373359610562588449721)
    ·
      refine ⟨169398280019707921941337291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225864373359610562588449721 169398280019707921941337291)
      ·
        refine ⟨254097420029561882912005937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169398280019707921941337291 254097420029561882912005937)
        ·
          refine ⟨190573065022171412184004453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254097420029561882912005937 190573065022171412184004453)
          ·
            refine ⟨35732449691657139784500835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190573065022171412184004453 35732449691657139784500835)
            ·
              refine ⟨53598674537485709676751253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35732449691657139784500835 53598674537485709676751253)
              ·
                refine ⟨2512437868944642641097715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53598674537485709676751253 2512437868944642641097715)
                ·
                  refine ⟨3768656803416963961646573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2512437868944642641097715 3768656803416963961646573)
                  ·
                    refine ⟨1413246301281361485617465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3768656803416963961646573 1413246301281361485617465)
                    ·
                      rfl

theorem cell22_4128431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 1, 3].length) (baseStart_4128431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128431 prefixEnd_4128431 := by exact prefixLift 4128431
  have htrace : WordTrace (prefixWord ++ tailWord_4128431) baseStart_4128431 baseEnd_4128431 := by
    simpa [prefixWord, tailWord_4128431, baseEnd_4128431] using wordTrace_append hprefix tailTrace_4128431
  have hstable : (prefixWord ++ tailWord_4128431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128431).length < 2 ^ (prefixWord ++ tailWord_4128431).sum := by decide
  have hdescent : baseEnd_4128431 < baseStart_4128431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128461 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 7]
def baseStart_4128461 : Nat := 118140960795 + 4128461 * 2 ^ 59
def prefixEnd_4128461 : Nat := 4983230072969 + 3 ^ 40 * 4128461 * 2
def baseEnd_4128461 : Nat := 471085523631483802455791

theorem tailTrace_4128461 : CollatzResearch.WordTrace tailWord_4128461 prefixEnd_4128461 471085523631483802455791 := by
  unfold tailWord_4128461
  simp only [CollatzResearch.WordTrace]
  refine ⟨150577343096298356849225237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100384895397532237899483491 150577343096298356849225237)
  ·
    refine ⟨7058312957638985477307433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150577343096298356849225237 7058312957638985477307433)
    ·
      refine ⟨5293734718229239107980575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7058312957638985477307433 5293734718229239107980575)
      ·
        refine ⟨7940602077343858661970863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5293734718229239107980575 7940602077343858661970863)
        ·
          refine ⟨11910903116015787992956295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7940602077343858661970863 11910903116015787992956295)
          ·
            refine ⟨17866354674023681989434443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11910903116015787992956295 17866354674023681989434443)
            ·
              refine ⟨26799532011035522984151665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17866354674023681989434443 26799532011035522984151665)
              ·
                refine ⟨20099649008276642238113749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26799532011035522984151665 20099649008276642238113749)
                ·
                  refine ⟨471085523631483802455791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20099649008276642238113749 471085523631483802455791)
                  ·
                    rfl

theorem cell22_4128461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_4128461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128461 prefixEnd_4128461 := by exact prefixLift 4128461
  have htrace : WordTrace (prefixWord ++ tailWord_4128461) baseStart_4128461 baseEnd_4128461 := by
    simpa [prefixWord, tailWord_4128461, baseEnd_4128461] using wordTrace_append hprefix tailTrace_4128461
  have hstable : (prefixWord ++ tailWord_4128461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128461).length < 2 ^ (prefixWord ++ tailWord_4128461).sum := by decide
  have hdescent : baseEnd_4128461 < baseStart_4128461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128504 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 6, 3]
def baseStart_4128504 : Nat := 118140960795 + 4128504 * 2 ^ 59
def prefixEnd_4128504 : Nat := 4983230072969 + 3 ^ 40 * 4128504 * 2
def baseEnd_4128504 : Nat := 1413271290673213628542241

theorem tailTrace_4128504 : CollatzResearch.WordTrace tailWord_4128504 prefixEnd_4128504 1413271290673213628542241 := by
  unfold tailWord_4128504
  simp only [CollatzResearch.WordTrace]
  refine ⟨75289455717571287596520283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100385940956761716795360377 75289455717571287596520283)
  ·
    refine ⟨112934183576356931394780425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75289455717571287596520283 112934183576356931394780425)
    ·
      refine ⟨84700637682267698546085319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112934183576356931394780425 84700637682267698546085319)
      ·
        refine ⟨127050956523401547819127979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84700637682267698546085319 127050956523401547819127979)
        ·
          refine ⟨190576434785102321728691969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127050956523401547819127979 190576434785102321728691969)
          ·
            refine ⟨142932326088826741296518977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190576434785102321728691969 142932326088826741296518977)
            ·
              refine ⟨107199244566620055972389233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142932326088826741296518977 107199244566620055972389233)
              ·
                refine ⟨80399433424965041979291925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107199244566620055972389233 80399433424965041979291925)
                ·
                  refine ⟨3768723441795236342779309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80399433424965041979291925 3768723441795236342779309)
                  ·
                    refine ⟨1413271290673213628542241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3768723441795236342779309 1413271290673213628542241)
                    ·
                      rfl

theorem cell22_4128504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_4128504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128504 prefixEnd_4128504 := by exact prefixLift 4128504
  have htrace : WordTrace (prefixWord ++ tailWord_4128504) baseStart_4128504 baseEnd_4128504 := by
    simpa [prefixWord, tailWord_4128504, baseEnd_4128504] using wordTrace_append hprefix tailTrace_4128504
  have hstable : (prefixWord ++ tailWord_4128504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128504).length < 2 ^ (prefixWord ++ tailWord_4128504).sum := by decide
  have hdescent : baseEnd_4128504 < baseStart_4128504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128538 : List Nat := [3, 1, 1, 3, 2, 3, 2, 2, 2, 3]
def baseStart_4128538 : Nat := 118140960795 + 4128538 * 2 ^ 59
def prefixEnd_4128538 : Nat := 4983230072969 + 3 ^ 40 * 4128538 * 2
def baseEnd_4128538 : Nat := 1413282929568048873192137

theorem tailTrace_4128538 : CollatzResearch.WordTrace tailWord_4128538 prefixEnd_4128538 1413282929568048873192137 := by
  unfold tailWord_4128538
  simp only [CollatzResearch.WordTrace]
  refine ⟨37645037879254849749944567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100386767678012932666518845 37645037879254849749944567)
  ·
    refine ⟨56467556818882274624916851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37645037879254849749944567 56467556818882274624916851)
    ·
      refine ⟨84701335228323411937375277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56467556818882274624916851 84701335228323411937375277)
      ·
        refine ⟨31763000710621279476515729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84701335228323411937375277 31763000710621279476515729)
        ·
          refine ⟨23822250532965959607386797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31763000710621279476515729 23822250532965959607386797)
          ·
            refine ⟨8933343949862234852770049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23822250532965959607386797 8933343949862234852770049)
            ·
              refine ⟨6700007962396676139577537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8933343949862234852770049 6700007962396676139577537)
              ·
                refine ⟨5025005971797507104683153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6700007962396676139577537 5025005971797507104683153)
                ·
                  refine ⟨3768754478848130328512365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5025005971797507104683153 3768754478848130328512365)
                  ·
                    refine ⟨1413282929568048873192137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3768754478848130328512365 1413282929568048873192137)
                    ·
                      rfl

theorem cell22_4128538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_4128538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128538 prefixEnd_4128538 := by exact prefixLift 4128538
  have htrace : WordTrace (prefixWord ++ tailWord_4128538) baseStart_4128538 baseEnd_4128538 := by
    simpa [prefixWord, tailWord_4128538, baseEnd_4128538] using wordTrace_append hprefix tailTrace_4128538
  have hstable : (prefixWord ++ tailWord_4128538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128538).length < 2 ^ (prefixWord ++ tailWord_4128538).sum := by decide
  have hdescent : baseEnd_4128538 < baseStart_4128538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128583 : List Nat := [1, 1, 4, 1, 2, 1, 3, 5, 1, 3]
def baseStart_4128583 : Nat := 118140960795 + 4128583 * 2 ^ 59
def prefixEnd_4128583 : Nat := 4983230072969 + 3 ^ 40 * 4128583 * 2
def baseEnd_4128583 : Nat := 1413298333987683755816999

theorem tailTrace_4128583 : CollatzResearch.WordTrace tailWord_4128583 prefixEnd_4128583 1413298333987683755816999 := by
  unfold tailWord_4128583
  simp only [CollatzResearch.WordTrace]
  refine ⟨150581792801856371685166403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100387861867904247790110935 150581792801856371685166403)
  ·
    refine ⟨225872689202784557527749605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150581792801856371685166403 225872689202784557527749605)
    ·
      refine ⟨42351129225522104536453051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225872689202784557527749605 42351129225522104536453051)
      ·
        refine ⟨63526693838283156804679577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42351129225522104536453051 63526693838283156804679577)
        ·
          refine ⟨47645020378712367603509683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63526693838283156804679577 47645020378712367603509683)
          ·
            refine ⟨71467530568068551405264525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47645020378712367603509683 71467530568068551405264525)
            ·
              refine ⟨26800323963025706776974197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71467530568068551405264525 26800323963025706776974197)
              ·
                refine ⟨2512530371533660010341331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26800323963025706776974197 2512530371533660010341331)
                ·
                  refine ⟨3768795557300490015511997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2512530371533660010341331 3768795557300490015511997)
                  ·
                    refine ⟨1413298333987683755816999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3768795557300490015511997 1413298333987683755816999)
                    ·
                      rfl

theorem cell22_4128583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_4128583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128583 prefixEnd_4128583 := by exact prefixLift 4128583
  have htrace : WordTrace (prefixWord ++ tailWord_4128583) baseStart_4128583 baseEnd_4128583 := by
    simpa [prefixWord, tailWord_4128583, baseEnd_4128583] using wordTrace_append hprefix tailTrace_4128583
  have hstable : (prefixWord ++ tailWord_4128583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128583).length < 2 ^ (prefixWord ++ tailWord_4128583).sum := by decide
  have hdescent : baseEnd_4128583 < baseStart_4128583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128596 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 7]
def baseStart_4128596 : Nat := 118140960795 + 4128596 * 2 ^ 59
def prefixEnd_4128596 : Nat := 4983230072969 + 3 ^ 40 * 4128596 * 2
def baseEnd_4128596 : Nat := 471100928051118685080653

theorem tailTrace_4128596 : CollatzResearch.WordTrace tailWord_4128596 prefixEnd_4128596 471100928051118685080653 := by
  unfold tailWord_4128596
  simp only [CollatzResearch.WordTrace]
  refine ⟨75291133475404637452694821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100388177967206183270259761 75291133475404637452694821)
  ·
    refine ⟨14117087526638369522380279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75291133475404637452694821 14117087526638369522380279)
    ·
      refine ⟨21175631289957554283570419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14117087526638369522380279 21175631289957554283570419)
      ·
        refine ⟨31763446934936331425355629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21175631289957554283570419 31763446934936331425355629)
        ·
          refine ⟨11911292600601124284508361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31763446934936331425355629 11911292600601124284508361)
          ·
            refine ⟨8933469450450843213381271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11911292600601124284508361 8933469450450843213381271)
            ·
              refine ⟨13400204175676264820071907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8933469450450843213381271 13400204175676264820071907)
              ·
                refine ⟨20100306263514397230107861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13400204175676264820071907 20100306263514397230107861)
                ·
                  refine ⟨471100928051118685080653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20100306263514397230107861 471100928051118685080653)
                  ·
                    rfl

theorem cell22_4128596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_4128596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128596 prefixEnd_4128596 := by exact prefixLift 4128596
  have htrace : WordTrace (prefixWord ++ tailWord_4128596) baseStart_4128596 baseEnd_4128596 := by
    simpa [prefixWord, tailWord_4128596, baseEnd_4128596] using wordTrace_append hprefix tailTrace_4128596
  have hstable : (prefixWord ++ tailWord_4128596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128596).length < 2 ^ (prefixWord ++ tailWord_4128596).sum := by decide
  have hdescent : baseEnd_4128596 < baseStart_4128596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128639 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 3, 5]
def baseStart_4128639 : Nat := 118140960795 + 4128639 * 2 ^ 59
def prefixEnd_4128639 : Nat := 4983230072969 + 3 ^ 40 * 4128639 * 2
def baseEnd_4128639 : Nat := 1413317503932118276416827

theorem tailTrace_4128639 : CollatzResearch.WordTrace tailWord_4128639 prefixEnd_4128639 1413317503932118276416827 := by
  unfold tailWord_4128639
  simp only [CollatzResearch.WordTrace]
  refine ⟨150583835289653493249204971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100389223526435662166136647 150583835289653493249204971)
  ·
    refine ⟨225875752934480239873807457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150583835289653493249204971 225875752934480239873807457)
    ·
      refine ⟨169406814700860179905355593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225875752934480239873807457 169406814700860179905355593)
      ·
        refine ⟨127055111025645134929016695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169406814700860179905355593 127055111025645134929016695)
        ·
          refine ⟨190582666538467702393525043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127055111025645134929016695 190582666538467702393525043)
          ·
            refine ⟨285873999807701553590287565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190582666538467702393525043 285873999807701553590287565)
            ·
              refine ⟨107202749927888082596357837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285873999807701553590287565 107202749927888082596357837)
              ·
                refine ⟨40201031222958030973634189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107202749927888082596357837 40201031222958030973634189)
                ·
                  refine ⟨15075386708609261615112821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40201031222958030973634189 15075386708609261615112821)
                  ·
                    refine ⟨1413317503932118276416827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15075386708609261615112821 1413317503932118276416827)
                    ·
                      rfl

theorem cell22_4128639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_4128639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128639 prefixEnd_4128639 := by exact prefixLift 4128639
  have htrace : WordTrace (prefixWord ++ tailWord_4128639) baseStart_4128639 baseEnd_4128639 := by
    simpa [prefixWord, tailWord_4128639, baseEnd_4128639] using wordTrace_append hprefix tailTrace_4128639
  have hstable : (prefixWord ++ tailWord_4128639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128639).length < 2 ^ (prefixWord ++ tailWord_4128639).sum := by decide
  have hdescent : baseEnd_4128639 < baseStart_4128639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128658 : List Nat := [3, 2, 3, 2, 1, 1, 3, 1, 6]
def baseStart_4128658 : Nat := 118140960795 + 4128658 * 2 ^ 59
def prefixEnd_4128658 : Nat := 4983230072969 + 3 ^ 40 * 4128658 * 2
def baseEnd_4128658 : Nat := 471108002673469520063923

theorem tailTrace_4128658 : CollatzResearch.WordTrace tailWord_4128658 prefixEnd_4128658 471108002673469520063923 := by
  unfold tailWord_4128658
  simp only [CollatzResearch.WordTrace]
  refine ⟨37646132069146164873536657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100389685517723106329431085 37646132069146164873536657)
  ·
    refine ⟨28234599051859623655152493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37646132069146164873536657 28234599051859623655152493)
    ·
      refine ⟨10587974644447358870682185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28234599051859623655152493 10587974644447358870682185)
      ·
        refine ⟨7940980983335519153011639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10587974644447358870682185 7940980983335519153011639)
        ·
          refine ⟨11911471475003278729517459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7940980983335519153011639 11911471475003278729517459)
          ·
            refine ⟨17867207212504918094276189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11911471475003278729517459 17867207212504918094276189)
            ·
              refine ⟨6700202704689344285353571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17867207212504918094276189 6700202704689344285353571)
              ·
                refine ⟨10050304057034016428030357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6700202704689344285353571 10050304057034016428030357)
                ·
                  refine ⟨471108002673469520063923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10050304057034016428030357 471108002673469520063923)
                  ·
                    rfl

theorem cell22_4128658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_4128658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128658 prefixEnd_4128658 := by exact prefixLift 4128658
  have htrace : WordTrace (prefixWord ++ tailWord_4128658) baseStart_4128658 baseEnd_4128658 := by
    simpa [prefixWord, tailWord_4128658, baseEnd_4128658] using wordTrace_append hprefix tailTrace_4128658
  have hstable : (prefixWord ++ tailWord_4128658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128658).length < 2 ^ (prefixWord ++ tailWord_4128658).sum := by decide
  have hdescent : baseEnd_4128658 < baseStart_4128658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128699 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 1, 8]
def baseStart_4128699 : Nat := 118140960795 + 4128699 * 2 ^ 59
def prefixEnd_4128699 : Nat := 4983230072969 + 3 ^ 40 * 4128699 * 2
def baseEnd_4128699 : Nat := 1413338043158298119916643

theorem tailTrace_4128699 : CollatzResearch.WordTrace tailWord_4128699 prefixEnd_4128699 1413338043158298119916643 := by
  unfold tailWord_4128699
  simp only [CollatzResearch.WordTrace]
  refine ⟨150586023669436123496389151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100390682446290748997592767 150586023669436123496389151)
  ·
    refine ⟨225879035504154185244583727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150586023669436123496389151 225879035504154185244583727)
    ·
      refine ⟨338818553256231277866875591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225879035504154185244583727 338818553256231277866875591)
      ·
        refine ⟨508227829884346916800313387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338818553256231277866875591 508227829884346916800313387)
        ·
          refine ⟨762341744826520375200470081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508227829884346916800313387 762341744826520375200470081)
          ·
            refine ⟨571756308619890281400352561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 762341744826520375200470081 571756308619890281400352561)
            ·
              refine ⟨428817231464917711050264421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571756308619890281400352561 428817231464917711050264421)
              ·
                refine ⟨80403230899672070821924579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 428817231464917711050264421 80403230899672070821924579)
                ·
                  refine ⟨120604846349508106232886869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80403230899672070821924579 120604846349508106232886869)
                  ·
                    refine ⟨1413338043158298119916643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120604846349508106232886869 1413338043158298119916643)
                    ·
                      rfl

theorem cell22_4128699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 8].length) (baseStart_4128699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128699 prefixEnd_4128699 := by exact prefixLift 4128699
  have htrace : WordTrace (prefixWord ++ tailWord_4128699) baseStart_4128699 baseEnd_4128699 := by
    simpa [prefixWord, tailWord_4128699, baseEnd_4128699] using wordTrace_append hprefix tailTrace_4128699
  have hstable : (prefixWord ++ tailWord_4128699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128699).length < 2 ^ (prefixWord ++ tailWord_4128699).sum := by decide
  have hdescent : baseEnd_4128699 < baseStart_4128699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128716 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 2, 6]
def baseStart_4128716 : Nat := 118140960795 + 4128716 * 2 ^ 59
def prefixEnd_4128716 : Nat := 4983230072969 + 3 ^ 40 * 4128716 * 2
def baseEnd_4128716 : Nat := 1413343862605715742241591

theorem tailTrace_4128716 : CollatzResearch.WordTrace tailWord_4128716 prefixEnd_4128716 1413343862605715742241591 := by
  unfold tailWord_4128716
  simp only [CollatzResearch.WordTrace]
  refine ⟨75293321855187267699879001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100391095806916356933172001 75293321855187267699879001)
  ·
    refine ⟨56469991391390450774909251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75293321855187267699879001 56469991391390450774909251)
    ·
      refine ⟨84704987087085676162363877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56469991391390450774909251 84704987087085676162363877)
      ·
        refine ⟨15882185078828564280443227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84704987087085676162363877 15882185078828564280443227)
        ·
          refine ⟨23823277618242846420664841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15882185078828564280443227 23823277618242846420664841)
          ·
            refine ⟨17867458213682134815498631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23823277618242846420664841 17867458213682134815498631)
            ·
              refine ⟨26801187320523202223247947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17867458213682134815498631 26801187320523202223247947)
              ·
                refine ⟨40201780980784803334871921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26801187320523202223247947 40201780980784803334871921)
                ·
                  refine ⟨30151335735588602501153941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40201780980784803334871921 30151335735588602501153941)
                  ·
                    refine ⟨1413343862605715742241591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30151335735588602501153941 1413343862605715742241591)
                    ·
                      rfl

theorem cell22_4128716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_4128716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128716 prefixEnd_4128716 := by exact prefixLift 4128716
  have htrace : WordTrace (prefixWord ++ tailWord_4128716) baseStart_4128716 baseEnd_4128716 := by
    simpa [prefixWord, tailWord_4128716, baseEnd_4128716] using wordTrace_append hprefix tailTrace_4128716
  have hstable : (prefixWord ++ tailWord_4128716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128716).length < 2 ^ (prefixWord ++ tailWord_4128716).sum := by decide
  have hdescent : baseEnd_4128716 < baseStart_4128716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128718 : List Nat := [4, 1, 1, 1, 2, 2, 2, 3, 3, 3]
def baseStart_4128718 : Nat := 118140960795 + 4128718 * 2 ^ 59
def prefixEnd_4128718 : Nat := 4983230072969 + 3 ^ 40 * 4128718 * 2
def baseEnd_4128718 : Nat := 1413344547246588403691585

theorem tailTrace_4128718 : CollatzResearch.WordTrace tailWord_4128718 prefixEnd_4128718 1413344547246588403691585 := by
  unfold tailWord_4128718
  simp only [CollatzResearch.WordTrace]
  refine ⟨18823339582045911217666351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100391144437578193160887205 18823339582045911217666351)
  ·
    refine ⟨28235009373068866826499527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18823339582045911217666351 28235009373068866826499527)
    ·
      refine ⟨42352514059603300239749291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28235009373068866826499527 42352514059603300239749291)
      ·
        refine ⟨63528771089404950359623937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42352514059603300239749291 63528771089404950359623937)
        ·
          refine ⟨47646578317053712769717953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63528771089404950359623937 47646578317053712769717953)
          ·
            refine ⟨35734933737790284577288465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47646578317053712769717953 35734933737790284577288465)
            ·
              refine ⟨26801200303342713432966349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35734933737790284577288465 26801200303342713432966349)
              ·
                refine ⟨10050450113753517537362381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26801200303342713432966349 10050450113753517537362381)
                ·
                  refine ⟨3768918792657569076510893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10050450113753517537362381 3768918792657569076510893)
                  ·
                    refine ⟨1413344547246588403691585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3768918792657569076510893 1413344547246588403691585)
                    ·
                      rfl

theorem cell22_4128718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_4128718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128718 prefixEnd_4128718 := by exact prefixLift 4128718
  have htrace : WordTrace (prefixWord ++ tailWord_4128718) baseStart_4128718 baseEnd_4128718 := by
    simpa [prefixWord, tailWord_4128718, baseEnd_4128718] using wordTrace_append hprefix tailTrace_4128718
  have hstable : (prefixWord ++ tailWord_4128718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128718).length < 2 ^ (prefixWord ++ tailWord_4128718).sum := by decide
  have hdescent : baseEnd_4128718 < baseStart_4128718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128746 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 1, 7]
def baseStart_4128746 : Nat := 118140960795 + 4128746 * 2 ^ 59
def prefixEnd_4128746 : Nat := 4983230072969 + 3 ^ 40 * 4128746 * 2
def baseEnd_4128746 : Nat := 1413354132218805663991499

theorem tailTrace_4128746 : CollatzResearch.WordTrace tailWord_4128746 prefixEnd_4128746 1413354132218805663991499 := by
  unfold tailWord_4128746
  simp only [CollatzResearch.WordTrace]
  refine ⟨37646934475066462630837523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100391825266843900348900061 37646934475066462630837523)
  ·
    refine ⟨56470401712599693946256285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37646934475066462630837523 56470401712599693946256285)
    ·
      refine ⟨21176400642224885229846107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56470401712599693946256285 21176400642224885229846107)
      ·
        refine ⟨31764600963337327844769161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21176400642224885229846107 31764600963337327844769161)
        ·
          refine ⟨23823450722502995883576871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31764600963337327844769161 23823450722502995883576871)
          ·
            refine ⟨35735176083754493825365307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23823450722502995883576871 35735176083754493825365307)
            ·
              refine ⟨53602764125631740738047961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35735176083754493825365307 53602764125631740738047961)
              ·
                refine ⟨40202073094223805553535971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53602764125631740738047961 40202073094223805553535971)
                ·
                  refine ⟨60303109641335708330303957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40202073094223805553535971 60303109641335708330303957)
                  ·
                    refine ⟨1413354132218805663991499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60303109641335708330303957 1413354132218805663991499)
                    ·
                      rfl

theorem cell22_4128746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_4128746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128746 prefixEnd_4128746 := by exact prefixLift 4128746
  have htrace : WordTrace (prefixWord ++ tailWord_4128746) baseStart_4128746 baseEnd_4128746 := by
    simpa [prefixWord, tailWord_4128746, baseEnd_4128746] using wordTrace_append hprefix tailTrace_4128746
  have hstable : (prefixWord ++ tailWord_4128746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128746).length < 2 ^ (prefixWord ++ tailWord_4128746).sum := by decide
  have hdescent : baseEnd_4128746 < baseStart_4128746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128821 : List Nat := [1, 3, 3, 1, 1, 1, 12]
def baseStart_4128821 : Nat := 118140960795 + 4128821 * 2 ^ 59
def prefixEnd_4128821 : Nat := 4983230072969 + 3 ^ 40 * 4128821 * 2
def baseEnd_4128821 : Nat := 52347400231538165495047

theorem tailTrace_4128821 : CollatzResearch.WordTrace tailWord_4128821 prefixEnd_4128821 52347400231538165495047 := by
  unfold tailWord_4128821
  simp only [CollatzResearch.WordTrace]
  refine ⟨150590473374994138332330317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100393648916662758888220211 150590473374994138332330317)
  ·
    refine ⟨56471427515622801874623869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150590473374994138332330317 56471427515622801874623869)
    ·
      refine ⟨21176785318358550702983951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56471427515622801874623869 21176785318358550702983951)
      ·
        refine ⟨31765177977537826054475927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21176785318358550702983951 31765177977537826054475927)
        ·
          refine ⟨47647766966306739081713891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31765177977537826054475927 47647766966306739081713891)
          ·
            refine ⟨71471650449460108622570837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47647766966306739081713891 71471650449460108622570837)
            ·
              refine ⟨52347400231538165495047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 71471650449460108622570837 52347400231538165495047)
              ·
                rfl

theorem cell22_4128821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 12].length) (baseStart_4128821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128821 prefixEnd_4128821 := by exact prefixLift 4128821
  have htrace : WordTrace (prefixWord ++ tailWord_4128821) baseStart_4128821 baseEnd_4128821 := by
    simpa [prefixWord, tailWord_4128821, baseEnd_4128821] using wordTrace_append hprefix tailTrace_4128821
  have hstable : (prefixWord ++ tailWord_4128821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128821).length < 2 ^ (prefixWord ++ tailWord_4128821).sum := by decide
  have hdescent : baseEnd_4128821 < baseStart_4128821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128887 : List Nat := [1, 1, 3, 1, 1, 6, 1, 4, 1, 3]
def baseStart_4128887 : Nat := 118140960795 + 4128887 * 2 ^ 59
def prefixEnd_4128887 : Nat := 4983230072969 + 3 ^ 40 * 4128887 * 2
def baseEnd_4128887 : Nat := 1413402399400328296216067

theorem tailTrace_4128887 : CollatzResearch.WordTrace tailWord_4128887 prefixEnd_4128887 1413402399400328296216067 := by
  unfold tailWord_4128887
  simp only [CollatzResearch.WordTrace]
  refine ⟨150592880592755031604232915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100395253728503354402821943 150592880592755031604232915)
  ·
    refine ⟨225889320889132547406349373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150592880592755031604232915 225889320889132547406349373)
    ·
      refine ⟨84708495333424705277381015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225889320889132547406349373 84708495333424705277381015)
      ·
        refine ⟨127062743000137057916071523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84708495333424705277381015 127062743000137057916071523)
        ·
          refine ⟨190594114500205586874107285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127062743000137057916071523 190594114500205586874107285)
          ·
            refine ⟨8934099117197136884723779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 190594114500205586874107285 8934099117197136884723779)
            ·
              refine ⟨13401148675795705327085669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8934099117197136884723779 13401148675795705327085669)
              ·
                refine ⟨2512715376711694748828563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13401148675795705327085669 2512715376711694748828563)
                ·
                  refine ⟨3769073065067542123242845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2512715376711694748828563 3769073065067542123242845)
                  ·
                    refine ⟨1413402399400328296216067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3769073065067542123242845 1413402399400328296216067)
                    ·
                      rfl

theorem cell22_4128887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 1, 3].length) (baseStart_4128887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128887 prefixEnd_4128887 := by exact prefixLift 4128887
  have htrace : WordTrace (prefixWord ++ tailWord_4128887) baseStart_4128887 baseEnd_4128887 := by
    simpa [prefixWord, tailWord_4128887, baseEnd_4128887] using wordTrace_append hprefix tailTrace_4128887
  have hstable : (prefixWord ++ tailWord_4128887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128887).length < 2 ^ (prefixWord ++ tailWord_4128887).sum := by decide
  have hdescent : baseEnd_4128887 < baseStart_4128887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4128960 : List Nat := [2, 1, 1, 2, 5, 1, 3, 1, 1, 5]
def baseStart_4128960 : Nat := 118140960795 + 4128960 * 2 ^ 59
def prefixEnd_4128960 : Nat := 4983230072969 + 3 ^ 40 * 4128960 * 2
def baseEnd_4128960 : Nat := 1413427388792180439140843

theorem tailTrace_4128960 : CollatzResearch.WordTrace tailWord_4128960 prefixEnd_4128960 1413427388792180439140843 := by
  unfold tailWord_4128960
  simp only [CollatzResearch.WordTrace]
  refine ⟨75297771560745282535820167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100397028747660376714426889 75297771560745282535820167)
  ·
    refine ⟨112946657341117923803730251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75297771560745282535820167 112946657341117923803730251)
    ·
      refine ⟨169419986011676885705595377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112946657341117923803730251 169419986011676885705595377)
      ·
        refine ⟨127064989508757664279196533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169419986011676885705595377 127064989508757664279196533)
        ·
          refine ⟨11912342766446031026174675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127064989508757664279196533 11912342766446031026174675)
          ·
            refine ⟨17868514149669046539262013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11912342766446031026174675 17868514149669046539262013)
            ·
              refine ⟨6700692806125892452223255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17868514149669046539262013 6700692806125892452223255)
              ·
                refine ⟨10051039209188838678334883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6700692806125892452223255 10051039209188838678334883)
                ·
                  refine ⟨15076558813783258017502325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10051039209188838678334883 15076558813783258017502325)
                  ·
                    refine ⟨1413427388792180439140843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15076558813783258017502325 1413427388792180439140843)
                    ·
                      rfl

theorem cell22_4128960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 1, 5].length) (baseStart_4128960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4128960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4128960 prefixEnd_4128960 := by exact prefixLift 4128960
  have htrace : WordTrace (prefixWord ++ tailWord_4128960) baseStart_4128960 baseEnd_4128960 := by
    simpa [prefixWord, tailWord_4128960, baseEnd_4128960] using wordTrace_append hprefix tailTrace_4128960
  have hstable : (prefixWord ++ tailWord_4128960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4128960).length < 2 ^ (prefixWord ++ tailWord_4128960).sum := by decide
  have hdescent : baseEnd_4128960 < baseStart_4128960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4128960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129003 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 2, 6]
def baseStart_4129003 : Nat := 118140960795 + 4129003 * 2 ^ 59
def prefixEnd_4129003 : Nat := 4983230072969 + 3 ^ 40 * 4129003 * 2
def baseEnd_4129003 : Nat := 1413442108570942660315711

theorem tailTrace_4129003 : CollatzResearch.WordTrace tailWord_4129003 prefixEnd_4129003 1413442108570942660315711 := by
  unfold tailWord_4129003
  simp only [CollatzResearch.WordTrace]
  refine ⟨150597111460334783415455663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100398074306889855610303775 150597111460334783415455663)
  ·
    refine ⟨225895667190502175123183495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150597111460334783415455663 225895667190502175123183495)
    ·
      refine ⟨338843500785753262684775243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225895667190502175123183495 338843500785753262684775243)
      ·
        refine ⟨508265251178629894027162865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338843500785753262684775243 508265251178629894027162865)
        ·
          refine ⟨381198938383972420520372149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508265251178629894027162865 381198938383972420520372149)
          ·
            refine ⟨35737400473497414423784889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 381198938383972420520372149 35737400473497414423784889)
            ·
              refine ⟨26803050355123060817838667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35737400473497414423784889 26803050355123060817838667)
              ·
                refine ⟨40204575532684591226758001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26803050355123060817838667 40204575532684591226758001)
                ·
                  refine ⟨30153431649513443420068501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40204575532684591226758001 30153431649513443420068501)
                  ·
                    refine ⟨1413442108570942660315711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30153431649513443420068501 1413442108570942660315711)
                    ·
                      rfl

theorem cell22_4129003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 6].length) (baseStart_4129003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129003 prefixEnd_4129003 := by exact prefixLift 4129003
  have htrace : WordTrace (prefixWord ++ tailWord_4129003) baseStart_4129003 baseEnd_4129003 := by
    simpa [prefixWord, tailWord_4129003, baseEnd_4129003] using wordTrace_append hprefix tailTrace_4129003
  have hstable : (prefixWord ++ tailWord_4129003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129003).length < 2 ^ (prefixWord ++ tailWord_4129003).sum := by decide
  have hdescent : baseEnd_4129003 < baseStart_4129003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129022 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_4129022 : Nat := 118140960795 + 4129022 * 2 ^ 59
def prefixEnd_4129022 : Nat := 4983230072969 + 3 ^ 40 * 4129022 * 2
def baseEnd_4129022 : Nat := 1413448612659232944090653

theorem tailTrace_4129022 : CollatzResearch.WordTrace tailWord_4129022 prefixEnd_4129022 1413448612659232944090653 := by
  unfold tailWord_4129022
  simp only [CollatzResearch.WordTrace]
  refine ⟨18824725555908243707549665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100398536298177299773598213 18824725555908243707549665)
  ·
    refine ⟨14118544166931182780662249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18824725555908243707549665 14118544166931182780662249)
    ·
      refine ⟨10588908125198387085496687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14118544166931182780662249 10588908125198387085496687)
      ·
        refine ⟨15883362187797580628245031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10588908125198387085496687 15883362187797580628245031)
        ·
          refine ⟨23825043281696370942367547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15883362187797580628245031 23825043281696370942367547)
          ·
            refine ⟨35737564922544556413551321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23825043281696370942367547 35737564922544556413551321)
            ·
              refine ⟨26803173691908417310163491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35737564922544556413551321 26803173691908417310163491)
              ·
                refine ⟨40204760537862625965245237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26803173691908417310163491 40204760537862625965245237)
                ·
                  refine ⟨3769196300424621184241741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40204760537862625965245237 3769196300424621184241741)
                  ·
                    refine ⟨1413448612659232944090653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3769196300424621184241741 1413448612659232944090653)
                    ·
                      rfl

theorem cell22_4129022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_4129022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129022 prefixEnd_4129022 := by exact prefixLift 4129022
  have htrace : WordTrace (prefixWord ++ tailWord_4129022) baseStart_4129022 baseEnd_4129022 := by
    simpa [prefixWord, tailWord_4129022, baseEnd_4129022] using wordTrace_append hprefix tailTrace_4129022
  have hstable : (prefixWord ++ tailWord_4129022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129022).length < 2 ^ (prefixWord ++ tailWord_4129022).sum := by decide
  have hdescent : baseEnd_4129022 < baseStart_4129022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129056 : List Nat := [2, 1, 1, 5, 2, 1, 4, 2, 1, 3]
def baseStart_4129056 : Nat := 118140960795 + 4129056 * 2 ^ 59
def prefixEnd_4129056 : Nat := 4983230072969 + 3 ^ 40 * 4129056 * 2
def baseEnd_4129056 : Nat := 1413460251554068188740549

theorem tailTrace_4129056 : CollatzResearch.WordTrace tailWord_4129056 prefixEnd_4129056 1413460251554068188740549 := by
  unfold tailWord_4129056
  simp only [CollatzResearch.WordTrace]
  refine ⟨75299522264571386733567511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100399363019428515644756681 75299522264571386733567511)
  ·
    refine ⟨112949283396857080100351267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75299522264571386733567511 112949283396857080100351267)
    ·
      refine ⟨169423925095285620150526901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112949283396857080100351267 169423925095285620150526901)
      ·
        refine ⟨15883492977683026889111897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169423925095285620150526901 15883492977683026889111897)
        ·
          refine ⟨11912619733262270166833923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15883492977683026889111897 11912619733262270166833923)
          ·
            refine ⟨17868929599893405250250885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11912619733262270166833923 17868929599893405250250885)
            ·
              refine ⟨3350424299980013484422041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17868929599893405250250885 3350424299980013484422041)
              ·
                refine ⟨2512818224985010113316531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3350424299980013484422041 2512818224985010113316531)
                ·
                  refine ⟨3769227337477515169974797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2512818224985010113316531 3769227337477515169974797)
                  ·
                    refine ⟨1413460251554068188740549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3769227337477515169974797 1413460251554068188740549)
                    ·
                      rfl

theorem cell22_4129056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 1, 3].length) (baseStart_4129056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129056 prefixEnd_4129056 := by exact prefixLift 4129056
  have htrace : WordTrace (prefixWord ++ tailWord_4129056) baseStart_4129056 baseEnd_4129056 := by
    simpa [prefixWord, tailWord_4129056, baseEnd_4129056] using wordTrace_append hprefix tailTrace_4129056
  have hstable : (prefixWord ++ tailWord_4129056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129056).length < 2 ^ (prefixWord ++ tailWord_4129056).sum := by decide
  have hdescent : baseEnd_4129056 < baseStart_4129056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129095 : List Nat := [1, 1, 4, 1, 2, 2, 1, 4, 1, 5]
def baseStart_4129095 : Nat := 118140960795 + 4129095 * 2 ^ 59
def prefixEnd_4129095 : Nat := 4983230072969 + 3 ^ 40 * 4129095 * 2
def baseEnd_4129095 : Nat := 1413473602051085087015429

theorem tailTrace_4129095 : CollatzResearch.WordTrace tailWord_4129095 prefixEnd_4129095 1413473602051085087015429 := by
  unfold tailWord_4129095
  simp only [CollatzResearch.WordTrace]
  refine ⟨150600466976001483127804739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100400311317334322085203159 150600466976001483127804739)
  ·
    refine ⟨225900700464002224691707109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150600466976001483127804739 225900700464002224691707109)
    ·
      refine ⟨42356381337000417129695083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225900700464002224691707109 42356381337000417129695083)
      ·
        refine ⟨63534572005500625694542625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42356381337000417129695083 63534572005500625694542625)
        ·
          refine ⟨47650929004125469270906969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63534572005500625694542625 47650929004125469270906969)
          ·
            refine ⟨35738196753094101953180227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47650929004125469270906969 35738196753094101953180227)
            ·
              refine ⟨53607295129641152929770341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35738196753094101953180227 53607295129641152929770341)
              ·
                refine ⟨10051367836807716174331939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53607295129641152929770341 10051367836807716174331939)
                ·
                  refine ⟨15077051755211574261497909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10051367836807716174331939 15077051755211574261497909)
                  ·
                    refine ⟨1413473602051085087015429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15077051755211574261497909 1413473602051085087015429)
                    ·
                      rfl

theorem cell22_4129095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_4129095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129095 prefixEnd_4129095 := by exact prefixLift 4129095
  have htrace : WordTrace (prefixWord ++ tailWord_4129095) baseStart_4129095 baseEnd_4129095 := by
    simpa [prefixWord, tailWord_4129095, baseEnd_4129095] using wordTrace_append hprefix tailTrace_4129095
  have hstable : (prefixWord ++ tailWord_4129095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129095).length < 2 ^ (prefixWord ++ tailWord_4129095).sum := by decide
  have hdescent : baseEnd_4129095 < baseStart_4129095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129112 : List Nat := [2, 1, 2, 2, 1, 1, 2, 6, 2, 3]
def baseStart_4129112 : Nat := 118140960795 + 4129112 * 2 ^ 59
def prefixEnd_4129112 : Nat := 4983230072969 + 3 ^ 40 * 4129112 * 2
def baseEnd_4129112 : Nat := 1413479421498502709340377

theorem tailTrace_4129112 : CollatzResearch.WordTrace tailWord_4129112 prefixEnd_4129112 1413479421498502709340377 := by
  unfold tailWord_4129112
  simp only [CollatzResearch.WordTrace]
  refine ⟨75300543508469947515586795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100400724677959930020782393 75300543508469947515586795)
  ·
    refine ⟨112950815262704921273380193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75300543508469947515586795 112950815262704921273380193)
    ·
      refine ⟨84713111447028690955035145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112950815262704921273380193 84713111447028690955035145)
      ·
        refine ⟨63534833585271518216276359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84713111447028690955035145 63534833585271518216276359)
        ·
          refine ⟨95302250377907277324414539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63534833585271518216276359 95302250377907277324414539)
          ·
            refine ⟨142953375566860915986621809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95302250377907277324414539 142953375566860915986621809)
            ·
              refine ⟨107215031675145686989966357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142953375566860915986621809 107215031675145686989966357)
              ·
                refine ⟨5025704609772454077654673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107215031675145686989966357 5025704609772454077654673)
                ·
                  refine ⟨3769278457329340558241005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5025704609772454077654673 3769278457329340558241005)
                  ·
                    refine ⟨1413479421498502709340377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3769278457329340558241005 1413479421498502709340377)
                    ·
                      rfl

theorem cell22_4129112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_4129112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129112 prefixEnd_4129112 := by exact prefixLift 4129112
  have htrace : WordTrace (prefixWord ++ tailWord_4129112) baseStart_4129112 baseEnd_4129112 := by
    simpa [prefixWord, tailWord_4129112, baseEnd_4129112] using wordTrace_append hprefix tailTrace_4129112
  have hstable : (prefixWord ++ tailWord_4129112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129112).length < 2 ^ (prefixWord ++ tailWord_4129112).sum := by decide
  have hdescent : baseEnd_4129112 < baseStart_4129112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129129 : List Nat := [1, 2, 1, 1, 1, 3, 7, 1, 2, 3]
def baseStart_4129129 : Nat := 118140960795 + 4129129 * 2 ^ 59
def prefixEnd_4129129 : Nat := 4983230072969 + 3 ^ 40 * 4129129 * 2
def baseEnd_4129129 : Nat := 1413485240945920331665325

theorem tailTrace_4129129 : CollatzResearch.WordTrace tailWord_4129129 prefixEnd_4129129 1413485240945920331665325 := by
  unfold tailWord_4129129
  simp only [CollatzResearch.WordTrace]
  refine ⟨150601707057878306934542441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100401138038585537956361627 150601707057878306934542441)
  ·
    refine ⟨112951280293408730200906831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150601707057878306934542441 112951280293408730200906831)
    ·
      refine ⟨169426920440113095301360247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112951280293408730200906831 169426920440113095301360247)
      ·
        refine ⟨254140380660169642952040371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169426920440113095301360247 254140380660169642952040371)
        ·
          refine ⟨381210570990254464428060557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254140380660169642952040371 381210570990254464428060557)
          ·
            refine ⟨142953964121345424160522709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 381210570990254464428060557 142953964121345424160522709)
            ·
              refine ⟨3350483534094033378762251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 142953964121345424160522709 3350483534094033378762251)
              ·
                refine ⟨5025725301141050068143377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3350483534094033378762251 5025725301141050068143377)
                ·
                  refine ⟨3769293975855787551107533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5025725301141050068143377 3769293975855787551107533)
                  ·
                    refine ⟨1413485240945920331665325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3769293975855787551107533 1413485240945920331665325)
                    ·
                      rfl

theorem cell22_4129129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 2, 3].length) (baseStart_4129129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129129 prefixEnd_4129129 := by exact prefixLift 4129129
  have htrace : WordTrace (prefixWord ++ tailWord_4129129) baseStart_4129129 baseEnd_4129129 := by
    simpa [prefixWord, tailWord_4129129, baseEnd_4129129] using wordTrace_append hprefix tailTrace_4129129
  have hstable : (prefixWord ++ tailWord_4129129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129129).length < 2 ^ (prefixWord ++ tailWord_4129129).sum := by decide
  have hdescent : baseEnd_4129129 < baseStart_4129129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129187 : List Nat := [1, 1, 1, 4, 1, 5, 1, 3, 5]
def baseStart_4129187 : Nat := 118140960795 + 4129187 * 2 ^ 59
def prefixEnd_4129187 : Nat := 4983230072969 + 3 ^ 40 * 4129187 * 2
def baseEnd_4129187 : Nat := 471168365177075837905049

theorem tailTrace_4129187 : CollatzResearch.WordTrace tailWord_4129187 prefixEnd_4129187 471168365177075837905049 := by
  unfold tailWord_4129187
  simp only [CollatzResearch.WordTrace]
  refine ⟨150603822491668182840153815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100402548327778788560102543 150603822491668182840153815)
  ·
    refine ⟨225905733737502274260230723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150603822491668182840153815 225905733737502274260230723)
    ·
      refine ⟨338858600606253411390346085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225905733737502274260230723 338858600606253411390346085)
      ·
        refine ⟨63535987613672514635689891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338858600606253411390346085 63535987613672514635689891)
        ·
          refine ⟨95303981420508771953534837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63535987613672514635689891 95303981420508771953534837)
          ·
            refine ⟨8934748258172697370643891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95303981420508771953534837 8934748258172697370643891)
            ·
              refine ⟨13402122387259046055965837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8934748258172697370643891 13402122387259046055965837)
              ·
                refine ⟨5025795895222142270987189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13402122387259046055965837 5025795895222142270987189)
                ·
                  refine ⟨471168365177075837905049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5025795895222142270987189 471168365177075837905049)
                  ·
                    rfl

theorem cell22_4129187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 5].length) (baseStart_4129187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129187 prefixEnd_4129187 := by exact prefixLift 4129187
  have htrace : WordTrace (prefixWord ++ tailWord_4129187) baseStart_4129187 baseEnd_4129187 := by
    simpa [prefixWord, tailWord_4129187, baseEnd_4129187] using wordTrace_append hprefix tailTrace_4129187
  have hstable : (prefixWord ++ tailWord_4129187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129187).length < 2 ^ (prefixWord ++ tailWord_4129187).sum := by decide
  have hdescent : baseEnd_4129187 < baseStart_4129187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129247 : List Nat := [1, 1, 2, 3, 3, 2, 1, 3, 1, 5]
def baseStart_4129247 : Nat := 118140960795 + 4129247 * 2 ^ 59
def prefixEnd_4129247 : Nat := 4983230072969 + 3 ^ 40 * 4129247 * 2
def baseEnd_4129247 : Nat := 1413525634757407357214963

theorem tailTrace_4129247 : CollatzResearch.WordTrace tailWord_4129247 prefixEnd_4129247 1413525634757407357214963 := by
  unfold tailWord_4129247
  simp only [CollatzResearch.WordTrace]
  refine ⟨150606010871450813087337995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100404007247633875391558663 150606010871450813087337995)
  ·
    refine ⟨225909016307176219631006993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150606010871450813087337995 225909016307176219631006993)
    ·
      refine ⟨169431762230382164723255245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225909016307176219631006993 169431762230382164723255245)
      ·
        refine ⟨63536910836393311771220717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169431762230382164723255245 63536910836393311771220717)
        ·
          refine ⟨23826341563647491914207769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63536910836393311771220717 23826341563647491914207769)
          ·
            refine ⟨17869756172735618935655827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23826341563647491914207769 17869756172735618935655827)
            ·
              refine ⟨26804634259103428403483741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17869756172735618935655827 26804634259103428403483741)
              ·
                refine ⟨10051737847163785651306403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26804634259103428403483741 10051737847163785651306403)
                ·
                  refine ⟨15077606770745678476959605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10051737847163785651306403 15077606770745678476959605)
                  ·
                    refine ⟨1413525634757407357214963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15077606770745678476959605 1413525634757407357214963)
                    ·
                      rfl

theorem cell22_4129247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_4129247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129247 prefixEnd_4129247 := by exact prefixLift 4129247
  have htrace : WordTrace (prefixWord ++ tailWord_4129247) baseStart_4129247 baseEnd_4129247 := by
    simpa [prefixWord, tailWord_4129247, baseEnd_4129247] using wordTrace_append hprefix tailTrace_4129247
  have hstable : (prefixWord ++ tailWord_4129247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129247).length < 2 ^ (prefixWord ++ tailWord_4129247).sum := by decide
  have hdescent : baseEnd_4129247 < baseStart_4129247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129281 : List Nat := [1, 2, 4, 1, 3, 1, 3, 2, 2, 3]
def baseStart_4129281 : Nat := 118140960795 + 4129281 * 2 ^ 59
def prefixEnd_4129281 : Nat := 4983230072969 + 3 ^ 40 * 4129281 * 2
def baseEnd_4129281 : Nat := 1413537273652242601864859

theorem tailTrace_4129281 : CollatzResearch.WordTrace tailWord_4129281 prefixEnd_4129281 1413537273652242601864859 := by
  unfold tailWord_4129281
  simp only [CollatzResearch.WordTrace]
  refine ⟨150607250953327636894075697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100404833968885091262717131 150607250953327636894075697)
  ·
    refine ⟨112955438214995727670556773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150607250953327636894075697 112955438214995727670556773)
    ·
      refine ⟨21179144665311698938229395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112955438214995727670556773 21179144665311698938229395)
      ·
        refine ⟨31768716997967548407344093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21179144665311698938229395 31768716997967548407344093)
        ·
          refine ⟨11913268874237830652754035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31768716997967548407344093 11913268874237830652754035)
          ·
            refine ⟨17869903311356745979131053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11913268874237830652754035 17869903311356745979131053)
            ·
              refine ⟨6701213741758779742174145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17869903311356745979131053 6701213741758779742174145)
              ·
                refine ⟨5025910306319084806630609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6701213741758779742174145 5025910306319084806630609)
                ·
                  refine ⟨3769432729739313604972957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5025910306319084806630609 3769432729739313604972957)
                  ·
                    refine ⟨1413537273652242601864859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3769432729739313604972957 1413537273652242601864859)
                    ·
                      rfl

theorem cell22_4129281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_4129281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129281 prefixEnd_4129281 := by exact prefixLift 4129281
  have htrace : WordTrace (prefixWord ++ tailWord_4129281) baseStart_4129281 baseEnd_4129281 := by
    simpa [prefixWord, tailWord_4129281, baseEnd_4129281] using wordTrace_append hprefix tailTrace_4129281
  have hstable : (prefixWord ++ tailWord_4129281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129281).length < 2 ^ (prefixWord ++ tailWord_4129281).sum := by decide
  have hdescent : baseEnd_4129281 < baseStart_4129281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129343 : List Nat := [1, 1, 2, 2, 3, 2, 5, 2, 1, 3]
def baseStart_4129343 : Nat := 118140960795 + 4129343 * 2 ^ 59
def prefixEnd_4129343 : Nat := 4983230072969 + 3 ^ 40 * 4129343 * 2
def baseEnd_4129343 : Nat := 1413558497519295106814669

theorem tailTrace_4129343 : CollatzResearch.WordTrace tailWord_4129343 prefixEnd_4129343 1413558497519295106814669 := by
  unfold tailWord_4129343
  simp only [CollatzResearch.WordTrace]
  refine ⟨150609512279103021482832683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100406341519402014321888455 150609512279103021482832683)
  ·
    refine ⟨225914268418654532224249025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150609512279103021482832683 225914268418654532224249025)
    ·
      refine ⟨169435701313990899168186769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225914268418654532224249025 169435701313990899168186769)
      ·
        refine ⟨127076775985493174376140077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169435701313990899168186769 127076775985493174376140077)
        ·
          refine ⟨47653790994559940391052529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127076775985493174376140077 47653790994559940391052529)
          ·
            refine ⟨35740343245919955293289397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47653790994559940391052529 35740343245919955293289397)
            ·
              refine ⟨3350657179304995808745881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35740343245919955293289397 3350657179304995808745881)
              ·
                refine ⟨2512992884478746856559411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3350657179304995808745881 2512992884478746856559411)
                ·
                  refine ⟨3769489326718120284839117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2512992884478746856559411 3769489326718120284839117)
                  ·
                    refine ⟨1413558497519295106814669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3769489326718120284839117 1413558497519295106814669)
                    ·
                      rfl

theorem cell22_4129343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 1, 3].length) (baseStart_4129343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129343 prefixEnd_4129343 := by exact prefixLift 4129343
  have htrace : WordTrace (prefixWord ++ tailWord_4129343) baseStart_4129343 baseEnd_4129343 := by
    simpa [prefixWord, tailWord_4129343, baseEnd_4129343] using wordTrace_append hprefix tailTrace_4129343
  have hstable : (prefixWord ++ tailWord_4129343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129343).length < 2 ^ (prefixWord ++ tailWord_4129343).sum := by decide
  have hdescent : baseEnd_4129343 < baseStart_4129343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129367 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 8]
def baseStart_4129367 : Nat := 118140960795 + 4129367 * 2 ^ 59
def prefixEnd_4129367 : Nat := 4983230072969 + 3 ^ 40 * 4129367 * 2
def baseEnd_4129367 : Nat := 471188904403255681404865

theorem tailTrace_4129367 : CollatzResearch.WordTrace tailWord_4129367 prefixEnd_4129367 471188904403255681404865 := by
  unfold tailWord_4129367
  simp only [CollatzResearch.WordTrace]
  refine ⟨150610387631016073581706355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100406925087344049054470903 150610387631016073581706355)
  ·
    refine ⟨225915581446524110372559533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150610387631016073581706355 225915581446524110372559533)
    ·
      refine ⟨84718343042446541389709825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225915581446524110372559533 84718343042446541389709825)
      ·
        refine ⟨63538757281834906042282369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84718343042446541389709825 63538757281834906042282369)
        ·
          refine ⟨47654067961376179531711777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63538757281834906042282369 47654067961376179531711777)
          ·
            refine ⟨35740550971032134648783833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47654067961376179531711777 35740550971032134648783833)
            ·
              refine ⟨26805413228274100986587875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35740550971032134648783833 26805413228274100986587875)
              ·
                refine ⟨40208119842411151479881813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26805413228274100986587875 40208119842411151479881813)
                ·
                  refine ⟨471188904403255681404865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40208119842411151479881813 471188904403255681404865)
                  ·
                    rfl

theorem cell22_4129367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 8].length) (baseStart_4129367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129367 prefixEnd_4129367 := by exact prefixLift 4129367
  have htrace : WordTrace (prefixWord ++ tailWord_4129367) baseStart_4129367 baseEnd_4129367 := by
    simpa [prefixWord, tailWord_4129367, baseEnd_4129367] using wordTrace_append hprefix tailTrace_4129367
  have hstable : (prefixWord ++ tailWord_4129367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129367).length < 2 ^ (prefixWord ++ tailWord_4129367).sum := by decide
  have hdescent : baseEnd_4129367 < baseStart_4129367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129399 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 4, 3]
def baseStart_4129399 : Nat := 118140960795 + 4129399 * 2 ^ 59
def prefixEnd_4129399 : Nat := 4983230072969 + 3 ^ 40 * 4129399 * 2
def baseEnd_4129399 : Nat := 1413577667463729627414497

theorem tailTrace_4129399 : CollatzResearch.WordTrace tailWord_4129399 prefixEnd_4129399 1413577667463729627414497 := by
  unfold tailWord_4129399
  simp only [CollatzResearch.WordTrace]
  refine ⟨150611554766900143046871251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100407703177933428697914167 150611554766900143046871251)
  ·
    refine ⟨225917332150350214570306877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150611554766900143046871251 225917332150350214570306877)
    ·
      refine ⟨84718999556381330463865079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225917332150350214570306877 84718999556381330463865079)
      ·
        refine ⟨127078499334571995695797619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84718999556381330463865079 127078499334571995695797619)
        ·
          refine ⟨190617749001857993543696429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127078499334571995695797619 190617749001857993543696429)
          ·
            refine ⟨71481655875696747578886161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190617749001857993543696429 71481655875696747578886161)
            ·
              refine ⟨53611241906772560684164621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71481655875696747578886161 53611241906772560684164621)
              ·
                refine ⟨20104215715039710256561733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53611241906772560684164621 20104215715039710256561733)
                ·
                  refine ⟨3769540446569945673105325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20104215715039710256561733 3769540446569945673105325)
                  ·
                    refine ⟨1413577667463729627414497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3769540446569945673105325 1413577667463729627414497)
                    ·
                      rfl

theorem cell22_4129399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_4129399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129399 prefixEnd_4129399 := by exact prefixLift 4129399
  have htrace : WordTrace (prefixWord ++ tailWord_4129399) baseStart_4129399 baseEnd_4129399 := by
    simpa [prefixWord, tailWord_4129399, baseEnd_4129399] using wordTrace_append hprefix tailTrace_4129399
  have hstable : (prefixWord ++ tailWord_4129399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129399).length < 2 ^ (prefixWord ++ tailWord_4129399).sum := by decide
  have hdescent : baseEnd_4129399 < baseStart_4129399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129401 : List Nat := [1, 2, 1, 3, 3, 3, 1, 4, 4]
def baseStart_4129401 : Nat := 118140960795 + 4129401 * 2 ^ 59
def prefixEnd_4129401 : Nat := 4983230072969 + 3 ^ 40 * 4129401 * 2
def baseEnd_4129401 : Nat := 471192784034867429621497

theorem tailTrace_4129401 : CollatzResearch.WordTrace tailWord_4129401 prefixEnd_4129401 471192784034867429621497 := by
  unfold tailWord_4129401
  simp only [CollatzResearch.WordTrace]
  refine ⟨150611627712892897388444057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100407751808595264925629371 150611627712892897388444057)
  ·
    refine ⟨112958720784669673041333043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150611627712892897388444057 112958720784669673041333043)
    ·
      refine ⟨169438081177004509561999565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112958720784669673041333043 169438081177004509561999565)
      ·
        refine ⟨63539280441376691085749837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169438081177004509561999565 63539280441376691085749837)
        ·
          refine ⟨23827230165516259157156189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63539280441376691085749837 23827230165516259157156189)
          ·
            refine ⟨8935211312068597183933571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23827230165516259157156189 8935211312068597183933571)
            ·
              refine ⟨13402816968102895775900357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8935211312068597183933571 13402816968102895775900357)
              ·
                refine ⟨2513028181519292957981317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13402816968102895775900357 2513028181519292957981317)
                ·
                  refine ⟨471192784034867429621497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2513028181519292957981317 471192784034867429621497)
                  ·
                    rfl

theorem cell22_4129401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 4].length) (baseStart_4129401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129401 prefixEnd_4129401 := by exact prefixLift 4129401
  have htrace : WordTrace (prefixWord ++ tailWord_4129401) baseStart_4129401 baseEnd_4129401 := by
    simpa [prefixWord, tailWord_4129401, baseEnd_4129401] using wordTrace_append hprefix tailTrace_4129401
  have hstable : (prefixWord ++ tailWord_4129401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129401).length < 2 ^ (prefixWord ++ tailWord_4129401).sum := by decide
  have hdescent : baseEnd_4129401 < baseStart_4129401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129427 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 2, 7]
def baseStart_4129427 : Nat := 118140960795 + 4129427 * 2 ^ 59
def prefixEnd_4129427 : Nat := 4983230072969 + 3 ^ 40 * 4129427 * 2
def baseEnd_4129427 : Nat := 1413587252435946887714411

theorem tailTrace_4129427 : CollatzResearch.WordTrace tailWord_4129427 prefixEnd_4129427 1413587252435946887714411 := by
  unfold tailWord_4129427
  simp only [CollatzResearch.WordTrace]
  refine ⟨150612576010798703828890535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100408384007199135885927023 150612576010798703828890535)
  ·
    refine ⟨225918864016198055743335803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150612576010798703828890535 225918864016198055743335803)
    ·
      refine ⟨338878296024297083615003705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225918864016198055743335803 338878296024297083615003705)
      ·
        refine ⟨254158722018222812711252779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338878296024297083615003705 254158722018222812711252779)
        ·
          refine ⟨381238083027334219066879169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254158722018222812711252779 381238083027334219066879169)
          ·
            refine ⟨285928562270500664300159377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381238083027334219066879169 285928562270500664300159377)
            ·
              refine ⟨214446421702875498225119533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285928562270500664300159377 214446421702875498225119533)
              ·
                refine ⟨80417408138578311834419825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214446421702875498225119533 80417408138578311834419825)
                ·
                  refine ⟨60313056103933733875814869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80417408138578311834419825 60313056103933733875814869)
                  ·
                    refine ⟨1413587252435946887714411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60313056103933733875814869 1413587252435946887714411)
                    ·
                      rfl

theorem cell22_4129427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 7].length) (baseStart_4129427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129427 prefixEnd_4129427 := by exact prefixLift 4129427
  have htrace : WordTrace (prefixWord ++ tailWord_4129427) baseStart_4129427 baseEnd_4129427 := by
    simpa [prefixWord, tailWord_4129427, baseEnd_4129427] using wordTrace_append hprefix tailTrace_4129427
  have hstable : (prefixWord ++ tailWord_4129427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129427).length < 2 ^ (prefixWord ++ tailWord_4129427).sum := by decide
  have hdescent : baseEnd_4129427 < baseStart_4129427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129450 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 4, 3]
def baseStart_4129450 : Nat := 118140960795 + 4129450 * 2 ^ 59
def prefixEnd_4129450 : Nat := 4983230072969 + 3 ^ 40 * 4129450 * 2
def baseEnd_4129450 : Nat := 1413595125805982494389341

theorem tailTrace_4129450 : CollatzResearch.WordTrace tailWord_4129450 prefixEnd_4129450 1413595125805982494389341 := by
  unfold tailWord_4129450
  simp only [CollatzResearch.WordTrace]
  refine ⟨37653353722428844689244451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100408943259810252504651869 37653353722428844689244451)
  ·
    refine ⟨56480030583643267033866677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37653353722428844689244451 56480030583643267033866677)
    ·
      refine ⟨5295002867216556284425001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56480030583643267033866677 5295002867216556284425001)
      ·
        refine ⟨3971252150412417213318751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5295002867216556284425001 3971252150412417213318751)
        ·
          refine ⟨5956878225618625819978127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3971252150412417213318751 5956878225618625819978127)
          ·
            refine ⟨8935317338427938729967191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5956878225618625819978127 8935317338427938729967191)
            ·
              refine ⟨13402976007641908094950787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8935317338427938729967191 13402976007641908094950787)
              ·
                refine ⟨20104464011462862142426181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13402976007641908094950787 20104464011462862142426181)
                ·
                  refine ⟨3769587002149286651704909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20104464011462862142426181 3769587002149286651704909)
                  ·
                    refine ⟨1413595125805982494389341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3769587002149286651704909 1413595125805982494389341)
                    ·
                      rfl

theorem cell22_4129450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_4129450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129450 prefixEnd_4129450 := by exact prefixLift 4129450
  have htrace : WordTrace (prefixWord ++ tailWord_4129450) baseStart_4129450 baseEnd_4129450 := by
    simpa [prefixWord, tailWord_4129450, baseEnd_4129450] using wordTrace_append hprefix tailTrace_4129450
  have hstable : (prefixWord ++ tailWord_4129450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129450).length < 2 ^ (prefixWord ++ tailWord_4129450).sum := by decide
  have hdescent : baseEnd_4129450 < baseStart_4129450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129495 : List Nat := [1, 1, 3, 2, 1, 6, 1, 3, 1, 3]
def baseStart_4129495 : Nat := 118140960795 + 4129495 * 2 ^ 59
def prefixEnd_4129495 : Nat := 4983230072969 + 3 ^ 40 * 4129495 * 2
def baseEnd_4129495 : Nat := 1413610530225617377014203

theorem tailTrace_4129495 : CollatzResearch.WordTrace tailWord_4129495 prefixEnd_4129495 1413610530225617377014203 := by
  unfold tailWord_4129495
  simp only [CollatzResearch.WordTrace]
  refine ⟨150615056174552351442365939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100410037449701567628243959 150615056174552351442365939)
  ·
    refine ⟨225922584261828527163548909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150615056174552351442365939 225922584261828527163548909)
    ·
      refine ⟨84720969098185697686330841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225922584261828527163548909 84720969098185697686330841)
      ·
        refine ⟨63540726823639273264748131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84720969098185697686330841 63540726823639273264748131)
        ·
          refine ⟨95311090235458909897122197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63540726823639273264748131 95311090235458909897122197)
          ·
            refine ⟨4467707354787136401427603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95311090235458909897122197 4467707354787136401427603)
            ·
              refine ⟨6701561032180704602141405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4467707354787136401427603 6701561032180704602141405)
              ·
                refine ⟨2513085387067764225803027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6701561032180704602141405 2513085387067764225803027)
                ·
                  refine ⟨3769628080601646338704541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2513085387067764225803027 3769628080601646338704541)
                  ·
                    refine ⟨1413610530225617377014203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3769628080601646338704541 1413610530225617377014203)
                    ·
                      rfl

theorem cell22_4129495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 1, 3].length) (baseStart_4129495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129495 prefixEnd_4129495 := by exact prefixLift 4129495
  have htrace : WordTrace (prefixWord ++ tailWord_4129495) baseStart_4129495 baseEnd_4129495 := by
    simpa [prefixWord, tailWord_4129495, baseEnd_4129495] using wordTrace_append hprefix tailTrace_4129495
  have hstable : (prefixWord ++ tailWord_4129495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129495).length < 2 ^ (prefixWord ++ tailWord_4129495).sum := by decide
  have hdescent : baseEnd_4129495 < baseStart_4129495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129504 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 5, 4]
def baseStart_4129504 : Nat := 118140960795 + 4129504 * 2 ^ 59
def prefixEnd_4129504 : Nat := 4983230072969 + 3 ^ 40 * 4129504 * 2
def baseEnd_4129504 : Nat := 1413613611109544353539175

theorem tailTrace_4129504 : CollatzResearch.WordTrace tailWord_4129504 prefixEnd_4129504 1413613611109544353539175 := by
  unfold tailWord_4129504
  simp only [CollatzResearch.WordTrace]
  refine ⟨75307692215759872989721783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100410256287679830652962377 75307692215759872989721783)
  ·
    refine ⟨112961538323639809484582675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75307692215759872989721783 112961538323639809484582675)
    ·
      refine ⟨169442307485459714226874013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112961538323639809484582675 169442307485459714226874013)
      ·
        refine ⟨63540865307047392835077755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169442307485459714226874013 63540865307047392835077755)
        ·
          refine ⟨95311297960571089252616633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63540865307047392835077755 95311297960571089252616633)
          ·
            refine ⟨71483473470428316939462475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95311297960571089252616633 71483473470428316939462475)
            ·
              refine ⟨107225210205642475409193713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71483473470428316939462475 107225210205642475409193713)
              ·
                refine ⟨80418907654231856556895285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107225210205642475409193713 80418907654231856556895285)
                ·
                  refine ⟨7539272592584236552208933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80418907654231856556895285 7539272592584236552208933)
                  ·
                    refine ⟨1413613611109544353539175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7539272592584236552208933 1413613611109544353539175)
                    ·
                      rfl

theorem cell22_4129504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_4129504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129504 prefixEnd_4129504 := by exact prefixLift 4129504
  have htrace : WordTrace (prefixWord ++ tailWord_4129504) baseStart_4129504 baseEnd_4129504 := by
    simpa [prefixWord, tailWord_4129504, baseEnd_4129504] using wordTrace_append hprefix tailTrace_4129504
  have hstable : (prefixWord ++ tailWord_4129504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129504).length < 2 ^ (prefixWord ++ tailWord_4129504).sum := by decide
  have hdescent : baseEnd_4129504 < baseStart_4129504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129512 : List Nat := [2, 1, 4, 1, 4, 1, 3, 2, 1, 3]
def baseStart_4129512 : Nat := 118140960795 + 4129512 * 2 ^ 59
def prefixEnd_4129512 : Nat := 4983230072969 + 3 ^ 40 * 4129512 * 2
def baseEnd_4129512 : Nat := 1413616349673034999339151

theorem tailTrace_4129512 : CollatzResearch.WordTrace tailWord_4129512 prefixEnd_4129512 1413616349673034999339151 := by
  unfold tailWord_4129512
  simp only [CollatzResearch.WordTrace]
  refine ⟨75307838107745381672867395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100410450810327175563823193 75307838107745381672867395)
  ·
    refine ⟨112961757161618072509301093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75307838107745381672867395 112961757161618072509301093)
    ·
      refine ⟨21180329467803388595493955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112961757161618072509301093 21180329467803388595493955)
      ·
        refine ⟨31770494201705082893240933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21180329467803388595493955 31770494201705082893240933)
        ·
          refine ⟨5956967662819703042482675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31770494201705082893240933 5956967662819703042482675)
          ·
            refine ⟨8935451494229554563724013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5956967662819703042482675 8935451494229554563724013)
            ·
              refine ⟨3350794310336082961396505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8935451494229554563724013 3350794310336082961396505)
              ·
                refine ⟨2513095732752062221047379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3350794310336082961396505 2513095732752062221047379)
                ·
                  refine ⟨3769643599128093331571069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2513095732752062221047379 3769643599128093331571069)
                  ·
                    refine ⟨1413616349673034999339151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3769643599128093331571069 1413616349673034999339151)
                    ·
                      rfl

theorem cell22_4129512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_4129512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129512 prefixEnd_4129512 := by exact prefixLift 4129512
  have htrace : WordTrace (prefixWord ++ tailWord_4129512) baseStart_4129512 baseEnd_4129512 := by
    simpa [prefixWord, tailWord_4129512, baseEnd_4129512] using wordTrace_append hprefix tailTrace_4129512
  have hstable : (prefixWord ++ tailWord_4129512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129512).length < 2 ^ (prefixWord ++ tailWord_4129512).sum := by decide
  have hdescent : baseEnd_4129512 < baseStart_4129512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129538 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_4129538 : Nat := 118140960795 + 4129538 * 2 ^ 59
def prefixEnd_4129538 : Nat := 4983230072969 + 3 ^ 40 * 4129538 * 2
def baseEnd_4129538 : Nat := 1413625250004379598189071

theorem tailTrace_4129538 : CollatzResearch.WordTrace tailWord_4129538 prefixEnd_4129538 1413625250004379598189071 := by
  unfold tailWord_4129538
  simp only [CollatzResearch.WordTrace]
  refine ⟨37654156128349142446545317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100411083008931046524120845 37654156128349142446545317)
  ·
    refine ⟨7060154274065464208727247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37654156128349142446545317 7060154274065464208727247)
    ·
      refine ⟨10590231411098196313090871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7060154274065464208727247 10590231411098196313090871)
      ·
        refine ⟨15885347116647294469636307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10590231411098196313090871 15885347116647294469636307)
        ·
          refine ⟨23828020674970941704454461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15885347116647294469636307 23828020674970941704454461)
          ·
            refine ⟨8935507753114103139170423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23828020674970941704454461 8935507753114103139170423)
            ·
              refine ⟨13403261629671154708755635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8935507753114103139170423 13403261629671154708755635)
              ·
                refine ⟨20104892444506732063133453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13403261629671154708755635 20104892444506732063133453)
                ·
                  refine ⟨7539334666690024523675045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20104892444506732063133453 7539334666690024523675045)
                  ·
                    refine ⟨1413625250004379598189071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7539334666690024523675045 1413625250004379598189071)
                    ·
                      rfl

theorem cell22_4129538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_4129538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129538 prefixEnd_4129538 := by exact prefixLift 4129538
  have htrace : WordTrace (prefixWord ++ tailWord_4129538) baseStart_4129538 baseEnd_4129538 := by
    simpa [prefixWord, tailWord_4129538, baseEnd_4129538] using wordTrace_append hprefix tailTrace_4129538
  have hstable : (prefixWord ++ tailWord_4129538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129538).length < 2 ^ (prefixWord ++ tailWord_4129538).sum := by decide
  have hdescent : baseEnd_4129538 < baseStart_4129538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129564 : List Nat := [2, 2, 3, 1, 1, 13]
def baseStart_4129564 : Nat := 118140960795 + 4129564 * 2 ^ 59
def prefixEnd_4129564 : Nat := 4983230072969 + 3 ^ 40 * 4129564 * 2
def baseEnd_4129564 : Nat := 17452273460934866630111

theorem tailTrace_4129564 : CollatzResearch.WordTrace tailWord_4129564 prefixEnd_4129564 17452273460934866630111 := by
  unfold tailWord_4129564
  simp only [CollatzResearch.WordTrace]
  refine ⟨75308786405651188113313873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100411715207534917484418497 75308786405651188113313873)
  ·
    refine ⟨56481589804238391084985405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75308786405651188113313873 56481589804238391084985405)
    ·
      refine ⟨21180596176589396656869527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56481589804238391084985405 21180596176589396656869527)
      ·
        refine ⟨31770894264884094985304291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21180596176589396656869527 31770894264884094985304291)
        ·
          refine ⟨47656341397326142477956437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31770894264884094985304291 47656341397326142477956437)
          ·
            refine ⟨17452273460934866630111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 47656341397326142477956437 17452273460934866630111)
            ·
              rfl

theorem cell22_4129564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 13].length) (baseStart_4129564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129564 prefixEnd_4129564 := by exact prefixLift 4129564
  have htrace : WordTrace (prefixWord ++ tailWord_4129564) baseStart_4129564 baseEnd_4129564 := by
    simpa [prefixWord, tailWord_4129564, baseEnd_4129564] using wordTrace_append hprefix tailTrace_4129564
  have hstable : (prefixWord ++ tailWord_4129564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129564).length < 2 ^ (prefixWord ++ tailWord_4129564).sum := by decide
  have hdescent : baseEnd_4129564 < baseStart_4129564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129568 : List Nat := [2, 1, 1, 5, 1, 2, 1, 4, 2, 3]
def baseStart_4129568 : Nat := 118140960795 + 4129568 * 2 ^ 59
def prefixEnd_4129568 : Nat := 4983230072969 + 3 ^ 40 * 4129568 * 2
def baseEnd_4129568 : Nat := 1413635519617469519938979

theorem tailTrace_4129568 : CollatzResearch.WordTrace tailWord_4129568 prefixEnd_4129568 1413635519617469519938979 := by
  unfold tailWord_4129568
  simp only [CollatzResearch.WordTrace]
  refine ⟨75308859351643942454886679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100411812468858589939848905 75308859351643942454886679)
  ·
    refine ⟨112963289027465913682330019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75308859351643942454886679 112963289027465913682330019)
    ·
      refine ⟨169444933541198870523495029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112963289027465913682330019 169444933541198870523495029)
      ·
        refine ⟨15885462519487394111577659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169444933541198870523495029 15885462519487394111577659)
        ·
          refine ⟨23828193779231091167366489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15885462519487394111577659 23828193779231091167366489)
          ·
            refine ⟨17871145334423318375524867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23828193779231091167366489 17871145334423318375524867)
            ·
              refine ⟨26806718001634977563287301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17871145334423318375524867 26806718001634977563287301)
              ·
                refine ⟨5026259625306558293116369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26806718001634977563287301 5026259625306558293116369)
                ·
                  refine ⟨3769694718979918719837277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5026259625306558293116369 3769694718979918719837277)
                  ·
                    refine ⟨1413635519617469519938979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3769694718979918719837277 1413635519617469519938979)
                    ·
                      rfl

theorem cell22_4129568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 2, 3].length) (baseStart_4129568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129568 prefixEnd_4129568 := by exact prefixLift 4129568
  have htrace : WordTrace (prefixWord ++ tailWord_4129568) baseStart_4129568 baseEnd_4129568 := by
    simpa [prefixWord, tailWord_4129568, baseEnd_4129568] using wordTrace_append hprefix tailTrace_4129568
  have hstable : (prefixWord ++ tailWord_4129568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129568).length < 2 ^ (prefixWord ++ tailWord_4129568).sum := by decide
  have hdescent : baseEnd_4129568 < baseStart_4129568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129570 : List Nat := [3, 3, 1, 1, 2, 2, 4, 2, 4]
def baseStart_4129570 : Nat := 118140960795 + 4129570 * 2 ^ 59
def prefixEnd_4129570 : Nat := 4983230072969 + 3 ^ 40 * 4129570 * 2
def baseEnd_4129570 : Nat := 471212068086114060462991

theorem tailTrace_4129570 : CollatzResearch.WordTrace tailWord_4129570 prefixEnd_4129570 471212068086114060462991 := by
  unfold tailWord_4129570
  simp only [CollatzResearch.WordTrace]
  refine ⟨37654447912320159812836541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100411861099520426167564109 37654447912320159812836541)
  ·
    refine ⟨14120417967120059929813703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37654447912320159812836541 14120417967120059929813703)
    ·
      refine ⟨21180626950680089894720555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14120417967120059929813703 21180626950680089894720555)
      ·
        refine ⟨31770940426020134842080833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21180626950680089894720555 31770940426020134842080833)
        ·
          refine ⟨23828205319515101131560625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31770940426020134842080833 23828205319515101131560625)
          ·
            refine ⟨17871153989636325848670469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23828205319515101131560625 17871153989636325848670469)
            ·
              refine ⟨3350841373056811096625713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17871153989636325848670469 3350841373056811096625713)
              ·
                refine ⟨2513131029792608322469285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3350841373056811096625713 2513131029792608322469285)
                ·
                  refine ⟨471212068086114060462991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2513131029792608322469285 471212068086114060462991)
                  ·
                    rfl

theorem cell22_4129570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_4129570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129570 prefixEnd_4129570 := by exact prefixLift 4129570
  have htrace : WordTrace (prefixWord ++ tailWord_4129570) baseStart_4129570 baseEnd_4129570 := by
    simpa [prefixWord, tailWord_4129570, baseEnd_4129570] using wordTrace_append hprefix tailTrace_4129570
  have hstable : (prefixWord ++ tailWord_4129570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129570).length < 2 ^ (prefixWord ++ tailWord_4129570).sum := by decide
  have hdescent : baseEnd_4129570 < baseStart_4129570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129606 : List Nat := [6, 1, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_4129606 : Nat := 118140960795 + 4129606 * 2 ^ 59
def prefixEnd_4129606 : Nat := 4983230072969 + 3 ^ 40 * 4129606 * 2
def baseEnd_4129606 : Nat := 1413648527794050087488863

theorem tailTrace_4129606 : CollatzResearch.WordTrace tailWord_4129606 prefixEnd_4129606 1413648527794050087488863 := by
  unfold tailWord_4129606
  simp only [CollatzResearch.WordTrace]
  refine ⟨4706847021160944293739271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100412736451433478266437781 4706847021160944293739271)
  ·
    refine ⟨7060270531741416440608907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4706847021160944293739271 7060270531741416440608907)
    ·
      refine ⟨10590405797612124660913361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7060270531741416440608907 10590405797612124660913361)
      ·
        refine ⟨7942804348209093495685021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10590405797612124660913361 7942804348209093495685021)
        ·
          refine ⟨2978551630578410060881883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7942804348209093495685021 2978551630578410060881883)
          ·
            refine ⟨4467827445867615091322825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2978551630578410060881883 4467827445867615091322825)
            ·
              refine ⟨3350870584400711318492119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4467827445867615091322825 3350870584400711318492119)
              ·
                refine ⟨5026305876601066977738179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3350870584400711318492119 5026305876601066977738179)
                ·
                  refine ⟨7539458814901600466607269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5026305876601066977738179 7539458814901600466607269)
                  ·
                    refine ⟨1413648527794050087488863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7539458814901600466607269 1413648527794050087488863)
                    ·
                      rfl

theorem cell22_4129606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_4129606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129606 prefixEnd_4129606 := by exact prefixLift 4129606
  have htrace : WordTrace (prefixWord ++ tailWord_4129606) baseStart_4129606 baseEnd_4129606 := by
    simpa [prefixWord, tailWord_4129606, baseEnd_4129606] using wordTrace_append hprefix tailTrace_4129606
  have hstable : (prefixWord ++ tailWord_4129606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129606).length < 2 ^ (prefixWord ++ tailWord_4129606).sum := by decide
  have hdescent : baseEnd_4129606 < baseStart_4129606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129626 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 7]
def baseStart_4129626 : Nat := 118140960795 + 4129626 * 2 ^ 59
def prefixEnd_4129626 : Nat := 4983230072969 + 3 ^ 40 * 4129626 * 2
def baseEnd_4129626 : Nat := 471218458067592233996267

theorem tailTrace_4129626 : CollatzResearch.WordTrace tailWord_4129626 prefixEnd_4129626 471218458067592233996267 := by
  unfold tailWord_4129626
  simp only [CollatzResearch.WordTrace]
  refine ⟨37654958534269440203846183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100413222758051840543589821 37654958534269440203846183)
  ·
    refine ⟨56482437801404160305769275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37654958534269440203846183 56482437801404160305769275)
    ·
      refine ⟨84723656702106240458653913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56482437801404160305769275 84723656702106240458653913)
      ·
        refine ⟨63542742526579680343990435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84723656702106240458653913 63542742526579680343990435)
        ·
          refine ⟨95314113789869520515985653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63542742526579680343990435 95314113789869520515985653)
          ·
            refine ⟨8935698167800267548373655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95314113789869520515985653 8935698167800267548373655)
            ·
              refine ⟨13403547251700401322560483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8935698167800267548373655 13403547251700401322560483)
              ·
                refine ⟨20105320877550601983840725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13403547251700401322560483 20105320877550601983840725)
                ·
                  refine ⟨471218458067592233996267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20105320877550601983840725 471218458067592233996267)
                  ·
                    rfl

theorem cell22_4129626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_4129626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129626 prefixEnd_4129626 := by exact prefixLift 4129626
  have htrace : WordTrace (prefixWord ++ tailWord_4129626) baseStart_4129626 baseEnd_4129626 := by
    simpa [prefixWord, tailWord_4129626, baseEnd_4129626] using wordTrace_append hprefix tailTrace_4129626
  have hstable : (prefixWord ++ tailWord_4129626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129626).length < 2 ^ (prefixWord ++ tailWord_4129626).sum := by decide
  have hdescent : baseEnd_4129626 < baseStart_4129626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129673 : List Nat := [1, 2, 1, 1, 5, 2, 2, 3, 1, 4]
def baseStart_4129673 : Nat := 118140960795 + 4129673 * 2 ^ 59
def prefixEnd_4129673 : Nat := 4983230072969 + 3 ^ 40 * 4129673 * 2
def baseEnd_4129673 : Nat := 1413671463263284246063657

theorem tailTrace_4129673 : CollatzResearch.WordTrace tailWord_4129673 prefixEnd_4129673 1413671463263284246063657 := by
  unfold tailWord_4129673
  simp only [CollatzResearch.WordTrace]
  refine ⟨150621548367907487842345673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100414365578604991894897115 150621548367907487842345673)
  ·
    refine ⟨112966161275930615881759255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150621548367907487842345673 112966161275930615881759255)
    ·
      refine ⟨169449241913895923822638883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112966161275930615881759255 169449241913895923822638883)
      ·
        refine ⟨254173862870843885733958325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169449241913895923822638883 254173862870843885733958325)
        ·
          refine ⟨23828799644141614287558593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254173862870843885733958325 23828799644141614287558593)
          ·
            refine ⟨17871599733106210715668945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23828799644141614287558593 17871599733106210715668945)
            ·
              refine ⟨13403699799829658036751709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17871599733106210715668945 13403699799829658036751709)
              ·
                refine ⟨5026387424936121763781891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13403699799829658036751709 5026387424936121763781891)
                ·
                  refine ⟨7539581137404182645672837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5026387424936121763781891 7539581137404182645672837)
                  ·
                    refine ⟨1413671463263284246063657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7539581137404182645672837 1413671463263284246063657)
                    ·
                      rfl

theorem cell22_4129673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 4].length) (baseStart_4129673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129673 prefixEnd_4129673 := by exact prefixLift 4129673
  have htrace : WordTrace (prefixWord ++ tailWord_4129673) baseStart_4129673 baseEnd_4129673 := by
    simpa [prefixWord, tailWord_4129673, baseEnd_4129673] using wordTrace_append hprefix tailTrace_4129673
  have hstable : (prefixWord ++ tailWord_4129673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129673).length < 2 ^ (prefixWord ++ tailWord_4129673).sum := by decide
  have hdescent : baseEnd_4129673 < baseStart_4129673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129750 : List Nat := [5, 2, 1, 1, 2, 1, 3, 7]
def baseStart_4129750 : Nat := 118140960795 + 4129750 * 2 ^ 59
def prefixEnd_4129750 : Nat := 4983230072969 + 3 ^ 40 * 4129750 * 2
def baseEnd_4129750 : Nat := 157077535770764634654269

theorem tailTrace_4129750 : CollatzResearch.WordTrace tailWord_4129750 prefixEnd_4129750 157077535770764634654269 := by
  unfold tailWord_4129750
  simp only [CollatzResearch.WordTrace]
  refine ⟨9414022299289283124556169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100416237859085686661932469 9414022299289283124556169)
  ·
    refine ⟨7060516724466962343417127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9414022299289283124556169 7060516724466962343417127)
    ·
      refine ⟨10590775086700443515125691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7060516724466962343417127 10590775086700443515125691)
      ·
        refine ⟨15886162630050665272688537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10590775086700443515125691 15886162630050665272688537)
        ·
          refine ⟨11914621972537998954516403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15886162630050665272688537 11914621972537998954516403)
          ·
            refine ⟨17871932958806998431774605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11914621972537998954516403 17871932958806998431774605)
            ·
              refine ⟨6701974859552624411915477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17871932958806998431774605 6701974859552624411915477)
              ·
                refine ⟨157077535770764634654269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6701974859552624411915477 157077535770764634654269)
                ·
                  rfl

theorem cell22_4129750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_4129750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129750 prefixEnd_4129750 := by exact prefixLift 4129750
  have htrace : WordTrace (prefixWord ++ tailWord_4129750) baseStart_4129750 baseEnd_4129750 := by
    simpa [prefixWord, tailWord_4129750, baseEnd_4129750] using wordTrace_append hprefix tailTrace_4129750
  have hstable : (prefixWord ++ tailWord_4129750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129750).length < 2 ^ (prefixWord ++ tailWord_4129750).sum := by decide
  have hdescent : baseEnd_4129750 < baseStart_4129750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129761 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 9]
def baseStart_4129761 : Nat := 118140960795 + 4129761 * 2 ^ 59
def prefixEnd_4129761 : Nat := 4983230072969 + 3 ^ 40 * 4129761 * 2
def baseEnd_4129761 : Nat := 471233862487227116621129

theorem tailTrace_4129761 : CollatzResearch.WordTrace tailWord_4129761 prefixEnd_4129761 471233862487227116621129 := by
  unfold tailWord_4129761
  simp only [CollatzResearch.WordTrace]
  refine ⟨150624757991588678871549137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100416505327725785914366091 150624757991588678871549137)
  ·
    refine ⟨112968568493691509153661853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150624757991588678871549137 112968568493691509153661853)
    ·
      refine ⟨42363213185134315932623195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112968568493691509153661853 42363213185134315932623195)
      ·
        refine ⟨63544819777701473898934793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42363213185134315932623195 63544819777701473898934793)
        ·
          refine ⟨47658614833276105424201095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63544819777701473898934793 47658614833276105424201095)
          ·
            refine ⟨71487922249914158136301643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47658614833276105424201095 71487922249914158136301643)
            ·
              refine ⟨107231883374871237204452465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71487922249914158136301643 107231883374871237204452465)
              ·
                refine ⟨80423912531153427903339349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107231883374871237204452465 80423912531153427903339349)
                ·
                  refine ⟨471233862487227116621129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80423912531153427903339349 471233862487227116621129)
                  ·
                    rfl

theorem cell22_4129761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 9].length) (baseStart_4129761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129761 prefixEnd_4129761 := by exact prefixLift 4129761
  have htrace : WordTrace (prefixWord ++ tailWord_4129761) baseStart_4129761 baseEnd_4129761 := by
    simpa [prefixWord, tailWord_4129761, baseEnd_4129761] using wordTrace_append hprefix tailTrace_4129761
  have hstable : (prefixWord ++ tailWord_4129761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129761).length < 2 ^ (prefixWord ++ tailWord_4129761).sum := by decide
  have hdescent : baseEnd_4129761 < baseStart_4129761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129776 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 3, 7]
def baseStart_4129776 : Nat := 118140960795 + 4129776 * 2 ^ 59
def prefixEnd_4129776 : Nat := 4983230072969 + 3 ^ 40 * 4129776 * 2
def baseEnd_4129776 : Nat := 1413706722268226310738341

theorem tailTrace_4129776 : CollatzResearch.WordTrace tailWord_4129776 prefixEnd_4129776 1413706722268226310738341 := by
  unfold tailWord_4129776
  simp only [CollatzResearch.WordTrace]
  refine ⟨75312652543267168216672591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100416870057689557622230121 75312652543267168216672591)
  ·
    refine ⟨112968978814900752325008887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75312652543267168216672591 112968978814900752325008887)
    ·
      refine ⟨169453468222351128487513331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112968978814900752325008887 169453468222351128487513331)
      ·
        refine ⟨254180202333526692731269997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169453468222351128487513331 254180202333526692731269997)
        ·
          refine ⟨95317575875072509774226249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254180202333526692731269997 95317575875072509774226249)
          ·
            refine ⟨71488181906304382330669687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95317575875072509774226249 71488181906304382330669687)
            ·
              refine ⟨107232272859456573496004531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71488181906304382330669687 107232272859456573496004531)
              ·
                refine ⟨160848409289184860244006797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107232272859456573496004531 160848409289184860244006797)
                ·
                  refine ⟨60318153483444322591502549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160848409289184860244006797 60318153483444322591502549)
                  ·
                    refine ⟨1413706722268226310738341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60318153483444322591502549 1413706722268226310738341)
                    ·
                      rfl

theorem cell22_4129776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_4129776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129776 prefixEnd_4129776 := by exact prefixLift 4129776
  have htrace : WordTrace (prefixWord ++ tailWord_4129776) baseStart_4129776 baseEnd_4129776 := by
    simpa [prefixWord, tailWord_4129776, baseEnd_4129776] using wordTrace_append hprefix tailTrace_4129776
  have hstable : (prefixWord ++ tailWord_4129776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129776).length < 2 ^ (prefixWord ++ tailWord_4129776).sum := by decide
  have hdescent : baseEnd_4129776 < baseStart_4129776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129793 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 2, 5]
def baseStart_4129793 : Nat := 118140960795 + 4129793 * 2 ^ 59
def prefixEnd_4129793 : Nat := 4983230072969 + 3 ^ 40 * 4129793 * 2
def baseEnd_4129793 : Nat := 1413712541715643933063289

theorem tailTrace_4129793 : CollatzResearch.WordTrace tailWord_4129793 prefixEnd_4129793 1413712541715643933063289 := by
  unfold tailWord_4129793
  simp only [CollatzResearch.WordTrace]
  refine ⟨150625925127472748336714033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100417283418315165557809355 150625925127472748336714033)
  ·
    refine ⟨112969443845604561252535525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150625925127472748336714033 112969443845604561252535525)
    ·
      refine ⟨21181770721050855234850411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112969443845604561252535525 21181770721050855234850411)
      ·
        refine ⟨31772656081576282852275617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21181770721050855234850411 31772656081576282852275617)
        ·
          refine ⟨23829492061182212139206713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31772656081576282852275617 23829492061182212139206713)
          ·
            refine ⟨17872119045886659104405035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23829492061182212139206713 17872119045886659104405035)
            ·
              refine ⟨26808178568829988656607553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17872119045886659104405035 26808178568829988656607553)
              ·
                refine ⟨20106133926622491492455665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26808178568829988656607553 20106133926622491492455665)
                ·
                  refine ⟨15079600444966868619341749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20106133926622491492455665 15079600444966868619341749)
                  ·
                    refine ⟨1413712541715643933063289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15079600444966868619341749 1413712541715643933063289)
                    ·
                      rfl

theorem cell22_4129793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_4129793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129793 prefixEnd_4129793 := by exact prefixLift 4129793
  have htrace : WordTrace (prefixWord ++ tailWord_4129793) baseStart_4129793 baseEnd_4129793 := by
    simpa [prefixWord, tailWord_4129793, baseEnd_4129793] using wordTrace_append hprefix tailTrace_4129793
  have hstable : (prefixWord ++ tailWord_4129793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129793).length < 2 ^ (prefixWord ++ tailWord_4129793).sum := by decide
  have hdescent : baseEnd_4129793 < baseStart_4129793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129823 : List Nat := [1, 1, 2, 4, 1, 3, 2, 2, 6]
def baseStart_4129823 : Nat := 118140960795 + 4129823 * 2 ^ 59
def prefixEnd_4129823 : Nat := 4983230072969 + 3 ^ 40 * 4129823 * 2
def baseEnd_4129823 : Nat := 471240937109577951604399

theorem tailTrace_4129823 : CollatzResearch.WordTrace tailWord_4129823 prefixEnd_4129823 471240937109577951604399 := by
  unfold tailWord_4129823
  simp only [CollatzResearch.WordTrace]
  refine ⟨150627019317364063460306123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100418012878242708973537415 150627019317364063460306123)
  ·
    refine ⟨225940528976046095190459185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150627019317364063460306123 225940528976046095190459185)
    ·
      refine ⟨169455396732034571392844389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225940528976046095190459185 169455396732034571392844389)
      ·
        refine ⟨31772886887256482136158323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169455396732034571392844389 31772886887256482136158323)
        ·
          refine ⟨47659330330884723204237485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31772886887256482136158323 47659330330884723204237485)
          ·
            refine ⟨17872248874081771201589057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47659330330884723204237485 17872248874081771201589057)
            ·
              refine ⟨13404186655561328401191793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17872248874081771201589057 13404186655561328401191793)
              ·
                refine ⟨10053139991670996300893845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13404186655561328401191793 10053139991670996300893845)
                ·
                  refine ⟨471240937109577951604399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10053139991670996300893845 471240937109577951604399)
                  ·
                    rfl

theorem cell22_4129823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 6].length) (baseStart_4129823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129823 prefixEnd_4129823 := by exact prefixLift 4129823
  have htrace : WordTrace (prefixWord ++ tailWord_4129823) baseStart_4129823 baseEnd_4129823 := by
    simpa [prefixWord, tailWord_4129823, baseEnd_4129823] using wordTrace_append hprefix tailTrace_4129823
  have hstable : (prefixWord ++ tailWord_4129823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129823).length < 2 ^ (prefixWord ++ tailWord_4129823).sum := by decide
  have hdescent : baseEnd_4129823 < baseStart_4129823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129825 : List Nat := [1, 2, 3, 2, 3, 1, 1, 4, 1, 4]
def baseStart_4129825 : Nat := 118140960795 + 4129825 * 2 ^ 59
def prefixEnd_4129825 : Nat := 4983230072969 + 3 ^ 40 * 4129825 * 2
def baseEnd_4129825 : Nat := 1413723495969606516263191

theorem tailTrace_4129825 : CollatzResearch.WordTrace tailWord_4129825 prefixEnd_4129825 1413723495969606516263191 := by
  unfold tailWord_4129825
  simp only [CollatzResearch.WordTrace]
  refine ⟨150627092263356817801878929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100418061508904545201252619 150627092263356817801878929)
  ·
    refine ⟨112970319197517613351409197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150627092263356817801878929 112970319197517613351409197)
    ·
      refine ⟨42363869699069105006778449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112970319197517613351409197 42363869699069105006778449)
      ·
        refine ⟨31772902274301828755083837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42363869699069105006778449 31772902274301828755083837)
        ·
          refine ⟨11914838352863185783156439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31772902274301828755083837 11914838352863185783156439)
          ·
            refine ⟨17872257529294778674734659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11914838352863185783156439 17872257529294778674734659)
            ·
              refine ⟨26808386293942168012101989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17872257529294778674734659 26808386293942168012101989)
              ·
                refine ⟨5026572430114156502269123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26808386293942168012101989 5026572430114156502269123)
                ·
                  refine ⟨7539858645171234753403685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5026572430114156502269123 7539858645171234753403685)
                  ·
                    refine ⟨1413723495969606516263191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7539858645171234753403685 1413723495969606516263191)
                    ·
                      rfl

theorem cell22_4129825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_4129825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129825 prefixEnd_4129825 := by exact prefixLift 4129825
  have htrace : WordTrace (prefixWord ++ tailWord_4129825) baseStart_4129825 baseEnd_4129825 := by
    simpa [prefixWord, tailWord_4129825, baseEnd_4129825] using wordTrace_append hprefix tailTrace_4129825
  have hstable : (prefixWord ++ tailWord_4129825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129825).length < 2 ^ (prefixWord ++ tailWord_4129825).sum := by decide
  have hdescent : baseEnd_4129825 < baseStart_4129825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129855 : List Nat := [1, 1, 2, 2, 3, 1, 1, 6, 2, 3]
def baseStart_4129855 : Nat := 118140960795 + 4129855 * 2 ^ 59
def prefixEnd_4129855 : Nat := 4983230072969 + 3 ^ 40 * 4129855 * 2
def baseEnd_4129855 : Nat := 1413733765582696438013099

theorem tailTrace_4129855 : CollatzResearch.WordTrace tailWord_4129855 prefixEnd_4129855 1413733765582696438013099 := by
  unfold tailWord_4129855
  simp only [CollatzResearch.WordTrace]
  refine ⟨150628186453248132925471019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100418790968832088616980679 150628186453248132925471019)
  ·
    refine ⟨225942279679872199388206529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150628186453248132925471019 225942279679872199388206529)
    ·
      refine ⟨169456709759904149541154897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225942279679872199388206529 169456709759904149541154897)
      ·
        refine ⟨127092532319928112155866173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169456709759904149541154897 127092532319928112155866173)
        ·
          refine ⟨47659699619973042058449815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127092532319928112155866173 47659699619973042058449815)
          ·
            refine ⟨71489549429959563087674723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47659699619973042058449815 71489549429959563087674723)
            ·
              refine ⟨107234324144939344631512085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71489549429959563087674723 107234324144939344631512085)
              ·
                refine ⟨5026608944294031779602129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107234324144939344631512085 5026608944294031779602129)
                ·
                  refine ⟨3769956708220523834701597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5026608944294031779602129 3769956708220523834701597)
                  ·
                    refine ⟨1413733765582696438013099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3769956708220523834701597 1413733765582696438013099)
                    ·
                      rfl

theorem cell22_4129855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 3].length) (baseStart_4129855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129855 prefixEnd_4129855 := by exact prefixLift 4129855
  have htrace : WordTrace (prefixWord ++ tailWord_4129855) baseStart_4129855 baseEnd_4129855 := by
    simpa [prefixWord, tailWord_4129855, baseEnd_4129855] using wordTrace_append hprefix tailTrace_4129855
  have hstable : (prefixWord ++ tailWord_4129855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129855).length < 2 ^ (prefixWord ++ tailWord_4129855).sum := by decide
  have hdescent : baseEnd_4129855 < baseStart_4129855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129857 : List Nat := [1, 2, 5, 1, 3, 2, 1, 1, 6]
def baseStart_4129857 : Nat := 118140960795 + 4129857 * 2 ^ 59
def prefixEnd_4129857 : Nat := 4983230072969 + 3 ^ 40 * 4129857 * 2
def baseEnd_4129857 : Nat := 471244816741189699821031

theorem tailTrace_4129857 : CollatzResearch.WordTrace tailWord_4129857 prefixEnd_4129857 471244816741189699821031 := by
  unfold tailWord_4129857
  simp only [CollatzResearch.WordTrace]
  refine ⟨150628259399240887267043825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100418839599493924844695883 150628259399240887267043825)
  ·
    refine ⟨112971194549430665450282869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150628259399240887267043825 112971194549430665450282869)
    ·
      refine ⟨10591049489009124885964019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112971194549430665450282869 10591049489009124885964019)
      ·
        refine ⟨15886574233513687328946029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10591049489009124885964019 15886574233513687328946029)
        ·
          refine ⟨5957465337567632748354761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15886574233513687328946029 5957465337567632748354761)
          ·
            refine ⟨4468099003175724561266071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5957465337567632748354761 4468099003175724561266071)
            ·
              refine ⟨6702148504763586841899107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4468099003175724561266071 6702148504763586841899107)
              ·
                refine ⟨10053222757145380262848661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6702148504763586841899107 10053222757145380262848661)
                ·
                  refine ⟨471244816741189699821031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10053222757145380262848661 471244816741189699821031)
                  ·
                    rfl

theorem cell22_4129857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 6].length) (baseStart_4129857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129857 prefixEnd_4129857 := by exact prefixLift 4129857
  have htrace : WordTrace (prefixWord ++ tailWord_4129857) baseStart_4129857 baseEnd_4129857 := by
    simpa [prefixWord, tailWord_4129857, baseEnd_4129857] using wordTrace_append hprefix tailTrace_4129857
  have hstable : (prefixWord ++ tailWord_4129857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129857).length < 2 ^ (prefixWord ++ tailWord_4129857).sum := by decide
  have hdescent : baseEnd_4129857 < baseStart_4129857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129930 : List Nat := [3, 1, 2, 3, 1, 1, 1, 5, 5]
def baseStart_4129930 : Nat := 118140960795 + 4129930 * 2 ^ 59
def prefixEnd_4129930 : Nat := 4983230072969 + 3 ^ 40 * 4129930 * 2
def baseEnd_4129930 : Nat := 471253146538473747462623

theorem tailTrace_4129930 : CollatzResearch.WordTrace tailWord_4129930 prefixEnd_4129930 471253146538473747462623 := by
  unfold tailWord_4129930
  simp only [CollatzResearch.WordTrace]
  refine ⟨37657730481994105183612811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100420614618650947156300829 37657730481994105183612811)
  ·
    refine ⟨56486595722991157775419217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37657730481994105183612811 56486595722991157775419217)
    ·
      refine ⟨42364946792243368331564413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56486595722991157775419217 42364946792243368331564413)
      ·
        refine ⟨15886855047091263124336655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42364946792243368331564413 15886855047091263124336655)
        ·
          refine ⟨23830282570636894686504983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15886855047091263124336655 23830282570636894686504983)
          ·
            refine ⟨35745423855955342029757475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23830282570636894686504983 35745423855955342029757475)
            ·
              refine ⟨53618135783933013044636213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35745423855955342029757475 53618135783933013044636213)
              ·
                refine ⟨5026700229743719972934645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53618135783933013044636213 5026700229743719972934645)
                ·
                  refine ⟨471253146538473747462623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5026700229743719972934645 471253146538473747462623)
                  ·
                    rfl

theorem cell22_4129930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_4129930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129930 prefixEnd_4129930 := by exact prefixLift 4129930
  have htrace : WordTrace (prefixWord ++ tailWord_4129930) baseStart_4129930 baseEnd_4129930 := by
    simpa [prefixWord, tailWord_4129930, baseEnd_4129930] using wordTrace_append hprefix tailTrace_4129930
  have hstable : (prefixWord ++ tailWord_4129930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129930).length < 2 ^ (prefixWord ++ tailWord_4129930).sum := by decide
  have hdescent : baseEnd_4129930 < baseStart_4129930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129951 : List Nat := [1, 1, 2, 6, 2, 1, 2, 3, 1, 3]
def baseStart_4129951 : Nat := 118140960795 + 4129951 * 2 ^ 59
def prefixEnd_4129951 : Nat := 4983230072969 + 3 ^ 40 * 4129951 * 2
def baseEnd_4129951 : Nat := 1413766628344584187612805

theorem tailTrace_4129951 : CollatzResearch.WordTrace tailWord_4129951 prefixEnd_4129951 1413766628344584187612805 := by
  unfold tailWord_4129951
  simp only [CollatzResearch.WordTrace]
  refine ⟨150631687860900341320965707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100421125240600227547310471 150631687860900341320965707)
  ·
    refine ⟨225947531791350511981448561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150631687860900341320965707 225947531791350511981448561)
    ·
      refine ⟨169460648843512883986086421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225947531791350511981448561 169460648843512883986086421)
      ·
        refine ⟨7943467914539666436847801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 169460648843512883986086421 7943467914539666436847801)
        ·
          refine ⟨5957600935904749827635851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7943467914539666436847801 5957600935904749827635851)
          ·
            refine ⟨8936401403857124741453777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5957600935904749827635851 8936401403857124741453777)
            ·
              refine ⟨6702301052892843556090333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8936401403857124741453777 6702301052892843556090333)
              ·
                refine ⟨2513362894834816333533875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6702301052892843556090333 2513362894834816333533875)
                ·
                  refine ⟨3770044342252224500300813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2513362894834816333533875 3770044342252224500300813)
                  ·
                    refine ⟨1413766628344584187612805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3770044342252224500300813 1413766628344584187612805)
                    ·
                      rfl

theorem cell22_4129951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 1, 3].length) (baseStart_4129951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129951 prefixEnd_4129951 := by exact prefixLift 4129951
  have htrace : WordTrace (prefixWord ++ tailWord_4129951) baseStart_4129951 baseEnd_4129951 := by
    simpa [prefixWord, tailWord_4129951, baseEnd_4129951] using wordTrace_append hprefix tailTrace_4129951
  have hstable : (prefixWord ++ tailWord_4129951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129951).length < 2 ^ (prefixWord ++ tailWord_4129951).sum := by decide
  have hdescent : baseEnd_4129951 < baseStart_4129951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129962 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 2, 5]
def baseStart_4129962 : Nat := 118140960795 + 4129962 * 2 ^ 59
def prefixEnd_4129962 : Nat := 4983230072969 + 3 ^ 40 * 4129962 * 2
def baseEnd_4129962 : Nat := 1413770393869383825587771

theorem tailTrace_4129962 : CollatzResearch.WordTrace tailWord_4129962 prefixEnd_4129962 1413770393869383825587771 := by
  unfold tailWord_4129962
  simp only [CollatzResearch.WordTrace]
  refine ⟨37658022265965122549904035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100421392709240326799744093 37658022265965122549904035)
  ·
    refine ⟨56487033398947683824856053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37658022265965122549904035 56487033398947683824856053)
    ·
      refine ⟨5295659381151345358580255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56487033398947683824856053 5295659381151345358580255)
      ·
        refine ⟨7943489071727018037870383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5295659381151345358580255 7943489071727018037870383)
        ·
          refine ⟨11915233607590527056805575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7943489071727018037870383 11915233607590527056805575)
          ·
            refine ⟨17872850411385790585208363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11915233607590527056805575 17872850411385790585208363)
            ·
              refine ⟨26809275617078685877812545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17872850411385790585208363 26809275617078685877812545)
              ·
                refine ⟨20106956712809014408359409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26809275617078685877812545 20106956712809014408359409)
                ·
                  refine ⟨15080217534606760806269557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20106956712809014408359409 15080217534606760806269557)
                  ·
                    refine ⟨1413770393869383825587771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15080217534606760806269557 1413770393869383825587771)
                    ·
                      rfl

theorem cell22_4129962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_4129962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129962 prefixEnd_4129962 := by exact prefixLift 4129962
  have htrace : WordTrace (prefixWord ++ tailWord_4129962) baseStart_4129962 baseEnd_4129962 := by
    simpa [prefixWord, tailWord_4129962, baseEnd_4129962] using wordTrace_append hprefix tailTrace_4129962
  have hstable : (prefixWord ++ tailWord_4129962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129962).length < 2 ^ (prefixWord ++ tailWord_4129962).sum := by decide
  have hdescent : baseEnd_4129962 < baseStart_4129962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4129975 : List Nat := [1, 1, 3, 1, 4, 1, 4, 1, 6]
def baseStart_4129975 : Nat := 118140960795 + 4129975 * 2 ^ 59
def prefixEnd_4129975 : Nat := 4983230072969 + 3 ^ 40 * 4129975 * 2
def baseEnd_4129975 : Nat := 471258281345018708337577

theorem tailTrace_4129975 : CollatzResearch.WordTrace tailWord_4129975 prefixEnd_4129975 471258281345018708337577 := by
  unfold tailWord_4129975
  simp only [CollatzResearch.WordTrace]
  refine ⟨150632563212813393419839379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100421708808542262279892919 150632563212813393419839379)
  ·
    refine ⟨225948844819220090129759069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150632563212813393419839379 225948844819220090129759069)
    ·
      refine ⟨84730816807207533798659651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225948844819220090129759069 84730816807207533798659651)
      ·
        refine ⟨127096225210811300697989477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84730816807207533798659651 127096225210811300697989477)
        ·
          refine ⟨23830542227027118880873027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127096225210811300697989477 23830542227027118880873027)
          ·
            refine ⟨35745813340540678321309541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23830542227027118880873027 35745813340540678321309541)
            ·
              refine ⟨6702340001351377185245539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35745813340540678321309541 6702340001351377185245539)
              ·
                refine ⟨10053510002027065777868309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6702340001351377185245539 10053510002027065777868309)
                ·
                  refine ⟨471258281345018708337577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10053510002027065777868309 471258281345018708337577)
                  ·
                    rfl

theorem cell22_4129975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 6].length) (baseStart_4129975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4129975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4129975 prefixEnd_4129975 := by exact prefixLift 4129975
  have htrace : WordTrace (prefixWord ++ tailWord_4129975) baseStart_4129975 baseEnd_4129975 := by
    simpa [prefixWord, tailWord_4129975, baseEnd_4129975] using wordTrace_append hprefix tailTrace_4129975
  have hstable : (prefixWord ++ tailWord_4129975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4129975).length < 2 ^ (prefixWord ++ tailWord_4129975).sum := by decide
  have hdescent : baseEnd_4129975 < baseStart_4129975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4129975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130003 : List Nat := [1, 1, 1, 2, 1, 1, 1, 14]
def baseStart_4130003 : Nat := 118140960795 + 4130003 * 2 ^ 59
def prefixEnd_4130003 : Nat := 4983230072969 + 3 ^ 40 * 4130003 * 2
def baseEnd_4130003 : Nat := 157087158778585931701405

theorem tailTrace_4130003 : CollatzResearch.WordTrace tailWord_4130003 prefixEnd_4130003 157087158778585931701405 := by
  unfold tailWord_4130003
  simp only [CollatzResearch.WordTrace]
  refine ⟨150633584456711954201858663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100422389637807969467905775 150633584456711954201858663)
  ·
    refine ⟨225950376685067931302787995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150633584456711954201858663 225950376685067931302787995)
    ·
      refine ⟨338925565027601896954181993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225950376685067931302787995 338925565027601896954181993)
      ·
        refine ⟨254194173770701422715636495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338925565027601896954181993 254194173770701422715636495)
        ·
          refine ⟨381291260656052134073454743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254194173770701422715636495 381291260656052134073454743)
          ·
            refine ⟨571936890984078201110182115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381291260656052134073454743 571936890984078201110182115)
            ·
              refine ⟨857905336476117301665273173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 571936890984078201110182115 857905336476117301665273173)
              ·
                refine ⟨157087158778585931701405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 857905336476117301665273173 157087158778585931701405)
                ·
                  rfl

theorem cell22_4130003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 14].length) (baseStart_4130003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130003 prefixEnd_4130003 := by exact prefixLift 4130003
  have htrace : WordTrace (prefixWord ++ tailWord_4130003) baseStart_4130003 baseEnd_4130003 := by
    simpa [prefixWord, tailWord_4130003, baseEnd_4130003] using wordTrace_append hprefix tailTrace_4130003
  have hstable : (prefixWord ++ tailWord_4130003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130003).length < 2 ^ (prefixWord ++ tailWord_4130003).sum := by decide
  have hdescent : baseEnd_4130003 < baseStart_4130003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130069 : List Nat := [1, 3, 2, 1, 2, 1, 1, 7, 1, 3]
def baseStart_4130069 : Nat := 118140960795 + 4130069 * 2 ^ 59
def prefixEnd_4130069 : Nat := 4983230072969 + 3 ^ 40 * 4130069 * 2
def baseEnd_4130069 : Nat := 1413807022156071213162443

theorem tailTrace_4130069 : CollatzResearch.WordTrace tailWord_4130069 prefixEnd_4130069 1413807022156071213162443 := by
  unfold tailWord_4130069
  simp only [CollatzResearch.WordTrace]
  refine ⟨150635991674472847473761261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100423994449648564982507507 150635991674472847473761261)
  ·
    refine ⟨56488496877927317802660473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150635991674472847473761261 56488496877927317802660473)
    ·
      refine ⟨42366372658445488351995355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56488496877927317802660473 42366372658445488351995355)
      ·
        refine ⟨63549558987668232527993033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42366372658445488351995355 63549558987668232527993033)
        ·
          refine ⟨47662169240751174395994775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63549558987668232527993033 47662169240751174395994775)
          ·
            refine ⟨71493253861126761593992163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47662169240751174395994775 71493253861126761593992163)
            ·
              refine ⟨107239880791690142390988245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71493253861126761593992163 107239880791690142390988245)
              ·
                refine ⟨2513434706055237712288787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 107239880791690142390988245 2513434706055237712288787)
                ·
                  refine ⟨3770152059082856568433181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2513434706055237712288787 3770152059082856568433181)
                  ·
                    refine ⟨1413807022156071213162443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3770152059082856568433181 1413807022156071213162443)
                    ·
                      rfl

theorem cell22_4130069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_4130069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130069 prefixEnd_4130069 := by exact prefixLift 4130069
  have htrace : WordTrace (prefixWord ++ tailWord_4130069) baseStart_4130069 baseEnd_4130069 := by
    simpa [prefixWord, tailWord_4130069, baseEnd_4130069] using wordTrace_append hprefix tailTrace_4130069
  have hstable : (prefixWord ++ tailWord_4130069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130069).length < 2 ^ (prefixWord ++ tailWord_4130069).sum := by decide
  have hdescent : baseEnd_4130069 < baseStart_4130069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130097 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 2, 5]
def baseStart_4130097 : Nat := 118140960795 + 4130097 * 2 ^ 59
def prefixEnd_4130097 : Nat := 4983230072969 + 3 ^ 40 * 4130097 * 2
def baseEnd_4130097 : Nat := 1413816607128288473462357

theorem tailTrace_4130097 : CollatzResearch.WordTrace tailWord_4130097 prefixEnd_4130097 1413816607128288473462357 := by
  unfold tailWord_4130097
  simp only [CollatzResearch.WordTrace]
  refine ⟨150637012918371408255780545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100424675278914272170520363 150637012918371408255780545)
  ·
    refine ⟨112977759688778556191835409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150637012918371408255780545 112977759688778556191835409)
    ·
      refine ⟨84733319766583917143876557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112977759688778556191835409 84733319766583917143876557)
      ·
        refine ⟨31774994912468968928953709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84733319766583917143876557 31774994912468968928953709)
        ·
          refine ⟨11915623092175863348357641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31774994912468968928953709 11915623092175863348357641)
          ·
            refine ⟨8936717319131897511268231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11915623092175863348357641 8936717319131897511268231)
            ·
              refine ⟨13405075978697846266902347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8936717319131897511268231 13405075978697846266902347)
              ·
                refine ⟨20107613968046769400353521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13405075978697846266902347 20107613968046769400353521)
                ·
                  refine ⟨15080710476035077050265141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20107613968046769400353521 15080710476035077050265141)
                  ·
                    refine ⟨1413816607128288473462357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15080710476035077050265141 1413816607128288473462357)
                    ·
                      rfl

theorem cell22_4130097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_4130097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130097 prefixEnd_4130097 := by exact prefixLift 4130097
  have htrace : WordTrace (prefixWord ++ tailWord_4130097) baseStart_4130097 baseEnd_4130097 := by
    simpa [prefixWord, tailWord_4130097, baseEnd_4130097] using wordTrace_append hprefix tailTrace_4130097
  have hstable : (prefixWord ++ tailWord_4130097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130097).length < 2 ^ (prefixWord ++ tailWord_4130097).sum := by decide
  have hdescent : baseEnd_4130097 < baseStart_4130097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130112 : List Nat := [2, 1, 1, 2, 2, 1, 4, 4, 1, 4]
def baseStart_4130112 : Nat := 118140960795 + 4130112 * 2 ^ 59
def prefixEnd_4130112 : Nat := 4983230072969 + 3 ^ 40 * 4130112 * 2
def baseEnd_4130112 : Nat := 1413821741934833434337311

theorem tailTrace_4130112 : CollatzResearch.WordTrace tailWord_4130112 prefixEnd_4130112 1413821741934833434337311 := by
  unfold tailWord_4130112
  simp only [CollatzResearch.WordTrace]
  refine ⟨75318780006658532908788295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100425040008878043878384393 75318780006658532908788295)
  ·
    refine ⟨112978170009987799363182443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75318780006658532908788295 112978170009987799363182443)
    ·
      refine ⟨169467255014981699044773665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112978170009987799363182443 169467255014981699044773665)
      ·
        refine ⟨127100441261236274283580249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169467255014981699044773665 127100441261236274283580249)
        ·
          refine ⟨95325330945927205712685187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127100441261236274283580249 95325330945927205712685187)
          ·
            refine ⟨142987996418890808569027781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95325330945927205712685187 142987996418890808569027781)
            ·
              refine ⟨26810249328542026606692709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142987996418890808569027781 26810249328542026606692709)
              ·
                refine ⟨5026921749101629988754883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26810249328542026606692709 5026921749101629988754883)
                ·
                  refine ⟨7540382623652444983132325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5026921749101629988754883 7540382623652444983132325)
                  ·
                    refine ⟨1413821741934833434337311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7540382623652444983132325 1413821741934833434337311)
                    ·
                      rfl

theorem cell22_4130112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 1, 4].length) (baseStart_4130112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130112 prefixEnd_4130112 := by exact prefixLift 4130112
  have htrace : WordTrace (prefixWord ++ tailWord_4130112) baseStart_4130112 baseEnd_4130112 := by
    simpa [prefixWord, tailWord_4130112, baseEnd_4130112] using wordTrace_append hprefix tailTrace_4130112
  have hstable : (prefixWord ++ tailWord_4130112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130112).length < 2 ^ (prefixWord ++ tailWord_4130112).sum := by decide
  have hdescent : baseEnd_4130112 < baseStart_4130112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130144 : List Nat := [2, 1, 1, 3, 4, 1, 2, 4, 4]
def baseStart_4130144 : Nat := 118140960795 + 4130144 * 2 ^ 59
def prefixEnd_4130144 : Nat := 4983230072969 + 3 ^ 40 * 4130144 * 2
def baseEnd_4130144 : Nat := 471277565396265339179071

theorem tailTrace_4130144 : CollatzResearch.WordTrace tailWord_4130144 prefixEnd_4130144 471277565396265339179071 := by
  unfold tailWord_4130144
  simp only [CollatzResearch.WordTrace]
  refine ⟨75319363574600567641370743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100425818099467423521827657 75319363574600567641370743)
  ·
    refine ⟨112979045361900851462056115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75319363574600567641370743 112979045361900851462056115)
    ·
      refine ⟨169468568042851277193084173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112979045361900851462056115 169468568042851277193084173)
      ·
        refine ⟨63550713016069228947406565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169468568042851277193084173 63550713016069228947406565)
        ·
          refine ⟨11915758690512980427638731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63550713016069228947406565 11915758690512980427638731)
          ·
            refine ⟨17873638035769470641458097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11915758690512980427638731 17873638035769470641458097)
            ·
              refine ⟨13405228526827102981093573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17873638035769470641458097 13405228526827102981093573)
              ·
                refine ⟨2513480348780081808955045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13405228526827102981093573 2513480348780081808955045)
                ·
                  refine ⟨471277565396265339179071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2513480348780081808955045 471277565396265339179071)
                  ·
                    rfl

theorem cell22_4130144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 4].length) (baseStart_4130144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130144 prefixEnd_4130144 := by exact prefixLift 4130144
  have htrace : WordTrace (prefixWord ++ tailWord_4130144) baseStart_4130144 baseEnd_4130144 := by
    simpa [prefixWord, tailWord_4130144, baseEnd_4130144] using wordTrace_append hprefix tailTrace_4130144
  have hstable : (prefixWord ++ tailWord_4130144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130144).length < 2 ^ (prefixWord ++ tailWord_4130144).sum := by decide
  have hdescent : baseEnd_4130144 < baseStart_4130144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130157 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_4130157 : Nat := 118140960795 + 4130157 * 2 ^ 59
def prefixEnd_4130157 : Nat := 4983230072969 + 3 ^ 40 * 4130157 * 2
def baseEnd_4130157 : Nat := 1413837146354468316962173

theorem tailTrace_4130157 : CollatzResearch.WordTrace tailWord_4130157 prefixEnd_4130157 1413837146354468316962173 := by
  unfold tailWord_4130157
  simp only [CollatzResearch.WordTrace]
  refine ⟨150639201298154038502964725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100426134198769359001976483 150639201298154038502964725)
  ·
    refine ⟨14122425121701941109652943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150639201298154038502964725 14122425121701941109652943)
    ·
      refine ⟨21183637682552911664479415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14122425121701941109652943 21183637682552911664479415)
      ·
        refine ⟨31775456523829367496719123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21183637682552911664479415 31775456523829367496719123)
        ·
          refine ⟨47663184785744051245078685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31775456523829367496719123 47663184785744051245078685)
          ·
            refine ⟨17873694294654019216904507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47663184785744051245078685 17873694294654019216904507)
            ·
              refine ⟨26810541441981028825356761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17873694294654019216904507 26810541441981028825356761)
              ·
                refine ⟨20107906081485771619017571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26810541441981028825356761 20107906081485771619017571)
                ·
                  refine ⟨30161859122228657428526357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20107906081485771619017571 30161859122228657428526357)
                  ·
                    refine ⟨1413837146354468316962173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30161859122228657428526357 1413837146354468316962173)
                    ·
                      rfl

theorem cell22_4130157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_4130157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130157 prefixEnd_4130157 := by exact prefixLift 4130157
  have htrace : WordTrace (prefixWord ++ tailWord_4130157) baseStart_4130157 baseEnd_4130157 := by
    simpa [prefixWord, tailWord_4130157, baseEnd_4130157] using wordTrace_append hprefix tailTrace_4130157
  have hstable : (prefixWord ++ tailWord_4130157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130157).length < 2 ^ (prefixWord ++ tailWord_4130157).sum := by decide
  have hdescent : baseEnd_4130157 < baseStart_4130157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130178 : List Nat := [3, 4, 2, 1, 1, 1, 3, 3, 4]
def baseStart_4130178 : Nat := 118140960795 + 4130178 * 2 ^ 59
def prefixEnd_4130178 : Nat := 4983230072969 + 3 ^ 40 * 4130178 * 2
def baseEnd_4130178 : Nat := 471281445027877087395703

theorem tailTrace_4130178 : CollatzResearch.WordTrace tailWord_4130178 prefixEnd_4130178 471281445027877087395703 := by
  unfold tailWord_4130178
  simp only [CollatzResearch.WordTrace]
  refine ⟨37659991807769489772369797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100426644820718639392986125 37659991807769489772369797)
  ·
    refine ⟨7061248463956779332319337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37659991807769489772369797 7061248463956779332319337)
    ·
      refine ⟨5295936347967584499239503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7061248463956779332319337 5295936347967584499239503)
      ·
        refine ⟨7943904521951376748859255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5295936347967584499239503 7943904521951376748859255)
        ·
          refine ⟨11915856782927065123288883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7943904521951376748859255 11915856782927065123288883)
          ·
            refine ⟨17873785174390597684933325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11915856782927065123288883 17873785174390597684933325)
            ·
              refine ⟨6702669440396474131849997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17873785174390597684933325 6702669440396474131849997)
              ·
                refine ⟨2513501040148677799443749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6702669440396474131849997 2513501040148677799443749)
                ·
                  refine ⟨471281445027877087395703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2513501040148677799443749 471281445027877087395703)
                  ·
                    rfl

theorem cell22_4130178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_4130178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130178 prefixEnd_4130178 := by exact prefixLift 4130178
  have htrace : WordTrace (prefixWord ++ tailWord_4130178) baseStart_4130178 baseEnd_4130178 := by
    simpa [prefixWord, tailWord_4130178, baseEnd_4130178] using wordTrace_append hprefix tailTrace_4130178
  have hstable : (prefixWord ++ tailWord_4130178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130178).length < 2 ^ (prefixWord ++ tailWord_4130178).sum := by decide
  have hdescent : baseEnd_4130178 < baseStart_4130178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130202 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 2, 6]
def baseStart_4130202 : Nat := 118140960795 + 4130202 * 2 ^ 59
def prefixEnd_4130202 : Nat := 4983230072969 + 3 ^ 40 * 4130202 * 2
def baseEnd_4130202 : Nat := 1413852550774103199587035

theorem tailTrace_4130202 : CollatzResearch.WordTrace tailWord_4130202 prefixEnd_4130202 1413852550774103199587035 := by
  unfold tailWord_4130202
  simp only [CollatzResearch.WordTrace]
  refine ⟨37660210645747752797088215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100427228388660674125568573 37660210645747752797088215)
  ·
    refine ⟨56490315968621629195632323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37660210645747752797088215 56490315968621629195632323)
    ·
      refine ⟨84735473952932443793448485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56490315968621629195632323 84735473952932443793448485)
      ·
        refine ⟨15887901366174833211271591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84735473952932443793448485 15887901366174833211271591)
        ·
          refine ⟨23831852049262249816907387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15887901366174833211271591 23831852049262249816907387)
          ·
            refine ⟨35747778073893374725361081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23831852049262249816907387 35747778073893374725361081)
            ·
              refine ⟨26810833555420031044020811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35747778073893374725361081 26810833555420031044020811)
              ·
                refine ⟨40216250333130046566031217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26810833555420031044020811 40216250333130046566031217)
                ·
                  refine ⟨30162187749847534924523413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40216250333130046566031217 30162187749847534924523413)
                  ·
                    refine ⟨1413852550774103199587035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30162187749847534924523413 1413852550774103199587035)
                    ·
                      rfl

theorem cell22_4130202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_4130202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130202 prefixEnd_4130202 := by exact prefixLift 4130202
  have htrace : WordTrace (prefixWord ++ tailWord_4130202) baseStart_4130202 baseEnd_4130202 := by
    simpa [prefixWord, tailWord_4130202, baseEnd_4130202] using wordTrace_append hprefix tailTrace_4130202
  have hstable : (prefixWord ++ tailWord_4130202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130202).length < 2 ^ (prefixWord ++ tailWord_4130202).sum := by decide
  have hdescent : baseEnd_4130202 < baseStart_4130202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130206 : List Nat := [4, 3, 1, 2, 2, 1, 2, 7]
def baseStart_4130206 : Nat := 118140960795 + 4130206 * 2 ^ 59
def prefixEnd_4130206 : Nat := 4983230072969 + 3 ^ 40 * 4130206 * 2
def baseEnd_4130206 : Nat := 157094880006205391387447

theorem tailTrace_4130206 : CollatzResearch.WordTrace tailWord_4130206 prefixEnd_4130206 157094880006205391387447 := by
  unfold tailWord_4130206
  simp only [CollatzResearch.WordTrace]
  refine ⟨18830123559372064983937309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100427325649984346580998981 18830123559372064983937309)
  ·
    refine ⟨7061296334764524368976491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18830123559372064983937309 7061296334764524368976491)
    ·
      refine ⟨10591944502146786553464737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7061296334764524368976491 10591944502146786553464737)
      ·
        refine ⟨7943958376610089915098553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10591944502146786553464737 7943958376610089915098553)
        ·
          refine ⟨5957968782457567436323915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7943958376610089915098553 5957968782457567436323915)
          ·
            refine ⟨8936953173686351154485873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5957968782457567436323915 8936953173686351154485873)
            ·
              refine ⟨6702714880264763365864405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8936953173686351154485873 6702714880264763365864405)
              ·
                refine ⟨157094880006205391387447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6702714880264763365864405 157094880006205391387447)
                ·
                  rfl

theorem cell22_4130206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_4130206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130206 prefixEnd_4130206 := by exact prefixLift 4130206
  have htrace : WordTrace (prefixWord ++ tailWord_4130206) baseStart_4130206 baseEnd_4130206 := by
    simpa [prefixWord, tailWord_4130206, baseEnd_4130206] using wordTrace_append hprefix tailTrace_4130206
  have hstable : (prefixWord ++ tailWord_4130206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130206).length < 2 ^ (prefixWord ++ tailWord_4130206).sum := by decide
  have hdescent : baseEnd_4130206 < baseStart_4130206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130279 : List Nat := [1, 1, 5, 2, 1, 3, 1, 2, 6]
def baseStart_4130279 : Nat := 118140960795 + 4130279 * 2 ^ 59
def prefixEnd_4130279 : Nat := 4983230072969 + 3 ^ 40 * 4130279 * 2
def baseEnd_4130279 : Nat := 471292969815900221803933

theorem tailTrace_4130279 : CollatzResearch.WordTrace tailWord_4130279 prefixEnd_4130279 471292969815900221803933 := by
  unfold tailWord_4130279
  simp only [CollatzResearch.WordTrace]
  refine ⟨150643651003712053338905891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100429100669141368892603927 150643651003712053338905891)
  ·
    refine ⟨225965476505568080008358837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150643651003712053338905891 225965476505568080008358837)
    ·
      refine ⟨21184263422397007500783641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225965476505568080008358837 21184263422397007500783641)
      ·
        refine ⟨15888197566797755625587731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21184263422397007500783641 15888197566797755625587731)
        ·
          refine ⟨23832296350196633438381597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15888197566797755625587731 23832296350196633438381597)
          ·
            refine ⟨8937111131323737539393099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23832296350196633438381597 8937111131323737539393099)
            ·
              refine ⟨13405666696985606309089649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8937111131323737539393099 13405666696985606309089649)
              ·
                refine ⟨10054250022739204731817237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13405666696985606309089649 10054250022739204731817237)
                ·
                  refine ⟨471292969815900221803933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10054250022739204731817237 471292969815900221803933)
                  ·
                    rfl

theorem cell22_4130279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 6].length) (baseStart_4130279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130279 prefixEnd_4130279 := by exact prefixLift 4130279
  have htrace : WordTrace (prefixWord ++ tailWord_4130279) baseStart_4130279 baseEnd_4130279 := by
    simpa [prefixWord, tailWord_4130279, baseEnd_4130279] using wordTrace_append hprefix tailTrace_4130279
  have hstable : (prefixWord ++ tailWord_4130279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130279).length < 2 ^ (prefixWord ++ tailWord_4130279).sum := by decide
  have hdescent : baseEnd_4130279 < baseStart_4130279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130296 : List Nat := [2, 1, 2, 1, 1, 6, 2, 3, 4]
def baseStart_4130296 : Nat := 118140960795 + 4130296 * 2 ^ 59
def prefixEnd_4130296 : Nat := 4983230072969 + 3 ^ 40 * 4130296 * 2
def baseEnd_4130296 : Nat := 471294909631706095912249

theorem tailTrace_4130296 : CollatzResearch.WordTrace tailWord_4130296 prefixEnd_4130296 471294909631706095912249 := by
  unfold tailWord_4130296
  simp only [CollatzResearch.WordTrace]
  refine ⟨75322135522325232621137371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100429514029766976828183161 75322135522325232621137371)
  ·
    refine ⟨112983203283487848931706057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75322135522325232621137371 112983203283487848931706057)
    ·
      refine ⟨84737402462615886698779543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112983203283487848931706057 84737402462615886698779543)
      ·
        refine ⟨127106103693923830048169315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84737402462615886698779543 127106103693923830048169315)
        ·
          refine ⟨190659155540885745072253973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127106103693923830048169315 190659155540885745072253973)
          ·
            refine ⟨8937147915979019300261905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 190659155540885745072253973 8937147915979019300261905)
            ·
              refine ⟨6702860936984264475196429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8937147915979019300261905 6702860936984264475196429)
              ·
                refine ⟨2513572851369099178198661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6702860936984264475196429 2513572851369099178198661)
                ·
                  refine ⟨471294909631706095912249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2513572851369099178198661 471294909631706095912249)
                  ·
                    rfl

theorem cell22_4130296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 4].length) (baseStart_4130296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130296 prefixEnd_4130296 := by exact prefixLift 4130296
  have htrace : WordTrace (prefixWord ++ tailWord_4130296) baseStart_4130296 baseEnd_4130296 := by
    simpa [prefixWord, tailWord_4130296, baseEnd_4130296] using wordTrace_append hprefix tailTrace_4130296
  have hstable : (prefixWord ++ tailWord_4130296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130296).length < 2 ^ (prefixWord ++ tailWord_4130296).sum := by decide
  have hdescent : baseEnd_4130296 < baseStart_4130296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130311 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 4, 3]
def baseStart_4130311 : Nat := 118140960795 + 4130311 * 2 ^ 59
def prefixEnd_4130311 : Nat := 4983230072969 + 3 ^ 40 * 4130311 * 2
def baseEnd_4130311 : Nat := 1413889863701663248611701

theorem tailTrace_4130311 : CollatzResearch.WordTrace tailWord_4130311 prefixEnd_4130311 1413889863701663248611701 := by
  unfold tailWord_4130311
  simp only [CollatzResearch.WordTrace]
  refine ⟨150644818139596122804070787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100429878759730748536047191 150644818139596122804070787)
  ·
    refine ⟨225967227209394184206106181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150644818139596122804070787 225967227209394184206106181)
    ·
      refine ⟨42368855101761409538644909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225967227209394184206106181 42368855101761409538644909)
      ·
        refine ⟨15888320663160528576991841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42368855101761409538644909 15888320663160528576991841)
        ·
          refine ⟨11916240497370396432743881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15888320663160528576991841 11916240497370396432743881)
          ·
            refine ⟨8937180373027797324557911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11916240497370396432743881 8937180373027797324557911)
            ·
              refine ⟨13405770559541695986836867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8937180373027797324557911 13405770559541695986836867)
              ·
                refine ⟨20108655839312543980255301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13405770559541695986836867 20108655839312543980255301)
                ·
                  refine ⟨3770372969871101996297869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20108655839312543980255301 3770372969871101996297869)
                  ·
                    refine ⟨1413889863701663248611701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3770372969871101996297869 1413889863701663248611701)
                    ·
                      rfl

theorem cell22_4130311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_4130311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130311 prefixEnd_4130311 := by exact prefixLift 4130311
  have htrace : WordTrace (prefixWord ++ tailWord_4130311) baseStart_4130311 baseEnd_4130311 := by
    simpa [prefixWord, tailWord_4130311, baseEnd_4130311] using wordTrace_append hprefix tailTrace_4130311
  have hstable : (prefixWord ++ tailWord_4130311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130311).length < 2 ^ (prefixWord ++ tailWord_4130311).sum := by decide
  have hdescent : baseEnd_4130311 < baseStart_4130311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130328 : List Nat := [2, 1, 2, 3, 5, 1, 1, 1, 1, 5]
def baseStart_4130328 : Nat := 118140960795 + 4130328 * 2 ^ 59
def prefixEnd_4130328 : Nat := 4983230072969 + 3 ^ 40 * 4130328 * 2
def baseEnd_4130328 : Nat := 1413895683149080870936649

theorem tailTrace_4130328 : CollatzResearch.WordTrace tailWord_4130328 prefixEnd_4130328 1413895683149080870936649 := by
  unfold tailWord_4130328
  simp only [CollatzResearch.WordTrace]
  refine ⟨75322719090267267353719819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100430292120356356471626425 75322719090267267353719819)
  ·
    refine ⟨112984078635400901030579729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75322719090267267353719819 112984078635400901030579729)
    ·
      refine ⟨84738058976550675772934797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112984078635400901030579729 84738058976550675772934797)
      ·
        refine ⟨31776772116206503414850549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84738058976550675772934797 31776772116206503414850549)
        ·
          refine ⟨2979072385894359695142239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31776772116206503414850549 2979072385894359695142239)
          ·
            refine ⟨4468608578841539542713359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2979072385894359695142239 4468608578841539542713359)
            ·
              refine ⟨6702912868262309314070039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4468608578841539542713359 6702912868262309314070039)
              ·
                refine ⟨10054369302393463971105059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6702912868262309314070039 10054369302393463971105059)
                ·
                  refine ⟨15081553953590195956657589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10054369302393463971105059 15081553953590195956657589)
                  ·
                    refine ⟨1413895683149080870936649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15081553953590195956657589 1413895683149080870936649)
                    ·
                      rfl

theorem cell22_4130328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 1, 5].length) (baseStart_4130328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130328 prefixEnd_4130328 := by exact prefixLift 4130328
  have htrace : WordTrace (prefixWord ++ tailWord_4130328) baseStart_4130328 baseEnd_4130328 := by
    simpa [prefixWord, tailWord_4130328, baseEnd_4130328] using wordTrace_append hprefix tailTrace_4130328
  have hstable : (prefixWord ++ tailWord_4130328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130328).length < 2 ^ (prefixWord ++ tailWord_4130328).sum := by decide
  have hdescent : baseEnd_4130328 < baseStart_4130328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130358 : List Nat := [5, 1, 2, 1, 4, 1, 8]
def baseStart_4130358 : Nat := 118140960795 + 4130358 * 2 ^ 59
def prefixEnd_4130358 : Nat := 4983230072969 + 3 ^ 40 * 4130358 * 2
def baseEnd_4130358 : Nat := 52366887139339658988391

theorem tailTrace_4130358 : CollatzResearch.WordTrace tailWord_4130358 prefixEnd_4130358 52366887139339658988391 := by
  unfold tailWord_4130358
  simp only [CollatzResearch.WordTrace]
  refine ⟨9415408273151615614439483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100431021580283899887354485 9415408273151615614439483)
  ·
    refine ⟨14123112409727423421659225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9415408273151615614439483 14123112409727423421659225)
    ·
      refine ⟨10592334307295567566244419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14123112409727423421659225 10592334307295567566244419)
      ·
        refine ⟨15888501460943351349366629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10592334307295567566244419 15888501460943351349366629)
        ·
          refine ⟨2979094023926878378006243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15888501460943351349366629 2979094023926878378006243)
          ·
            refine ⟨4468641035890317567009365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2979094023926878378006243 4468641035890317567009365)
            ·
              refine ⟨52366887139339658988391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4468641035890317567009365 52366887139339658988391)
              ·
                rfl

theorem cell22_4130358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 8].length) (baseStart_4130358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130358 prefixEnd_4130358 := by exact prefixLift 4130358
  have htrace : WordTrace (prefixWord ++ tailWord_4130358) baseStart_4130358 baseEnd_4130358 := by
    simpa [prefixWord, tailWord_4130358, baseEnd_4130358] using wordTrace_append hprefix tailTrace_4130358
  have hstable : (prefixWord ++ tailWord_4130358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130358).length < 2 ^ (prefixWord ++ tailWord_4130358).sum := by decide
  have hdescent : baseEnd_4130358 < baseStart_4130358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130369 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 7]
def baseStart_4130369 : Nat := 118140960795 + 4130369 * 2 ^ 59
def prefixEnd_4130369 : Nat := 4983230072969 + 3 ^ 40 * 4130369 * 2
def baseEnd_4130369 : Nat := 471303239428990143553841

theorem tailTrace_4130369 : CollatzResearch.WordTrace tailWord_4130369 prefixEnd_4130369 471303239428990143553841 := by
  unfold tailWord_4130369
  simp only [CollatzResearch.WordTrace]
  refine ⟨150646933573385998709682161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100431289048923999139788107 150646933573385998709682161)
  ·
    refine ⟨112985200180039499032261621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150646933573385998709682161 112985200180039499032261621)
    ·
      refine ⟨10592362516878703034274527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112985200180039499032261621 10592362516878703034274527)
      ·
        refine ⟨15888543775318054551411791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10592362516878703034274527 15888543775318054551411791)
        ·
          refine ⟨23832815662977081827117687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15888543775318054551411791 23832815662977081827117687)
          ·
            refine ⟨35749223494465622740676531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23832815662977081827117687 35749223494465622740676531)
            ·
              refine ⟨53623835241698434111014797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35749223494465622740676531 53623835241698434111014797)
              ·
                refine ⟨20108938215636912791630549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53623835241698434111014797 20108938215636912791630549)
                ·
                  refine ⟨471303239428990143553841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20108938215636912791630549 471303239428990143553841)
                  ·
                    rfl

theorem cell22_4130369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 7].length) (baseStart_4130369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130369 prefixEnd_4130369 := by exact prefixLift 4130369
  have htrace : WordTrace (prefixWord ++ tailWord_4130369) baseStart_4130369 baseEnd_4130369 := by
    simpa [prefixWord, tailWord_4130369, baseEnd_4130369] using wordTrace_append hprefix tailTrace_4130369
  have hstable : (prefixWord ++ tailWord_4130369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130369).length < 2 ^ (prefixWord ++ tailWord_4130369).sum := by decide
  have hdescent : baseEnd_4130369 < baseStart_4130369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130386 : List Nat := [3, 2, 2, 1, 2, 3, 1, 3, 5]
def baseStart_4130386 : Nat := 118140960795 + 4130386 * 2 ^ 59
def prefixEnd_4130386 : Nat := 4983230072969 + 3 ^ 40 * 4130386 * 2
def baseEnd_4130386 : Nat := 471305179244796017662157

theorem tailTrace_4130386 : CollatzResearch.WordTrace tailWord_4130386 prefixEnd_4130386 471305179244796017662157 := by
  unfold tailWord_4130386
  simp only [CollatzResearch.WordTrace]
  refine ⟨37661888403581102653262753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100431702409549607075367341 37661888403581102653262753)
  ·
    refine ⟨28246416302685826989947065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37661888403581102653262753 28246416302685826989947065)
    ·
      refine ⟨21184812227014370242460299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28246416302685826989947065 21184812227014370242460299)
      ·
        refine ⟨31777218340521555363690449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21184812227014370242460299 31777218340521555363690449)
        ·
          refine ⟨23832913755391166522767837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31777218340521555363690449 23832913755391166522767837)
          ·
            refine ⟨8937342658271687446037939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23832913755391166522767837 8937342658271687446037939)
            ·
              refine ⟨13406013987407531169056909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8937342658271687446037939 13406013987407531169056909)
              ·
                refine ⟨5027255245277824188396341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13406013987407531169056909 5027255245277824188396341)
                ·
                  refine ⟨471305179244796017662157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5027255245277824188396341 471305179244796017662157)
                  ·
                    rfl

theorem cell22_4130386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_4130386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130386 prefixEnd_4130386 := by exact prefixLift 4130386
  have htrace : WordTrace (prefixWord ++ tailWord_4130386) baseStart_4130386 baseEnd_4130386 := by
    simpa [prefixWord, tailWord_4130386, baseEnd_4130386] using wordTrace_append hprefix tailTrace_4130386
  have hstable : (prefixWord ++ tailWord_4130386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130386).length < 2 ^ (prefixWord ++ tailWord_4130386).sum := by decide
  have hdescent : baseEnd_4130386 < baseStart_4130386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130444 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 1, 6]
def baseStart_4130444 : Nat := 118140960795 + 4130444 * 2 ^ 59
def prefixEnd_4130444 : Nat := 4983230072969 + 3 ^ 40 * 4130444 * 2
def baseEnd_4130444 : Nat := 1413935392319695235036293

theorem tailTrace_4130444 : CollatzResearch.WordTrace tailWord_4130444 prefixEnd_4130444 1413935392319695235036293 := by
  unfold tailWord_4130444
  simp only [CollatzResearch.WordTrace]
  refine ⟨75324834524057143259331193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100433112698742857679108257 75324834524057143259331193)
  ·
    refine ⟨56493625893042857444498395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75324834524057143259331193 56493625893042857444498395)
    ·
      refine ⟨84740438839564286166747593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56493625893042857444498395 84740438839564286166747593)
      ·
        refine ⟨63555329129673214625060695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84740438839564286166747593 63555329129673214625060695)
        ·
          refine ⟨95332993694509821937591043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63555329129673214625060695 95332993694509821937591043)
          ·
            refine ⟨142999490541764732906386565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95332993694509821937591043 142999490541764732906386565)
            ·
              refine ⟨26812404476580887419947481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142999490541764732906386565 26812404476580887419947481)
              ·
                refine ⟨20109303357435665564960611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26812404476580887419947481 20109303357435665564960611)
                ·
                  refine ⟨30163955036153498347440917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20109303357435665564960611 30163955036153498347440917)
                  ·
                    refine ⟨1413935392319695235036293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30163955036153498347440917 1413935392319695235036293)
                    ·
                      rfl

theorem cell22_4130444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_4130444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130444 prefixEnd_4130444 := by exact prefixLift 4130444
  have htrace : WordTrace (prefixWord ++ tailWord_4130444) baseStart_4130444 baseEnd_4130444 := by
    simpa [prefixWord, tailWord_4130444, baseEnd_4130444] using wordTrace_append hprefix tailTrace_4130444
  have hstable : (prefixWord ++ tailWord_4130444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130444).length < 2 ^ (prefixWord ++ tailWord_4130444).sum := by decide
  have hdescent : baseEnd_4130444 < baseStart_4130444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130446 : List Nat := [4, 1, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_4130446 : Nat := 118140960795 + 4130446 * 2 ^ 59
def prefixEnd_4130446 : Nat := 4983230072969 + 3 ^ 40 * 4130446 * 2
def baseEnd_4130446 : Nat := 1413936076960567896486287

theorem tailTrace_4130446 : CollatzResearch.WordTrace tailWord_4130446 prefixEnd_4130446 1413936076960567896486287 := by
  unfold tailWord_4130446
  simp only [CollatzResearch.WordTrace]
  refine ⟨18831217749263380107529399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100433161329404693906823461 18831217749263380107529399)
  ·
    refine ⟨28246826623895070161294099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18831217749263380107529399 28246826623895070161294099)
    ·
      refine ⟨42370239935842605241941149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28246826623895070161294099 42370239935842605241941149)
      ·
        refine ⟨15888839975940976965727931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42370239935842605241941149 15888839975940976965727931)
        ·
          refine ⟨23833259963911465448591897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15888839975940976965727931 23833259963911465448591897)
          ·
            refine ⟨17874944972933599086443923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23833259963911465448591897 17874944972933599086443923)
            ·
              refine ⟨26812417459400398629665885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17874944972933599086443923 26812417459400398629665885)
              ·
                refine ⟨10054656547275149486124707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26812417459400398629665885 10054656547275149486124707)
                ·
                  refine ⟨15081984820912724229187061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10054656547275149486124707 15081984820912724229187061)
                  ·
                    refine ⟨1413936076960567896486287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15081984820912724229187061 1413936076960567896486287)
                    ·
                      rfl

theorem cell22_4130446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_4130446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130446 prefixEnd_4130446 := by exact prefixLift 4130446
  have htrace : WordTrace (prefixWord ++ tailWord_4130446) baseStart_4130446 baseEnd_4130446 := by
    simpa [prefixWord, tailWord_4130446, baseEnd_4130446] using wordTrace_append hprefix tailTrace_4130446
  have hstable : (prefixWord ++ tailWord_4130446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130446).length < 2 ^ (prefixWord ++ tailWord_4130446).sum := by decide
  have hdescent : baseEnd_4130446 < baseStart_4130446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130489 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 1, 8]
def baseStart_4130489 : Nat := 118140960795 + 4130489 * 2 ^ 59
def prefixEnd_4130489 : Nat := 4983230072969 + 3 ^ 40 * 4130489 * 2
def baseEnd_4130489 : Nat := 1413950796739330117661155

theorem tailTrace_4130489 : CollatzResearch.WordTrace tailWord_4130489 prefixEnd_4130489 1413950796739330117661155 := by
  unfold tailWord_4130489
  simp only [CollatzResearch.WordTrace]
  refine ⟨150651310332951259204050521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100434206888634172802700347 150651310332951259204050521)
  ·
    refine ⟨112988482749713444403037891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150651310332951259204050521 112988482749713444403037891)
    ·
      refine ⟨169482724124570166604556837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112988482749713444403037891 169482724124570166604556837)
      ·
        refine ⟨31778010773356906238354407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169482724124570166604556837 31778010773356906238354407)
        ·
          refine ⟨47667016160035359357531611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31778010773356906238354407 47667016160035359357531611)
          ·
            refine ⟨71500524240053039036297417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47667016160035359357531611 71500524240053039036297417)
            ·
              refine ⟨53625393180039779277223063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71500524240053039036297417 53625393180039779277223063)
              ·
                refine ⟨80438089770059668915834595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53625393180039779277223063 80438089770059668915834595)
                ·
                  refine ⟨120657134655089503373751893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80438089770059668915834595 120657134655089503373751893)
                  ·
                    refine ⟨1413950796739330117661155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120657134655089503373751893 1413950796739330117661155)
                    ·
                      rfl

theorem cell22_4130489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_4130489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130489 prefixEnd_4130489 := by exact prefixLift 4130489
  have htrace : WordTrace (prefixWord ++ tailWord_4130489) baseStart_4130489 baseEnd_4130489 := by
    simpa [prefixWord, tailWord_4130489, baseEnd_4130489] using wordTrace_append hprefix tailTrace_4130489
  have hstable : (prefixWord ++ tailWord_4130489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130489).length < 2 ^ (prefixWord ++ tailWord_4130489).sum := by decide
  have hdescent : baseEnd_4130489 < baseStart_4130489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130542 : List Nat := [4, 1, 2, 1, 1, 2, 5, 2, 1, 3]
def baseStart_4130542 : Nat := 118140960795 + 4130542 * 2 ^ 59
def prefixEnd_4130542 : Nat := 4983230072969 + 3 ^ 40 * 4130542 * 2
def baseEnd_4130542 : Nat := 1413968939722455646085993

theorem tailTrace_4130542 : CollatzResearch.WordTrace tailWord_4130542 prefixEnd_4130542 1413968939722455646085993 := by
  unfold tailWord_4130542
  simp only [CollatzResearch.WordTrace]
  refine ⟨18831655425219906156966235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100435495601172832837153253 18831655425219906156966235)
  ·
    refine ⟨28247483137829859235449353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18831655425219906156966235 28247483137829859235449353)
    ·
      refine ⟨21185612353372394426587015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28247483137829859235449353 21185612353372394426587015)
      ·
        refine ⟨31778418530058591639880523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21185612353372394426587015 31778418530058591639880523)
        ·
          refine ⟨47667627795087887459820785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31778418530058591639880523 47667627795087887459820785)
          ·
            refine ⟨35750720846315915594865589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47667627795087887459820785 35750720846315915594865589)
            ·
              refine ⟨3351630079342117087018649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35750720846315915594865589 3351630079342117087018649)
              ·
                refine ⟨2513722559506587815263987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3351630079342117087018649 2513722559506587815263987)
                ·
                  refine ⟨3770583839259881722895981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2513722559506587815263987 3770583839259881722895981)
                  ·
                    refine ⟨1413968939722455646085993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3770583839259881722895981 1413968939722455646085993)
                    ·
                      rfl

theorem cell22_4130542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_4130542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130542 prefixEnd_4130542 := by exact prefixLift 4130542
  have htrace : WordTrace (prefixWord ++ tailWord_4130542) baseStart_4130542 baseEnd_4130542 := by
    simpa [prefixWord, tailWord_4130542, baseEnd_4130542] using wordTrace_append hprefix tailTrace_4130542
  have hstable : (prefixWord ++ tailWord_4130542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130542).length < 2 ^ (prefixWord ++ tailWord_4130542).sum := by decide
  have hdescent : baseEnd_4130542 < baseStart_4130542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130581 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 3, 5]
def baseStart_4130581 : Nat := 118140960795 + 4130581 * 2 ^ 59
def prefixEnd_4130581 : Nat := 4983230072969 + 3 ^ 40 * 4130581 * 2
def baseEnd_4130581 : Nat := 1413982290219472544360873

theorem tailTrace_4130581 : CollatzResearch.WordTrace tailWord_4130581 prefixEnd_4130581 1413982290219472544360873 := by
  unfold tailWord_4130581
  simp only [CollatzResearch.WordTrace]
  refine ⟨150654665848617958916399597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100436443899078639277599731 150654665848617958916399597)
  ·
    refine ⟨56495499693231734593649849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150654665848617958916399597 56495499693231734593649849)
    ·
      refine ⟨42371624769923800945237387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56495499693231734593649849 42371624769923800945237387)
      ·
        refine ⟨63557437154885701417856081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42371624769923800945237387 63557437154885701417856081)
        ·
          refine ⟨47668077866164276063392061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63557437154885701417856081 47668077866164276063392061)
          ·
            refine ⟨17875529199811603523772023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47668077866164276063392061 17875529199811603523772023)
            ·
              refine ⟨26813293799717405285658035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17875529199811603523772023 26813293799717405285658035)
              ·
                refine ⟨40219940699576107928487053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26813293799717405285658035 40219940699576107928487053)
                ·
                  refine ⟨15082477762341040473182645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40219940699576107928487053 15082477762341040473182645)
                  ·
                    refine ⟨1413982290219472544360873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15082477762341040473182645 1413982290219472544360873)
                    ·
                      rfl

theorem cell22_4130581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_4130581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130581 prefixEnd_4130581 := by exact prefixLift 4130581
  have htrace : WordTrace (prefixWord ++ tailWord_4130581) baseStart_4130581 baseEnd_4130581 := by
    simpa [prefixWord, tailWord_4130581, baseEnd_4130581] using wordTrace_append hprefix tailTrace_4130581
  have hstable : (prefixWord ++ tailWord_4130581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130581).length < 2 ^ (prefixWord ++ tailWord_4130581).sum := by decide
  have hdescent : baseEnd_4130581 < baseStart_4130581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130600 : List Nat := [2, 1, 5, 1, 1, 3, 1, 4, 4]
def baseStart_4130600 : Nat := 118140960795 + 4130600 * 2 ^ 59
def prefixEnd_4130600 : Nat := 4983230072969 + 3 ^ 40 * 4130600 * 2
def baseEnd_4130600 : Nat := 471329598102587609378605

theorem tailTrace_4130600 : CollatzResearch.WordTrace tailWord_4130600 prefixEnd_4130600 471329598102587609378605 := by
  unfold tailWord_4130600
  simp only [CollatzResearch.WordTrace]
  refine ⟨75327679417774562580670627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100436905890366083440894169 75327679417774562580670627)
  ·
    refine ⟨112991519126661843871005941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75327679417774562580670627 112991519126661843871005941)
    ·
      refine ⟨10592954918124547862906807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112991519126661843871005941 10592954918124547862906807)
      ·
        refine ⟨15889432377186821794360211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10592954918124547862906807 15889432377186821794360211)
        ·
          refine ⟨23834148565780232691540317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15889432377186821794360211 23834148565780232691540317)
          ·
            refine ⟨8937805712167587259327619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23834148565780232691540317 8937805712167587259327619)
            ·
              refine ⟨13406708568251380888991429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8937805712167587259327619 13406708568251380888991429)
              ·
                refine ⟨2513757856547133916685893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13406708568251380888991429 2513757856547133916685893)
                ·
                  refine ⟨471329598102587609378605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2513757856547133916685893 471329598102587609378605)
                  ·
                    rfl

theorem cell22_4130600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 4].length) (baseStart_4130600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130600 prefixEnd_4130600 := by exact prefixLift 4130600
  have htrace : WordTrace (prefixWord ++ tailWord_4130600) baseStart_4130600 baseEnd_4130600 := by
    simpa [prefixWord, tailWord_4130600, baseEnd_4130600] using wordTrace_append hprefix tailTrace_4130600
  have hstable : (prefixWord ++ tailWord_4130600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130600).length < 2 ^ (prefixWord ++ tailWord_4130600).sum := by decide
  have hdescent : baseEnd_4130600 < baseStart_4130600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130737 : List Nat := [1, 2, 2, 4, 2, 3, 1, 2, 1, 4]
def baseStart_4130737 : Nat := 118140960795 + 4130737 * 2 ^ 59
def prefixEnd_4130737 : Nat := 4983230072969 + 3 ^ 40 * 4130737 * 2
def baseEnd_4130737 : Nat := 1414035692207540137460395

theorem tailTrace_4130737 : CollatzResearch.WordTrace tailWord_4130737 prefixEnd_4130737 1414035692207540137460395 := by
  unfold tailWord_4130737
  simp only [CollatzResearch.WordTrace]
  refine ⟨150660355636052797559078465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100440237090701865039385643 150660355636052797559078465)
  ·
    refine ⟨112995266727039598169308849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150660355636052797559078465 112995266727039598169308849)
    ·
      refine ⟨84746450045279698626981637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112995266727039598169308849 84746450045279698626981637)
      ·
        refine ⟨15889959383489943492559057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84746450045279698626981637 15889959383489943492559057)
        ·
          refine ⟨11917469537617457619419293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15889959383489943492559057 11917469537617457619419293)
          ·
            refine ⟨4469051076606546607282235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11917469537617457619419293 4469051076606546607282235)
            ·
              refine ⟨6703576614909819910923353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4469051076606546607282235 6703576614909819910923353)
              ·
                refine ⟨5027682461182364933192515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6703576614909819910923353 5027682461182364933192515)
                ·
                  refine ⟨7541523691773547399788773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5027682461182364933192515 7541523691773547399788773)
                  ·
                    refine ⟨1414035692207540137460395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7541523691773547399788773 1414035692207540137460395)
                    ·
                      rfl

theorem cell22_4130737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_4130737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130737 prefixEnd_4130737 := by exact prefixLift 4130737
  have htrace : WordTrace (prefixWord ++ tailWord_4130737) baseStart_4130737 baseEnd_4130737 := by
    simpa [prefixWord, tailWord_4130737, baseEnd_4130737] using wordTrace_append hprefix tailTrace_4130737
  have hstable : (prefixWord ++ tailWord_4130737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130737).length < 2 ^ (prefixWord ++ tailWord_4130737).sum := by decide
  have hdescent : baseEnd_4130737 < baseStart_4130737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130750 : List Nat := [4, 2, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_4130750 : Nat := 118140960795 + 4130750 * 2 ^ 59
def prefixEnd_4130750 : Nat := 4983230072969 + 3 ^ 40 * 4130750 * 2
def baseEnd_4130750 : Nat := 1414040142373212436885355

theorem tailTrace_4130750 : CollatzResearch.WordTrace tailWord_4130750 prefixEnd_4130750 1414040142373212436885355 := by
  unfold tailWord_4130750
  simp only [CollatzResearch.WordTrace]
  refine ⟨18832603723125712597412713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100440553190003800519534469 18832603723125712597412713)
  ·
    refine ⟨14124452792344284448059535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18832603723125712597412713 14124452792344284448059535)
    ·
      refine ⟨21186679188516426672089303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14124452792344284448059535 21186679188516426672089303)
      ·
        refine ⟨31780018782774640008133955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21186679188516426672089303 31780018782774640008133955)
        ·
          refine ⟨47670028174161960012200933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31780018782774640008133955 47670028174161960012200933)
          ·
            refine ⟨8938130282655367502287675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47670028174161960012200933 8938130282655367502287675)
            ·
              refine ⟨13407195423983051253431513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8938130282655367502287675 13407195423983051253431513)
              ·
                refine ⟨10055396567987288440073635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13407195423983051253431513 10055396567987288440073635)
                ·
                  refine ⟨15083094851980932660110453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10055396567987288440073635 15083094851980932660110453)
                  ·
                    refine ⟨1414040142373212436885355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15083094851980932660110453 1414040142373212436885355)
                    ·
                      rfl

theorem cell22_4130750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_4130750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130750 prefixEnd_4130750 := by exact prefixLift 4130750
  have htrace : WordTrace (prefixWord ++ tailWord_4130750) baseStart_4130750 baseEnd_4130750 := by
    simpa [prefixWord, tailWord_4130750, baseEnd_4130750] using wordTrace_append hprefix tailTrace_4130750
  have hstable : (prefixWord ++ tailWord_4130750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130750).length < 2 ^ (prefixWord ++ tailWord_4130750).sum := by decide
  have hdescent : baseEnd_4130750 < baseStart_4130750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130842 : List Nat := [3, 1, 1, 3, 1, 4, 3, 1, 5]
def baseStart_4130842 : Nat := 118140960795 + 4130842 * 2 ^ 59
def prefixEnd_4130842 : Nat := 4983230072969 + 3 ^ 40 * 4130842 * 2
def baseEnd_4130842 : Nat := 471357211951118287861691

theorem tailTrace_4130842 : CollatzResearch.WordTrace tailWord_4130842 prefixEnd_4130842 471357211951118287861691 := by
  unfold tailWord_4130842
  simp only [CollatzResearch.WordTrace]
  refine ⟨37666046325168100122912695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100442790200448266994433853 37666046325168100122912695)
  ·
    refine ⟨56499069487752150184369043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37666046325168100122912695 56499069487752150184369043)
    ·
      refine ⟨84748604231628225276553565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56499069487752150184369043 84748604231628225276553565)
      ·
        refine ⟨31780726586860584478707587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84748604231628225276553565 31780726586860584478707587)
        ·
          refine ⟨47671089880290876718061381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31780726586860584478707587 47671089880290876718061381)
          ·
            refine ⟨8938329352554539384636509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47671089880290876718061381 8938329352554539384636509)
            ·
              refine ⟨3351873507207952269238691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8938329352554539384636509 3351873507207952269238691)
              ·
                refine ⟨5027810260811928403858037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3351873507207952269238691 5027810260811928403858037)
                ·
                  refine ⟨471357211951118287861691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5027810260811928403858037 471357211951118287861691)
                  ·
                    rfl

theorem cell22_4130842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_4130842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130842 prefixEnd_4130842 := by exact prefixLift 4130842
  have htrace : WordTrace (prefixWord ++ tailWord_4130842) baseStart_4130842 baseEnd_4130842 := by
    simpa [prefixWord, tailWord_4130842, baseEnd_4130842] using wordTrace_append hprefix tailTrace_4130842
  have hstable : (prefixWord ++ tailWord_4130842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130842).length < 2 ^ (prefixWord ++ tailWord_4130842).sum := by decide
  have hdescent : baseEnd_4130842 < baseStart_4130842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130883 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 3, 6]
def baseStart_4130883 : Nat := 118140960795 + 4130883 * 2 ^ 59
def prefixEnd_4130883 : Nat := 4983230072969 + 3 ^ 40 * 4130883 * 2
def baseEnd_4130883 : Nat := 1414085670991244423309947

theorem tailTrace_4130883 : CollatzResearch.WordTrace tailWord_4130883 prefixEnd_4130883 1414085670991244423309947 := by
  unfold tailWord_4130883
  simp only [CollatzResearch.WordTrace]
  refine ⟨150665680693523864493893303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100443787129015909662595535 150665680693523864493893303)
  ·
    refine ⟨225998521040285796740839955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150665680693523864493893303 225998521040285796740839955)
    ·
      refine ⟨338997781560428695111259933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225998521040285796740839955 338997781560428695111259933)
      ·
        refine ⟨127124168085160760666722475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 338997781560428695111259933 127124168085160760666722475)
        ·
          refine ⟨190686252127741141000083713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127124168085160760666722475 190686252127741141000083713)
          ·
            refine ⟨143014689095805855750062785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190686252127741141000083713 143014689095805855750062785)
            ·
              refine ⟨107261016821854391812547089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143014689095805855750062785 107261016821854391812547089)
              ·
                refine ⟨80445762616390793859410317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107261016821854391812547089 80445762616390793859410317)
                ·
                  refine ⟨30167160981146547697278869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80445762616390793859410317 30167160981146547697278869)
                  ·
                    refine ⟨1414085670991244423309947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30167160981146547697278869 1414085670991244423309947)
                    ·
                      rfl

theorem cell22_4130883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 6].length) (baseStart_4130883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130883 prefixEnd_4130883 := by exact prefixLift 4130883
  have htrace : WordTrace (prefixWord ++ tailWord_4130883) baseStart_4130883 baseEnd_4130883 := by
    simpa [prefixWord, tailWord_4130883, baseEnd_4130883] using wordTrace_append hprefix tailTrace_4130883
  have hstable : (prefixWord ++ tailWord_4130883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130883).length < 2 ^ (prefixWord ++ tailWord_4130883).sum := by decide
  have hdescent : baseEnd_4130883 < baseStart_4130883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130900 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_4130900 : Nat := 118140960795 + 4130900 * 2 ^ 59
def prefixEnd_4130900 : Nat := 4983230072969 + 3 ^ 40 * 4130900 * 2
def baseEnd_4130900 : Nat := 1414091490438662045634895

theorem tailTrace_4130900 : CollatzResearch.WordTrace tailWord_4130900 prefixEnd_4130900 1414091490438662045634895 := by
  unfold tailWord_4130900
  simp only [CollatzResearch.WordTrace]
  refine ⟨75333150367231138198631077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100444200489641517598174769 75333150367231138198631077)
  ·
    refine ⟨14124965693855838412243327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75333150367231138198631077 14124965693855838412243327)
    ·
      refine ⟨21187448540783757618364991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14124965693855838412243327 21187448540783757618364991)
      ·
        refine ⟨31781172811175636427547487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21187448540783757618364991 31781172811175636427547487)
        ·
          refine ⟨47671759216763454641321231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31781172811175636427547487 47671759216763454641321231)
          ·
            refine ⟨71507638825145181961981847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47671759216763454641321231 71507638825145181961981847)
            ·
              refine ⟨107261458237717772942972771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71507638825145181961981847 107261458237717772942972771)
              ·
                refine ⟨160892187356576659414459157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107261458237717772942972771 160892187356576659414459157)
                ·
                  refine ⟨7541821282339530910052773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160892187356576659414459157 7541821282339530910052773)
                  ·
                    refine ⟨1414091490438662045634895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7541821282339530910052773 1414091490438662045634895)
                    ·
                      rfl

theorem cell22_4130900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_4130900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130900 prefixEnd_4130900 := by exact prefixLift 4130900
  have htrace : WordTrace (prefixWord ++ tailWord_4130900) baseStart_4130900 baseEnd_4130900 := by
    simpa [prefixWord, tailWord_4130900, baseEnd_4130900] using wordTrace_append hprefix tailTrace_4130900
  have hstable : (prefixWord ++ tailWord_4130900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130900).length < 2 ^ (prefixWord ++ tailWord_4130900).sum := by decide
  have hdescent : baseEnd_4130900 < baseStart_4130900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130917 : List Nat := [1, 3, 1, 3, 2, 3, 2, 1, 2, 4]
def baseStart_4130917 : Nat := 118140960795 + 4130917 * 2 ^ 59
def prefixEnd_4130917 : Nat := 4983230072969 + 3 ^ 40 * 4130917 * 2
def baseEnd_4130917 : Nat := 1414097309886079667959843

theorem tailTrace_4130917 : CollatzResearch.WordTrace tailWord_4130917 prefixEnd_4130917 1414097309886079667959843 := by
  unfold tailWord_4130917
  simp only [CollatzResearch.WordTrace]
  refine ⟨150666920775400688300631005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100444613850267125533754003 150666920775400688300631005)
  ·
    refine ⟨56500095290775258112736627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150666920775400688300631005 56500095290775258112736627)
    ·
      refine ⟨84750142936162887169104941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56500095290775258112736627 84750142936162887169104941)
      ·
        refine ⟨31781303601061082688414353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84750142936162887169104941 31781303601061082688414353)
        ·
          refine ⟨23835977700795812016310765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31781303601061082688414353 23835977700795812016310765)
          ·
            refine ⟨8938491637798429506116537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23835977700795812016310765 8938491637798429506116537)
            ·
              refine ⟨6703868728348822129587403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8938491637798429506116537 6703868728348822129587403)
              ·
                refine ⟨10055803092523233194381105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6703868728348822129587403 10055803092523233194381105)
                ·
                  refine ⟨7541852319392424895785829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10055803092523233194381105 7541852319392424895785829)
                  ·
                    refine ⟨1414097309886079667959843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7541852319392424895785829 1414097309886079667959843)
                    ·
                      rfl

theorem cell22_4130917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_4130917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130917 prefixEnd_4130917 := by exact prefixLift 4130917
  have htrace : WordTrace (prefixWord ++ tailWord_4130917) baseStart_4130917 baseEnd_4130917 := by
    simpa [prefixWord, tailWord_4130917, baseEnd_4130917] using wordTrace_append hprefix tailTrace_4130917
  have hstable : (prefixWord ++ tailWord_4130917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130917).length < 2 ^ (prefixWord ++ tailWord_4130917).sum := by decide
  have hdescent : baseEnd_4130917 < baseStart_4130917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4130960 : List Nat := [2, 1, 1, 1, 1, 1, 5, 5, 5]
def baseStart_4130960 : Nat := 118140960795 + 4130960 * 2 ^ 59
def prefixEnd_4130960 : Nat := 4983230072969 + 3 ^ 40 * 4130960 * 2
def baseEnd_4130960 : Nat := 471370676554947296378237

theorem tailTrace_4130960 : CollatzResearch.WordTrace tailWord_4130960 prefixEnd_4130960 471370676554947296378237 := by
  unfold tailWord_4130960
  simp only [CollatzResearch.WordTrace]
  refine ⟨75334244557122453322223167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100445659409496604429630889 75334244557122453322223167)
  ·
    refine ⟨113001366835683679983334751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75334244557122453322223167 113001366835683679983334751)
    ·
      refine ⟨169502050253525519975002127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113001366835683679983334751 169502050253525519975002127)
      ·
        refine ⟨254253075380288279962503191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169502050253525519975002127 254253075380288279962503191)
        ·
          refine ⟨381379613070432419943754787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254253075380288279962503191 381379613070432419943754787)
          ·
            refine ⟨572069419605648629915632181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381379613070432419943754787 572069419605648629915632181)
            ·
              refine ⟨53631508088029559054590517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 572069419605648629915632181 53631508088029559054590517)
              ·
                refine ⟨5027953883252771161367861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53631508088029559054590517 5027953883252771161367861)
                ·
                  refine ⟨471370676554947296378237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5027953883252771161367861 471370676554947296378237)
                  ·
                    rfl

theorem cell22_4130960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 5].length) (baseStart_4130960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4130960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4130960 prefixEnd_4130960 := by exact prefixLift 4130960
  have htrace : WordTrace (prefixWord ++ tailWord_4130960) baseStart_4130960 baseEnd_4130960 := by
    simpa [prefixWord, tailWord_4130960, baseEnd_4130960] using wordTrace_append hprefix tailTrace_4130960
  have hstable : (prefixWord ++ tailWord_4130960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4130960).length < 2 ^ (prefixWord ++ tailWord_4130960).sum := by decide
  have hdescent : baseEnd_4130960 < baseStart_4130960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4130960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131022 : List Nat := [4, 1, 1, 1, 4, 1, 2, 2, 6]
def baseStart_4131022 : Nat := 118140960795 + 4131022 * 2 ^ 59
def prefixEnd_4131022 : Nat := 4983230072969 + 3 ^ 40 * 4131022 * 2
def baseEnd_4131022 : Nat := 471377751177298131361507

theorem tailTrace_4131022 : CollatzResearch.WordTrace tailWord_4131022 prefixEnd_4131022 471377751177298131361507 := by
  unfold tailWord_4131022
  simp only [CollatzResearch.WordTrace]
  refine ⟨18833843805002536404150415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100447166960013527488802213 18833843805002536404150415)
  ·
    refine ⟨28250765707503804606225623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18833843805002536404150415 28250765707503804606225623)
    ·
      refine ⟨42376148561255706909338435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28250765707503804606225623 42376148561255706909338435)
      ·
        refine ⟨63564222841883560364007653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42376148561255706909338435 63564222841883560364007653)
        ·
          refine ⟨11918291782853167568251435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63564222841883560364007653 11918291782853167568251435)
          ·
            refine ⟨17877437674279751352377153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11918291782853167568251435 17877437674279751352377153)
            ·
              refine ⟨13408078255709813514282865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17877437674279751352377153 13408078255709813514282865)
              ·
                refine ⟨10056058691782360135712149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13408078255709813514282865 10056058691782360135712149)
                ·
                  refine ⟨471377751177298131361507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10056058691782360135712149 471377751177298131361507)
                  ·
                    rfl

theorem cell22_4131022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_4131022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131022 prefixEnd_4131022 := by exact prefixLift 4131022
  have htrace : WordTrace (prefixWord ++ tailWord_4131022) baseStart_4131022 baseEnd_4131022 := by
    simpa [prefixWord, tailWord_4131022, baseEnd_4131022] using wordTrace_append hprefix tailTrace_4131022
  have hstable : (prefixWord ++ tailWord_4131022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131022).length < 2 ^ (prefixWord ++ tailWord_4131022).sum := by decide
  have hdescent : baseEnd_4131022 < baseStart_4131022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131052 : List Nat := [2, 2, 1, 1, 2, 3, 3, 2, 2, 4]
def baseStart_4131052 : Nat := 118140960795 + 4131052 * 2 ^ 59
def prefixEnd_4131052 : Nat := 4983230072969 + 3 ^ 40 * 4131052 * 2
def baseEnd_4131052 : Nat := 1414143523144984315834429

theorem tailTrace_4131052 : CollatzResearch.WordTrace tailWord_4131052 prefixEnd_4131052 1414143523144984315834429 := by
  unfold tailWord_4131052
  simp only [CollatzResearch.WordTrace]
  refine ⟨75335922314955803178397705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100447896419941070904530273 75335922314955803178397705)
  ·
    refine ⟨56501941736216852383798279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75335922314955803178397705 56501941736216852383798279)
    ·
      refine ⟨84752912604325278575697419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56501941736216852383798279 84752912604325278575697419)
      ·
        refine ⟨127129368906487917863546129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84752912604325278575697419 127129368906487917863546129)
        ·
          refine ⟨95347026679865938397659597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127129368906487917863546129 95347026679865938397659597)
          ·
            refine ⟨35755135004949726899122349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95347026679865938397659597 35755135004949726899122349)
            ·
              refine ⟨13408175626856147587170881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35755135004949726899122349 13408175626856147587170881)
              ·
                refine ⟨10056131720142110690378161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13408175626856147587170881 10056131720142110690378161)
                ·
                  refine ⟨7542098790106583017783621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10056131720142110690378161 7542098790106583017783621)
                  ·
                    refine ⟨1414143523144984315834429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7542098790106583017783621 1414143523144984315834429)
                    ·
                      rfl

theorem cell22_4131052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_4131052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131052 prefixEnd_4131052 := by exact prefixLift 4131052
  have htrace : WordTrace (prefixWord ++ tailWord_4131052) baseStart_4131052 baseEnd_4131052 := by
    simpa [prefixWord, tailWord_4131052, baseEnd_4131052] using wordTrace_append hprefix tailTrace_4131052
  have hstable : (prefixWord ++ tailWord_4131052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131052).length < 2 ^ (prefixWord ++ tailWord_4131052).sum := by decide
  have hdescent : baseEnd_4131052 < baseStart_4131052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131054 : List Nat := [4, 1, 2, 1, 1, 1, 1, 6, 2, 3]
def baseStart_4131054 : Nat := 118140960795 + 4131054 * 2 ^ 59
def prefixEnd_4131054 : Nat := 4983230072969 + 3 ^ 40 * 4131054 * 2
def baseEnd_4131054 : Nat := 1414144207785856977284423

theorem tailTrace_4131054 : CollatzResearch.WordTrace tailWord_4131054 prefixEnd_4131054 1414144207785856977284423 := by
  unfold tailWord_4131054
  simp only [CollatzResearch.WordTrace]
  refine ⟨18833989696988045087296027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100447945050602907132245477 18833989696988045087296027)
  ·
    refine ⟨28250984545482067630944041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18833989696988045087296027 28250984545482067630944041)
    ·
      refine ⟨21188238409111550723208031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28250984545482067630944041 21188238409111550723208031)
      ·
        refine ⟨31782357613667326084812047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21188238409111550723208031 31782357613667326084812047)
        ·
          refine ⟨47673536420500989127218071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31782357613667326084812047 47673536420500989127218071)
          ·
            refine ⟨71510304630751483690827107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47673536420500989127218071 71510304630751483690827107)
            ·
              refine ⟨107265456946127225536240661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71510304630751483690827107 107265456946127225536240661)
              ·
                refine ⟨5028068294349713697011281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107265456946127225536240661 5028068294349713697011281)
                ·
                  refine ⟨3771051220762285272758461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5028068294349713697011281 3771051220762285272758461)
                  ·
                    refine ⟨1414144207785856977284423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3771051220762285272758461 1414144207785856977284423)
                    ·
                      rfl

theorem cell22_4131054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_4131054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131054 prefixEnd_4131054 := by exact prefixLift 4131054
  have htrace : WordTrace (prefixWord ++ tailWord_4131054) baseStart_4131054 baseEnd_4131054 := by
    simpa [prefixWord, tailWord_4131054, baseEnd_4131054] using wordTrace_append hprefix tailTrace_4131054
  have hstable : (prefixWord ++ tailWord_4131054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131054).length < 2 ^ (prefixWord ++ tailWord_4131054).sum := by decide
  have hdescent : baseEnd_4131054 < baseStart_4131054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131065 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 2, 7]
def baseStart_4131065 : Nat := 118140960795 + 4131065 * 2 ^ 59
def prefixEnd_4131065 : Nat := 4983230072969 + 3 ^ 40 * 4131065 * 2
def baseEnd_4131065 : Nat := 1414147973310656615259389

theorem tailTrace_4131065 : CollatzResearch.WordTrace tailWord_4131065 prefixEnd_4131065 1414147973310656615259389 := by
  unfold tailWord_4131065
  simp only [CollatzResearch.WordTrace]
  refine ⟨150672318778864509577018649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100448212519243006384679099 150672318778864509577018649)
  ·
    refine ⟨113004239084148382182763987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150672318778864509577018649 113004239084148382182763987)
    ·
      refine ⟨169506358626222573274145981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113004239084148382182763987 169506358626222573274145981)
      ·
        refine ⟨63564884484833464977804743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169506358626222573274145981 63564884484833464977804743)
        ·
          refine ⟨95347326727250197466707115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63564884484833464977804743 95347326727250197466707115)
          ·
            refine ⟨143020990090875296200060673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95347326727250197466707115 143020990090875296200060673)
            ·
              refine ⟨107265742568156472150045505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143020990090875296200060673 107265742568156472150045505)
              ·
                refine ⟨80449306926117354112534129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107265742568156472150045505 80449306926117354112534129)
                ·
                  refine ⟨60336980194588015584400597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80449306926117354112534129 60336980194588015584400597)
                  ·
                    refine ⟨1414147973310656615259389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60336980194588015584400597 1414147973310656615259389)
                    ·
                      rfl

theorem cell22_4131065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_4131065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131065 prefixEnd_4131065 := by exact prefixLift 4131065
  have htrace : WordTrace (prefixWord ++ tailWord_4131065) baseStart_4131065 baseEnd_4131065 := by
    simpa [prefixWord, tailWord_4131065, baseEnd_4131065] using wordTrace_append hprefix tailTrace_4131065
  have hstable : (prefixWord ++ tailWord_4131065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131065).length < 2 ^ (prefixWord ++ tailWord_4131065).sum := by decide
  have hdescent : baseEnd_4131065 < baseStart_4131065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131118 : List Nat := [4, 1, 3, 3, 2, 1, 1, 7]
def baseStart_4131118 : Nat := 118140960795 + 4131118 * 2 ^ 59
def prefixEnd_4131118 : Nat := 4983230072969 + 3 ^ 40 * 4131118 * 2
def baseEnd_4131118 : Nat := 157129568477086904853803

theorem tailTrace_4131118 : CollatzResearch.WordTrace tailWord_4131118 prefixEnd_4131118 157129568477086904853803 := by
  unfold tailWord_4131118
  simp only [CollatzResearch.WordTrace]
  refine ⟨18834281480959062453587251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100449501231781666419132005 18834281480959062453587251)
  ·
    refine ⟨28251422221438593680380877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18834281480959062453587251 28251422221438593680380877)
    ·
      refine ⟨10594283333039472630142829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28251422221438593680380877 10594283333039472630142829)
      ·
        refine ⟨3972856249889802236303561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10594283333039472630142829 3972856249889802236303561)
        ·
          refine ⟨2979642187417351677227671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3972856249889802236303561 2979642187417351677227671)
          ·
            refine ⟨4469463281126027515841507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2979642187417351677227671 4469463281126027515841507)
            ·
              refine ⟨6704194921689041273762261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4469463281126027515841507 6704194921689041273762261)
              ·
                refine ⟨157129568477086904853803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6704194921689041273762261 157129568477086904853803)
                ·
                  rfl

theorem cell22_4131118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_4131118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131118 prefixEnd_4131118 := by exact prefixLift 4131118
  have htrace : WordTrace (prefixWord ++ tailWord_4131118) baseStart_4131118 baseEnd_4131118 := by
    simpa [prefixWord, tailWord_4131118, baseEnd_4131118] using wordTrace_append hprefix tailTrace_4131118
  have hstable : (prefixWord ++ tailWord_4131118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131118).length < 2 ^ (prefixWord ++ tailWord_4131118).sum := by decide
  have hdescent : baseEnd_4131118 < baseStart_4131118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131129 : List Nat := [1, 2, 1, 6, 1, 1, 2, 3, 5]
def baseStart_4131129 : Nat := 118140960795 + 4131129 * 2 ^ 59
def prefixEnd_4131129 : Nat := 4983230072969 + 3 ^ 40 * 4131129 * 2
def baseEnd_4131129 : Nat := 471389960606193927219731

theorem tailTrace_4131129 : CollatzResearch.WordTrace tailWord_4131129 prefixEnd_4131129 471389960606193927219731 := by
  unfold tailWord_4131129
  simp only [CollatzResearch.WordTrace]
  refine ⟨150674653050632648507348441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100449768700421765671565627 150674653050632648507348441)
  ·
    refine ⟨113005989787974486380511331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150674653050632648507348441 113005989787974486380511331)
    ·
      refine ⟨169508984681961729570766997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113005989787974486380511331 169508984681961729570766997)
      ·
        refine ⟨7945733656966956073629703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 169508984681961729570766997 7945733656966956073629703)
        ·
          refine ⟨11918600485450434110444555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7945733656966956073629703 11918600485450434110444555)
          ·
            refine ⟨17877900728175651165666833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11918600485450434110444555 17877900728175651165666833)
            ·
              refine ⟨13408425546131738374250125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17877900728175651165666833 13408425546131738374250125)
              ·
                refine ⟨5028159579799401890343797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13408425546131738374250125 5028159579799401890343797)
                ·
                  refine ⟨471389960606193927219731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5028159579799401890343797 471389960606193927219731)
                  ·
                    rfl

theorem cell22_4131129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 5].length) (baseStart_4131129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131129 prefixEnd_4131129 := by exact prefixLift 4131129
  have htrace : WordTrace (prefixWord ++ tailWord_4131129) baseStart_4131129 baseEnd_4131129 := by
    simpa [prefixWord, tailWord_4131129, baseEnd_4131129] using wordTrace_append hprefix tailTrace_4131129
  have hstable : (prefixWord ++ tailWord_4131129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131129).length < 2 ^ (prefixWord ++ tailWord_4131129).sum := by decide
  have hdescent : baseEnd_4131129 < baseStart_4131129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131159 : List Nat := [1, 1, 3, 2, 3, 1, 3, 3, 1, 4]
def baseStart_4131159 : Nat := 118140960795 + 4131159 * 2 ^ 59
def prefixEnd_4131159 : Nat := 4983230072969 + 3 ^ 40 * 4131159 * 2
def baseEnd_4131159 : Nat := 1414180151431671703409101

theorem tailTrace_4131159 : CollatzResearch.WordTrace tailWord_4131159 prefixEnd_4131159 1414180151431671703409101 := by
  unfold tailWord_4131159
  simp only [CollatzResearch.WordTrace]
  refine ⟨150675747240523963630940531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100450498160349309087293687 150675747240523963630940531)
  ·
    refine ⟨226013620860785945446410797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150675747240523963630940531 226013620860785945446410797)
    ·
      refine ⟨84755107822794729542404049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226013620860785945446410797 84755107822794729542404049)
      ·
        refine ⟨63566330867096047156803037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84755107822794729542404049 63566330867096047156803037)
        ·
          refine ⟨23837374075161017683801139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63566330867096047156803037 23837374075161017683801139)
          ·
            refine ⟨35756061112741526525701709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23837374075161017683801139 35756061112741526525701709)
            ·
              refine ⟨13408522917278072447138141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35756061112741526525701709 13408522917278072447138141)
              ·
                refine ⟨5028196093979277167676803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13408522917278072447138141 5028196093979277167676803)
                ·
                  refine ⟨7542294140968915751515205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5028196093979277167676803 7542294140968915751515205)
                  ·
                    refine ⟨1414180151431671703409101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7542294140968915751515205 1414180151431671703409101)
                    ·
                      rfl

theorem cell22_4131159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_4131159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131159 prefixEnd_4131159 := by exact prefixLift 4131159
  have htrace : WordTrace (prefixWord ++ tailWord_4131159) baseStart_4131159 baseEnd_4131159 := by
    simpa [prefixWord, tailWord_4131159, baseEnd_4131159] using wordTrace_append hprefix tailTrace_4131159
  have hstable : (prefixWord ++ tailWord_4131159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131159).length < 2 ^ (prefixWord ++ tailWord_4131159).sum := by decide
  have hdescent : baseEnd_4131159 < baseStart_4131159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131187 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 4, 4]
def baseStart_4131187 : Nat := 118140960795 + 4131187 * 2 ^ 59
def prefixEnd_4131187 : Nat := 4983230072969 + 3 ^ 40 * 4131187 * 2
def baseEnd_4131187 : Nat := 1414189736403888963709015

theorem tailTrace_4131187 : CollatzResearch.WordTrace tailWord_4131187 prefixEnd_4131187 1414189736403888963709015 := by
  unfold tailWord_4131187
  simp only [CollatzResearch.WordTrace]
  refine ⟨150676768484422524412959815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100451178989615016275306543 150676768484422524412959815)
  ·
    refine ⟨226015152726633786619439723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150676768484422524412959815 226015152726633786619439723)
    ·
      refine ⟨339022729089950679929159585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226015152726633786619439723 339022729089950679929159585)
      ·
        refine ⟨254267046817463009946869689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339022729089950679929159585 254267046817463009946869689)
        ·
          refine ⟨190700285113097257460152267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254267046817463009946869689 190700285113097257460152267)
          ·
            refine ⟨286050427669645886190228401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190700285113097257460152267 286050427669645886190228401)
            ·
              refine ⟨214537820752234414642671301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286050427669645886190228401 214537820752234414642671301)
              ·
                refine ⟨40225841391043952745500869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214537820752234414642671301 40225841391043952745500869)
                ·
                  refine ⟨7542345260820741139781413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40225841391043952745500869 7542345260820741139781413)
                  ·
                    refine ⟨1414189736403888963709015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7542345260820741139781413 1414189736403888963709015)
                    ·
                      rfl

theorem cell22_4131187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 4].length) (baseStart_4131187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131187 prefixEnd_4131187 := by exact prefixLift 4131187
  have htrace : WordTrace (prefixWord ++ tailWord_4131187) baseStart_4131187 baseEnd_4131187 := by
    simpa [prefixWord, tailWord_4131187, baseEnd_4131187] using wordTrace_append hprefix tailTrace_4131187
  have hstable : (prefixWord ++ tailWord_4131187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131187).length < 2 ^ (prefixWord ++ tailWord_4131187).sum := by decide
  have hdescent : baseEnd_4131187 < baseStart_4131187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131204 : List Nat := [2, 3, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_4131204 : Nat := 118140960795 + 4131204 * 2 ^ 59
def prefixEnd_4131204 : Nat := 4983230072969 + 3 ^ 40 * 4131204 * 2
def baseEnd_4131204 : Nat := 1414195555851306586033963

theorem tailTrace_4131204 : CollatzResearch.WordTrace tailWord_4131204 prefixEnd_4131204 1414195555851306586033963 := by
  unfold tailWord_4131204
  simp only [CollatzResearch.WordTrace]
  refine ⟨75338694262680468158164333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100451592350240624210885777 75338694262680468158164333)
  ·
    refine ⟨28252010348505175559311625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75338694262680468158164333 28252010348505175559311625)
    ·
      refine ⟨21189007761378881669483719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28252010348505175559311625 21189007761378881669483719)
      ·
        refine ⟨31783511642068322504225579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21189007761378881669483719 31783511642068322504225579)
        ·
          refine ⟨47675267463102483756338369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31783511642068322504225579 47675267463102483756338369)
          ·
            refine ⟨35756450597326862817253777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47675267463102483756338369 35756450597326862817253777)
            ·
              refine ⟨26817337947995147112940333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35756450597326862817253777 26817337947995147112940333)
              ·
                refine ⟨10056501730498180167352625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26817337947995147112940333 10056501730498180167352625)
                ·
                  refine ⟨7542376297873635125514469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10056501730498180167352625 7542376297873635125514469)
                  ·
                    refine ⟨1414195555851306586033963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7542376297873635125514469 1414195555851306586033963)
                    ·
                      rfl

theorem cell22_4131204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_4131204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131204 prefixEnd_4131204 := by exact prefixLift 4131204
  have htrace : WordTrace (prefixWord ++ tailWord_4131204) baseStart_4131204 baseEnd_4131204 := by
    simpa [prefixWord, tailWord_4131204, baseEnd_4131204] using wordTrace_append hprefix tailTrace_4131204
  have hstable : (prefixWord ++ tailWord_4131204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131204).length < 2 ^ (prefixWord ++ tailWord_4131204).sum := by decide
  have hdescent : baseEnd_4131204 < baseStart_4131204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131240 : List Nat := [2, 1, 6, 1, 1, 1, 4, 1, 2, 3]
def baseStart_4131240 : Nat := 118140960795 + 4131240 * 2 ^ 59
def prefixEnd_4131240 : Nat := 4983230072969 + 3 ^ 40 * 4131240 * 2
def baseEnd_4131240 : Nat := 1414207879387014492133853

theorem tailTrace_4131240 : CollatzResearch.WordTrace tailWord_4131240 prefixEnd_4131240 1414207879387014492133853 := by
  unfold tailWord_4131240
  simp only [CollatzResearch.WordTrace]
  refine ⟨75339350776615257232319587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100452467702153676309759449 75339350776615257232319587)
  ·
    refine ⟨113009026164922885848479381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75339350776615257232319587 113009026164922885848479381)
    ·
      refine ⟨5297298101480760274147471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113009026164922885848479381 5297298101480760274147471)
      ·
        refine ⟨7945947152221140411221207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5297298101480760274147471 7945947152221140411221207)
        ·
          refine ⟨11918920728331710616831811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7945947152221140411221207 11918920728331710616831811)
          ·
            refine ⟨17878381092497565925247717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11918920728331710616831811 17878381092497565925247717)
            ·
              refine ⟨3352196454843293610983947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17878381092497565925247717 3352196454843293610983947)
              ·
                refine ⟨5028294682264940416475921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3352196454843293610983947 5028294682264940416475921)
                ·
                  refine ⟨3771221011698705312356941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5028294682264940416475921 3771221011698705312356941)
                  ·
                    refine ⟨1414207879387014492133853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3771221011698705312356941 1414207879387014492133853)
                    ·
                      rfl

theorem cell22_4131240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_4131240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131240 prefixEnd_4131240 := by exact prefixLift 4131240
  have htrace : WordTrace (prefixWord ++ tailWord_4131240) baseStart_4131240 baseEnd_4131240 := by
    simpa [prefixWord, tailWord_4131240, baseEnd_4131240] using wordTrace_append hprefix tailTrace_4131240
  have hstable : (prefixWord ++ tailWord_4131240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131240).length < 2 ^ (prefixWord ++ tailWord_4131240).sum := by decide
  have hdescent : baseEnd_4131240 < baseStart_4131240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131285 : List Nat := [1, 3, 2, 3, 1, 2, 4, 2, 1, 3]
def baseStart_4131285 : Nat := 118140960795 + 4131285 * 2 ^ 59
def prefixEnd_4131285 : Nat := 4983230072969 + 3 ^ 40 * 4131285 * 2
def baseEnd_4131285 : Nat := 1414223283806649374758715

theorem tailTrace_4131285 : CollatzResearch.WordTrace tailWord_4131285 prefixEnd_4131285 1414223283806649374758715 := by
  unfold tailWord_4131285
  simp only [CollatzResearch.WordTrace]
  refine ⟨150680342838067487150027309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100453561892044991433351539 150680342838067487150027309)
  ·
    refine ⟨56505128564275307681260241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150680342838067487150027309 56505128564275307681260241)
    ·
      refine ⟨42378846423206480760945181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56505128564275307681260241 42378846423206480760945181)
      ·
        refine ⟨15892067408702430285354443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42378846423206480760945181 15892067408702430285354443)
        ·
          refine ⟨23838101113053645428031665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15892067408702430285354443 23838101113053645428031665)
          ·
            refine ⟨17878575834790234071023749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23838101113053645428031665 17878575834790234071023749)
            ·
              refine ⟨3352232969023168888316953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17878575834790234071023749 3352232969023168888316953)
              ·
                refine ⟨2514174726767376666237715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3352232969023168888316953 2514174726767376666237715)
                ·
                  refine ⟨3771262090151064999356573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2514174726767376666237715 3771262090151064999356573)
                  ·
                    refine ⟨1414223283806649374758715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3771262090151064999356573 1414223283806649374758715)
                    ·
                      rfl

theorem cell22_4131285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_4131285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131285 prefixEnd_4131285 := by exact prefixLift 4131285
  have htrace : WordTrace (prefixWord ++ tailWord_4131285) baseStart_4131285 baseEnd_4131285 := by
    simpa [prefixWord, tailWord_4131285, baseEnd_4131285] using wordTrace_append hprefix tailTrace_4131285
  have hstable : (prefixWord ++ tailWord_4131285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131285).length < 2 ^ (prefixWord ++ tailWord_4131285).sum := by decide
  have hdescent : baseEnd_4131285 < baseStart_4131285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131390 : List Nat := [4, 2, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_4131390 : Nat := 118140960795 + 4131390 * 2 ^ 59
def prefixEnd_4131390 : Nat := 4983230072969 + 3 ^ 40 * 4131390 * 2
def baseEnd_4131390 : Nat := 1414259227452464100883393

theorem tailTrace_4131390 : CollatzResearch.WordTrace tailWord_4131390 prefixEnd_4131390 1414259227452464100883393 := by
  unfold tailWord_4131390
  simp only [CollatzResearch.WordTrace]
  refine ⟨18835521562835886260324953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100456115001791393388399749 18835521562835886260324953)
  ·
    refine ⟨14126641172126914695243715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18835521562835886260324953 14126641172126914695243715)
    ·
      refine ⟨21189961758190372042865573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14126641172126914695243715 21189961758190372042865573)
      ·
        refine ⟨3973117829660694758037295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21189961758190372042865573 3973117829660694758037295)
        ·
          refine ⟨5959676744491042137055943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3973117829660694758037295 5959676744491042137055943)
          ·
            refine ⟨8939515116736563205583915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5959676744491042137055943 8939515116736563205583915)
            ·
              refine ⟨13409272675104844808375873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8939515116736563205583915 13409272675104844808375873)
              ·
                refine ⟨10056954506328633606281905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13409272675104844808375873 10056954506328633606281905)
                ·
                  refine ⟨7542715879746475204711429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10056954506328633606281905 7542715879746475204711429)
                  ·
                    refine ⟨1414259227452464100883393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7542715879746475204711429 1414259227452464100883393)
                    ·
                      rfl

theorem cell22_4131390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_4131390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131390 prefixEnd_4131390 := by exact prefixLift 4131390
  have htrace : WordTrace (prefixWord ++ tailWord_4131390) baseStart_4131390 baseEnd_4131390 := by
    simpa [prefixWord, tailWord_4131390, baseEnd_4131390] using wordTrace_append hprefix tailTrace_4131390
  have hstable : (prefixWord ++ tailWord_4131390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131390).length < 2 ^ (prefixWord ++ tailWord_4131390).sum := by decide
  have hdescent : baseEnd_4131390 < baseStart_4131390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131403 : List Nat := [1, 1, 1, 1, 3, 1, 4, 6, 1, 3]
def baseStart_4131403 : Nat := 118140960795 + 4131403 * 2 ^ 59
def prefixEnd_4131403 : Nat := 4983230072969 + 3 ^ 40 * 4131403 * 2
def baseEnd_4131403 : Nat := 1414263677618136400308353

theorem tailTrace_4131403 : CollatzResearch.WordTrace tailWord_4131403 prefixEnd_4131403 1414263677618136400308353 := by
  unfold tailWord_4131403
  simp only [CollatzResearch.WordTrace]
  refine ⟨150684646651639993302822863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100456431101093328868548575 150684646651639993302822863)
  ·
    refine ⟨226026969977459989954234295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150684646651639993302822863 226026969977459989954234295)
    ·
      refine ⟨339040454966189984931351443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226026969977459989954234295 339040454966189984931351443)
      ·
        refine ⟨508560682449284977397027165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339040454966189984931351443 508560682449284977397027165)
        ·
          refine ⟨190710255918481866523885187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 508560682449284977397027165 190710255918481866523885187)
          ·
            refine ⟨286065383877722799785827781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190710255918481866523885187 286065383877722799785827781)
            ·
              refine ⟨53637259477073024959842709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286065383877722799785827781 53637259477073024959842709)
              ·
                refine ⟨2514246537987798044992627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53637259477073024959842709 2514246537987798044992627)
                ·
                  refine ⟨3771369806981697067488941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2514246537987798044992627 3771369806981697067488941)
                  ·
                    refine ⟨1414263677618136400308353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3771369806981697067488941 1414263677618136400308353)
                    ·
                      rfl

theorem cell22_4131403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 1, 3].length) (baseStart_4131403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131403 prefixEnd_4131403 := by exact prefixLift 4131403
  have htrace : WordTrace (prefixWord ++ tailWord_4131403) baseStart_4131403 baseEnd_4131403 := by
    simpa [prefixWord, tailWord_4131403, baseEnd_4131403] using wordTrace_append hprefix tailTrace_4131403
  have hstable : (prefixWord ++ tailWord_4131403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131403).length < 2 ^ (prefixWord ++ tailWord_4131403).sum := by decide
  have hdescent : baseEnd_4131403 < baseStart_4131403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131491 : List Nat := [1, 1, 1, 4, 1, 1, 2, 5, 2, 4]
def baseStart_4131491 : Nat := 118140960795 + 4131491 * 2 ^ 59
def prefixEnd_4131491 : Nat := 4983230072969 + 3 ^ 40 * 4131491 * 2
def baseEnd_4131491 : Nat := 1414293801816533504108083

theorem tailTrace_4131491 : CollatzResearch.WordTrace tailWord_4131491 prefixEnd_4131491 1414293801816533504108083 := by
  unfold tailWord_4131491
  simp only [CollatzResearch.WordTrace]
  refine ⟨150687856275321184332026327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100458570850214122888017551 150687856275321184332026327)
  ·
    refine ⟨226031784412981776498039491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150687856275321184332026327 226031784412981776498039491)
    ·
      refine ⟨339047676619472664747059237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226031784412981776498039491 339047676619472664747059237)
      ·
        refine ⟨63571439366151124640073607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339047676619472664747059237 63571439366151124640073607)
        ·
          refine ⟨95357159049226686960110411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63571439366151124640073607 95357159049226686960110411)
          ·
            refine ⟨143035738573840030440165617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95357159049226686960110411 143035738573840030440165617)
            ·
              refine ⟨107276803930380022830124213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143035738573840030440165617 107276803930380022830124213)
              ·
                refine ⟨10057200368473127140324145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107276803930380022830124213 10057200368473127140324145)
                ·
                  refine ⟨7542900276354845355243109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10057200368473127140324145 7542900276354845355243109)
                  ·
                    refine ⟨1414293801816533504108083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7542900276354845355243109 1414293801816533504108083)
                    ·
                      rfl

theorem cell22_4131491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 4].length) (baseStart_4131491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131491 prefixEnd_4131491 := by exact prefixLift 4131491
  have htrace : WordTrace (prefixWord ++ tailWord_4131491) baseStart_4131491 baseEnd_4131491 := by
    simpa [prefixWord, tailWord_4131491, baseEnd_4131491] using wordTrace_append hprefix tailTrace_4131491
  have hstable : (prefixWord ++ tailWord_4131491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131491).length < 2 ^ (prefixWord ++ tailWord_4131491).sum := by decide
  have hdescent : baseEnd_4131491 < baseStart_4131491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131551 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 7]
def baseStart_4131551 : Nat := 118140960795 + 4131551 * 2 ^ 59
def prefixEnd_4131551 : Nat := 4983230072969 + 3 ^ 40 * 4131551 * 2
def baseEnd_4131551 : Nat := 471438113680904449202633

theorem tailTrace_4131551 : CollatzResearch.WordTrace tailWord_4131551 prefixEnd_4131551 471438113680904449202633 := by
  unfold tailWord_4131551
  simp only [CollatzResearch.WordTrace]
  refine ⟨150690044655103814579210507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100460029770069209719473671 150690044655103814579210507)
  ·
    refine ⟨226035066982655721868815761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150690044655103814579210507 226035066982655721868815761)
    ·
      refine ⟨169526300236991791401611821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226035066982655721868815761 169526300236991791401611821)
      ·
        refine ⟨63572362588871921775604433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169526300236991791401611821 63572362588871921775604433)
        ·
          refine ⟨47679271941653941331703325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63572362588871921775604433 47679271941653941331703325)
          ·
            refine ⟨17879726978120227999388747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47679271941653941331703325 17879726978120227999388747)
            ·
              refine ⟨26819590467180341999083121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17879726978120227999388747 26819590467180341999083121)
              ·
                refine ⟨20114692850385256499312341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26819590467180341999083121 20114692850385256499312341)
                ·
                  refine ⟨471438113680904449202633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20114692850385256499312341 471438113680904449202633)
                  ·
                    rfl

theorem cell22_4131551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 7].length) (baseStart_4131551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131551 prefixEnd_4131551 := by exact prefixLift 4131551
  have htrace : WordTrace (prefixWord ++ tailWord_4131551) baseStart_4131551 baseEnd_4131551 := by
    simpa [prefixWord, tailWord_4131551, baseEnd_4131551] using wordTrace_append hprefix tailTrace_4131551
  have hstable : (prefixWord ++ tailWord_4131551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131551).length < 2 ^ (prefixWord ++ tailWord_4131551).sum := by decide
  have hdescent : baseEnd_4131551 < baseStart_4131551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131596 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 8]
def baseStart_4131596 : Nat := 118140960795 + 4131596 * 2 ^ 59
def prefixEnd_4131596 : Nat := 4983230072969 + 3 ^ 40 * 4131596 * 2
def baseEnd_4131596 : Nat := 471443248487449410077587

theorem tailTrace_4131596 : CollatzResearch.WordTrace tailWord_4131596 prefixEnd_4131596 471443248487449410077587 := by
  unfold tailWord_4131596
  simp only [CollatzResearch.WordTrace]
  refine ⟨75345842969970393632299321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100461123959960524843065761 75345842969970393632299321)
  ·
    refine ⟨56509382227477795224224491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75345842969970393632299321 56509382227477795224224491)
    ·
      refine ⟨84764073341216692836336737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56509382227477795224224491 84764073341216692836336737)
      ·
        refine ⟨63573055005912519627252553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84764073341216692836336737 63573055005912519627252553)
        ·
          refine ⟨47679791254434389720439415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63573055005912519627252553 47679791254434389720439415)
          ·
            refine ⟨71519686881651584580659123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47679791254434389720439415 71519686881651584580659123)
            ·
              refine ⟨107279530322477376870988685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71519686881651584580659123 107279530322477376870988685)
              ·
                refine ⟨40229823870929016326620757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107279530322477376870988685 40229823870929016326620757)
                ·
                  refine ⟨471443248487449410077587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40229823870929016326620757 471443248487449410077587)
                  ·
                    rfl

theorem cell22_4131596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_4131596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131596 prefixEnd_4131596 := by exact prefixLift 4131596
  have htrace : WordTrace (prefixWord ++ tailWord_4131596) baseStart_4131596 baseEnd_4131596 := by
    simpa [prefixWord, tailWord_4131596, baseEnd_4131596] using wordTrace_append hprefix tailTrace_4131596
  have hstable : (prefixWord ++ tailWord_4131596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131596).length < 2 ^ (prefixWord ++ tailWord_4131596).sum := by decide
  have hdescent : baseEnd_4131596 < baseStart_4131596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131660 : List Nat := [2, 2, 1, 3, 3, 1, 3, 1, 2, 4]
def baseStart_4131660 : Nat := 118140960795 + 4131660 * 2 ^ 59
def prefixEnd_4131660 : Nat := 4983230072969 + 3 ^ 40 * 4131660 * 2
def baseEnd_4131660 : Nat := 1414351653970273396632565

theorem tailTrace_4131660 : CollatzResearch.WordTrace tailWord_4131660 prefixEnd_4131660 1414351653970273396632565 := by
  unfold tailWord_4131660
  simp only [CollatzResearch.WordTrace]
  refine ⟨75347010105854463097464217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100462680141139284129952289 75347010105854463097464217)
  ·
    refine ⟨56510257579390847323098163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75347010105854463097464217 56510257579390847323098163)
    ·
      refine ⟨84765386369086270984647245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56510257579390847323098163 84765386369086270984647245)
      ·
        refine ⟨31787019888407351619242717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84765386369086270984647245 31787019888407351619242717)
        ·
          refine ⟨11920132458152756857216019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31787019888407351619242717 11920132458152756857216019)
          ·
            refine ⟨17880198687229135285824029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11920132458152756857216019 17880198687229135285824029)
            ·
              refine ⟨6705074507710925732184011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17880198687229135285824029 6705074507710925732184011)
              ·
                refine ⟨10057611761566388598276017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6705074507710925732184011 10057611761566388598276017)
                ·
                  refine ⟨7543208821174791448707013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10057611761566388598276017 7543208821174791448707013)
                  ·
                    refine ⟨1414351653970273396632565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7543208821174791448707013 1414351653970273396632565)
                    ·
                      rfl

theorem cell22_4131660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_4131660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131660 prefixEnd_4131660 := by exact prefixLift 4131660
  have htrace : WordTrace (prefixWord ++ tailWord_4131660) baseStart_4131660 baseEnd_4131660 := by
    simpa [prefixWord, tailWord_4131660, baseEnd_4131660] using wordTrace_append hprefix tailTrace_4131660
  have hstable : (prefixWord ++ tailWord_4131660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131660).length < 2 ^ (prefixWord ++ tailWord_4131660).sum := by decide
  have hdescent : baseEnd_4131660 < baseStart_4131660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131703 : List Nat := [1, 1, 3, 1, 1, 2, 1, 7, 5]
def baseStart_4131703 : Nat := 118140960795 + 4131703 * 2 ^ 59
def prefixEnd_4131703 : Nat := 4983230072969 + 3 ^ 40 * 4131703 * 2
def baseEnd_4131703 : Nat := 471455457916345205935811

theorem tailTrace_4131703 : CollatzResearch.WordTrace tailWord_4131703 prefixEnd_4131703 471455457916345205935811 := by
  unfold tailWord_4131703
  simp only [CollatzResearch.WordTrace]
  refine ⟨150695588550553144538743763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100463725700368763025829175 150695588550553144538743763)
  ·
    refine ⟨226043382825829716808115645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150695588550553144538743763 226043382825829716808115645)
    ·
      refine ⟨84766268559686143803043367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226043382825829716808115645 84766268559686143803043367)
      ·
        refine ⟨127149402839529215704565051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84766268559686143803043367 127149402839529215704565051)
        ·
          refine ⟨190724104259293823556847577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127149402839529215704565051 190724104259293823556847577)
          ·
            refine ⟨143043078194470367667635683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190724104259293823556847577 143043078194470367667635683)
            ·
              refine ⟨214564617291705551501453525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143043078194470367667635683 214564617291705551501453525)
              ·
                refine ⟨5028858217774348863315317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 214564617291705551501453525 5028858217774348863315317)
                ·
                  refine ⟨471455457916345205935811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5028858217774348863315317 471455457916345205935811)
                  ·
                    rfl

theorem cell22_4131703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 5].length) (baseStart_4131703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131703 prefixEnd_4131703 := by exact prefixLift 4131703
  have htrace : WordTrace (prefixWord ++ tailWord_4131703) baseStart_4131703 baseEnd_4131703 := by
    simpa [prefixWord, tailWord_4131703, baseEnd_4131703] using wordTrace_append hprefix tailTrace_4131703
  have hstable : (prefixWord ++ tailWord_4131703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131703).length < 2 ^ (prefixWord ++ tailWord_4131703).sum := by decide
  have hdescent : baseEnd_4131703 < baseStart_4131703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131784 : List Nat := [2, 1, 3, 1, 5, 1, 3, 1, 1, 4]
def baseStart_4131784 : Nat := 118140960795 + 4131784 * 2 ^ 59
def prefixEnd_4131784 : Nat := 4983230072969 + 3 ^ 40 * 4131784 * 2
def baseEnd_4131784 : Nat := 1414394101704378406532185

theorem tailTrace_4131784 : CollatzResearch.WordTrace tailWord_4131784 prefixEnd_4131784 1414394101704378406532185 := by
  unfold tailWord_4131784
  simp only [CollatzResearch.WordTrace]
  refine ⟨75349271431629847686221203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100465695242173130248294937 75349271431629847686221203)
  ·
    refine ⟨113023907147444771529331805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75349271431629847686221203 113023907147444771529331805)
    ·
      refine ⟨42383965180291789323499427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113023907147444771529331805 42383965180291789323499427)
      ·
        refine ⟨63575947770437683985249141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42383965180291789323499427 63575947770437683985249141)
        ·
          refine ⟨5960245103478532873617107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63575947770437683985249141 5960245103478532873617107)
          ·
            refine ⟨8940367655217799310425661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5960245103478532873617107 8940367655217799310425661)
            ·
              refine ⟨3352637870706674741409623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8940367655217799310425661 3352637870706674741409623)
              ·
                refine ⟨5028956806060012112114435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3352637870706674741409623 5028956806060012112114435)
                ·
                  refine ⟨7543435209090018168171653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5028956806060012112114435 7543435209090018168171653)
                  ·
                    refine ⟨1414394101704378406532185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7543435209090018168171653 1414394101704378406532185)
                    ·
                      rfl

theorem cell22_4131784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_4131784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131784 prefixEnd_4131784 := by exact prefixLift 4131784
  have htrace : WordTrace (prefixWord ++ tailWord_4131784) baseStart_4131784 baseEnd_4131784 := by
    simpa [prefixWord, tailWord_4131784, baseEnd_4131784] using wordTrace_append hprefix tailTrace_4131784
  have hstable : (prefixWord ++ tailWord_4131784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131784).length < 2 ^ (prefixWord ++ tailWord_4131784).sum := by decide
  have hdescent : baseEnd_4131784 < baseStart_4131784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131808 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 4, 7]
def baseStart_4131808 : Nat := 118140960795 + 4131808 * 2 ^ 59
def prefixEnd_4131808 : Nat := 4983230072969 + 3 ^ 40 * 4131808 * 2
def baseEnd_4131808 : Nat := 1414402317394850343932111

theorem tailTrace_4131808 : CollatzResearch.WordTrace tailWord_4131808 prefixEnd_4131808 1414402317394850343932111 := by
  unfold tailWord_4131808
  simp only [CollatzResearch.WordTrace]
  refine ⟨75349709107586373735658039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100466278810115164980877385 75349709107586373735658039)
  ·
    refine ⟨113024563661379560603487059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75349709107586373735658039 113024563661379560603487059)
    ·
      refine ⟨169536845492069340905230589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113024563661379560603487059 169536845492069340905230589)
      ·
        refine ⟨63576317059526002839461471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169536845492069340905230589 63576317059526002839461471)
        ·
          refine ⟨95364475589289004259192207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63576317059526002839461471 95364475589289004259192207)
          ·
            refine ⟨143046713383933506388788311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95364475589289004259192207 143046713383933506388788311)
            ·
              refine ⟨214570070075900259583182467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143046713383933506388788311 214570070075900259583182467)
              ·
                refine ⟨321855105113850389374773701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214570070075900259583182467 321855105113850389374773701)
                ·
                  refine ⟨60347832208846948007770069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 321855105113850389374773701 60347832208846948007770069)
                  ·
                    refine ⟨1414402317394850343932111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60347832208846948007770069 1414402317394850343932111)
                    ·
                      rfl

theorem cell22_4131808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_4131808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131808 prefixEnd_4131808 := by exact prefixLift 4131808
  have htrace : WordTrace (prefixWord ++ tailWord_4131808) baseStart_4131808 baseEnd_4131808 := by
    simpa [prefixWord, tailWord_4131808, baseEnd_4131808] using wordTrace_append hprefix tailTrace_4131808
  have hstable : (prefixWord ++ tailWord_4131808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131808).length < 2 ^ (prefixWord ++ tailWord_4131808).sum := by decide
  have hdescent : baseEnd_4131808 < baseStart_4131808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131829 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 1, 6]
def baseStart_4131829 : Nat := 118140960795 + 4131829 * 2 ^ 59
def prefixEnd_4131829 : Nat := 4983230072969 + 3 ^ 40 * 4131829 * 2
def baseEnd_4131829 : Nat := 1414409506124013289157047

theorem tailTrace_4131829 : CollatzResearch.WordTrace tailWord_4131829 prefixEnd_4131829 1414409506124013289157047 := by
  unfold tailWord_4131829
  simp only [CollatzResearch.WordTrace]
  refine ⟨150700184148096668057830541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100466789432064445371887027 150700184148096668057830541)
  ·
    refine ⟨56512569055536250521686453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150700184148096668057830541 56512569055536250521686453)
    ·
      refine ⟨5298053348956523486408105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56512569055536250521686453 5298053348956523486408105)
      ·
        refine ⟨3973540011717392614806079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5298053348956523486408105 3973540011717392614806079)
        ·
          refine ⟨5960310017576088922209119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3973540011717392614806079 5960310017576088922209119)
          ·
            refine ⟨8940465026364133383313679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5960310017576088922209119 8940465026364133383313679)
            ·
              refine ⟨13410697539546200074970519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8940465026364133383313679 13410697539546200074970519)
              ·
                refine ⟨20116046309319300112455779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13410697539546200074970519 20116046309319300112455779)
                ·
                  refine ⟨30174069463978950168683669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20116046309319300112455779 30174069463978950168683669)
                  ·
                    refine ⟨1414409506124013289157047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30174069463978950168683669 1414409506124013289157047)
                    ·
                      rfl

theorem cell22_4131829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_4131829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131829 prefixEnd_4131829 := by exact prefixLift 4131829
  have htrace : WordTrace (prefixWord ++ tailWord_4131829) baseStart_4131829 baseEnd_4131829 := by
    simpa [prefixWord, tailWord_4131829, baseEnd_4131829] using wordTrace_append hprefix tailTrace_4131829
  have hstable : (prefixWord ++ tailWord_4131829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131829).length < 2 ^ (prefixWord ++ tailWord_4131829).sum := by decide
  have hdescent : baseEnd_4131829 < baseStart_4131829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131910 : List Nat := [6, 1, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_4131910 : Nat := 118140960795 + 4131910 * 2 ^ 59
def prefixEnd_4131910 : Nat := 4983230072969 + 3 ^ 40 * 4131910 * 2
def baseEnd_4131910 : Nat := 1414437234079356077881799

theorem tailTrace_4131910 : CollatzResearch.WordTrace tailWord_4131910 prefixEnd_4131910 1414437234079356077881799 := by
  unfold tailWord_4131910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4709473076900100590360287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100468758973868812594352789 4709473076900100590360287)
  ·
    refine ⟨7064209615350150885540431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4709473076900100590360287 7064209615350150885540431)
    ·
      refine ⟨10596314423025226328310647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7064209615350150885540431 10596314423025226328310647)
      ·
        refine ⟨15894471634537839492465971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10596314423025226328310647 15894471634537839492465971)
        ·
          refine ⟨23841707451806759238698957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15894471634537839492465971 23841707451806759238698957)
          ·
            refine ⟨8940640294427534714512109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23841707451806759238698957 8940640294427534714512109)
            ·
              refine ⟨3352740110410325517942041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8940640294427534714512109 3352740110410325517942041)
              ·
                refine ⟨2514555082807744138456531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3352740110410325517942041 2514555082807744138456531)
                ·
                  refine ⟨3771832624211616207684797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2514555082807744138456531 3771832624211616207684797)
                  ·
                    refine ⟨1414437234079356077881799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3771832624211616207684797 1414437234079356077881799)
                    ·
                      rfl

theorem cell22_4131910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_4131910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131910 prefixEnd_4131910 := by exact prefixLift 4131910
  have htrace : WordTrace (prefixWord ++ tailWord_4131910) baseStart_4131910 baseEnd_4131910 := by
    simpa [prefixWord, tailWord_4131910, baseEnd_4131910] using wordTrace_append hprefix tailTrace_4131910
  have hstable : (prefixWord ++ tailWord_4131910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131910).length < 2 ^ (prefixWord ++ tailWord_4131910).sum := by decide
  have hdescent : baseEnd_4131910 < baseStart_4131910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131930 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 1, 6]
def baseStart_4131930 : Nat := 118140960795 + 4131930 * 2 ^ 59
def prefixEnd_4131930 : Nat := 4983230072969 + 3 ^ 40 * 4131930 * 2
def baseEnd_4131930 : Nat := 1414444080488082692381737

theorem tailTrace_4131930 : CollatzResearch.WordTrace tailWord_4131930 prefixEnd_4131930 1414444080488082692381737 := by
  unfold tailWord_4131930
  simp only [CollatzResearch.WordTrace]
  refine ⟨37675966980182690576814311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100469245280487174871504829 37675966980182690576814311)
  ·
    refine ⟨56513950470274035865221467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37675966980182690576814311 56513950470274035865221467)
    ·
      refine ⟨84770925705411053797832201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56513950470274035865221467 84770925705411053797832201)
      ·
        refine ⟨63578194279058290348374151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84770925705411053797832201 63578194279058290348374151)
        ·
          refine ⟨95367291418587435522561227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63578194279058290348374151 95367291418587435522561227)
          ·
            refine ⟨143050937127881153283841841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95367291418587435522561227 143050937127881153283841841)
            ·
              refine ⟨107288202845910864962881381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143050937127881153283841841 107288202845910864962881381)
              ·
                refine ⟨20116538033608287180540259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107288202845910864962881381 20116538033608287180540259)
                ·
                  refine ⟨30174807050412430770810389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20116538033608287180540259 30174807050412430770810389)
                  ·
                    refine ⟨1414444080488082692381737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30174807050412430770810389 1414444080488082692381737)
                    ·
                      rfl

theorem cell22_4131930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_4131930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131930 prefixEnd_4131930 := by exact prefixLift 4131930
  have htrace : WordTrace (prefixWord ++ tailWord_4131930) baseStart_4131930 baseEnd_4131930 := by
    simpa [prefixWord, tailWord_4131930, baseEnd_4131930] using wordTrace_append hprefix tailTrace_4131930
  have hstable : (prefixWord ++ tailWord_4131930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131930).length < 2 ^ (prefixWord ++ tailWord_4131930).sum := by decide
  have hdescent : baseEnd_4131930 < baseStart_4131930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131932 : List Nat := [2, 2, 4, 1, 1, 1, 2, 3, 1, 5]
def baseStart_4131932 : Nat := 118140960795 + 4131932 * 2 ^ 59
def prefixEnd_4131932 : Nat := 4983230072969 + 3 ^ 40 * 4131932 * 2
def baseEnd_4131932 : Nat := 1414444765128955353831731

theorem tailTrace_4131932 : CollatzResearch.WordTrace tailWord_4131932 prefixEnd_4131932 1414444765128955353831731 := by
  unfold tailWord_4131932
  simp only [CollatzResearch.WordTrace]
  refine ⟨75351970433361758324415025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100469293911149011099220033 75351970433361758324415025)
  ·
    refine ⟨56513977825021318743311269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75351970433361758324415025 56513977825021318743311269)
    ·
      refine ⟨10596370842191497264370863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56513977825021318743311269 10596370842191497264370863)
      ·
        refine ⟨15894556263287245896556295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10596370842191497264370863 15894556263287245896556295)
        ·
          refine ⟨23841834394930868844834443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15894556263287245896556295 23841834394930868844834443)
          ·
            refine ⟨35762751592396303267251665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23841834394930868844834443 35762751592396303267251665)
            ·
              refine ⟨26822063694297227450438749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35762751592396303267251665 26822063694297227450438749)
              ·
                refine ⟨10058273885361460293914531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26822063694297227450438749 10058273885361460293914531)
                ·
                  refine ⟨15087410828042190440871797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10058273885361460293914531 15087410828042190440871797)
                  ·
                    refine ⟨1414444765128955353831731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15087410828042190440871797 1414444765128955353831731)
                    ·
                      rfl

theorem cell22_4131932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_4131932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131932 prefixEnd_4131932 := by exact prefixLift 4131932
  have htrace : WordTrace (prefixWord ++ tailWord_4131932) baseStart_4131932 baseEnd_4131932 := by
    simpa [prefixWord, tailWord_4131932, baseEnd_4131932] using wordTrace_append hprefix tailTrace_4131932
  have hstable : (prefixWord ++ tailWord_4131932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131932).length < 2 ^ (prefixWord ++ tailWord_4131932).sum := by decide
  have hdescent : baseEnd_4131932 < baseStart_4131932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131945 : List Nat := [1, 2, 1, 1, 1, 6, 2, 8]
def baseStart_4131945 : Nat := 118140960795 + 4131945 * 2 ^ 59
def prefixEnd_4131945 : Nat := 4983230072969 + 3 ^ 40 * 4131945 * 2
def baseEnd_4131945 : Nat := 157161023921625294806299

theorem tailTrace_4131945 : CollatzResearch.WordTrace tailWord_4131945 prefixEnd_4131945 157161023921625294806299 := by
  unfold tailWord_4131945
  simp only [CollatzResearch.WordTrace]
  refine ⟨150704415015676419869053289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100469610010450946579368859 150704415015676419869053289)
  ·
    refine ⟨113028311261757314901789967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150704415015676419869053289 113028311261757314901789967)
    ·
      refine ⟨169542466892635972352684951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113028311261757314901789967 169542466892635972352684951)
      ·
        refine ⟨254313700338953958529027427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169542466892635972352684951 254313700338953958529027427)
        ·
          refine ⟨381470550508430937793541141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254313700338953958529027427 381470550508430937793541141)
          ·
            refine ⟨17881432055082700209072241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 381470550508430937793541141 17881432055082700209072241)
            ·
              refine ⟨13411074041312025156804181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17881432055082700209072241 13411074041312025156804181)
              ·
                refine ⟨157161023921625294806299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13411074041312025156804181 157161023921625294806299)
                ·
                  rfl

theorem cell22_4131945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 8].length) (baseStart_4131945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131945 prefixEnd_4131945 := by exact prefixLift 4131945
  have htrace : WordTrace (prefixWord ++ tailWord_4131945) baseStart_4131945 baseEnd_4131945 := by
    simpa [prefixWord, tailWord_4131945, baseEnd_4131945] using wordTrace_append hprefix tailTrace_4131945
  have hstable : (prefixWord ++ tailWord_4131945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131945).length < 2 ^ (prefixWord ++ tailWord_4131945).sum := by decide
  have hdescent : baseEnd_4131945 < baseStart_4131945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4131994 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 5, 3]
def baseStart_4131994 : Nat := 118140960795 + 4131994 * 2 ^ 59
def prefixEnd_4131994 : Nat := 4983230072969 + 3 ^ 40 * 4131994 * 2
def baseEnd_4131994 : Nat := 1414465988996007858781541

theorem tailTrace_4131994 : CollatzResearch.WordTrace tailWord_4131994 prefixEnd_4131994 1414465988996007858781541 := by
  unfold tailWord_4131994
  simp only [CollatzResearch.WordTrace]
  refine ⟨37676550548124725309396759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100470801461665934158391357 37676550548124725309396759)
  ·
    refine ⟨56514825822187087964095139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37676550548124725309396759 56514825822187087964095139)
    ·
      refine ⟨84772238733280631946142709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56514825822187087964095139 84772238733280631946142709)
      ·
        refine ⟨7947397381245059244950879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84772238733280631946142709 7947397381245059244950879)
        ·
          refine ⟨11921096071867588867426319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7947397381245059244950879 11921096071867588867426319)
          ·
            refine ⟨17881644107801383301139479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11921096071867588867426319 17881644107801383301139479)
            ·
              refine ⟨26822466161702074951709219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17881644107801383301139479 26822466161702074951709219)
              ·
                refine ⟨40233699242553112427563829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26822466161702074951709219 40233699242553112427563829)
                ·
                  refine ⟨3771909303989354290084109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40233699242553112427563829 3771909303989354290084109)
                  ·
                    refine ⟨1414465988996007858781541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3771909303989354290084109 1414465988996007858781541)
                    ·
                      rfl

theorem cell22_4131994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_4131994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4131994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4131994 prefixEnd_4131994 := by exact prefixLift 4131994
  have htrace : WordTrace (prefixWord ++ tailWord_4131994) baseStart_4131994 baseEnd_4131994 := by
    simpa [prefixWord, tailWord_4131994, baseEnd_4131994] using wordTrace_append hprefix tailTrace_4131994
  have hstable : (prefixWord ++ tailWord_4131994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4131994).length < 2 ^ (prefixWord ++ tailWord_4131994).sum := by decide
  have hdescent : baseEnd_4131994 < baseStart_4131994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4131994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132097 : List Nat := [1, 2, 4, 1, 1, 3, 1, 9]
def baseStart_4132097 : Nat := 118140960795 + 4132097 * 2 ^ 59
def prefixEnd_4132097 : Nat := 4983230072969 + 3 ^ 40 * 4132097 * 2
def baseEnd_4132097 : Nat := 157166805333438880384025

theorem tailTrace_4132097 : CollatzResearch.WordTrace tailWord_4132097 prefixEnd_4132097 157166805333438880384025 := by
  unfold tailWord_4132097
  simp only [CollatzResearch.WordTrace]
  refine ⟨150709958911125749828586545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100473305940750499885724363 150709958911125749828586545)
  ·
    refine ⟨113032469183344312371439909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150709958911125749828586545 113032469183344312371439909)
    ·
      refine ⟨21193587971877058569644983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113032469183344312371439909 21193587971877058569644983)
      ·
        refine ⟨31790381957815587854467475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21193587971877058569644983 31790381957815587854467475)
        ·
          refine ⟨47685572936723381781701213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31790381957815587854467475 47685572936723381781701213)
          ·
            refine ⟨17882089851271268168137955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47685572936723381781701213 17882089851271268168137955)
            ·
              refine ⟨26823134776906902252206933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17882089851271268168137955 26823134776906902252206933)
              ·
                refine ⟨157166805333438880384025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26823134776906902252206933 157166805333438880384025)
                ·
                  rfl

theorem cell22_4132097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 9].length) (baseStart_4132097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132097 prefixEnd_4132097 := by exact prefixLift 4132097
  have htrace : WordTrace (prefixWord ++ tailWord_4132097) baseStart_4132097 baseEnd_4132097 := by
    simpa [prefixWord, tailWord_4132097, baseEnd_4132097] using wordTrace_append hprefix tailTrace_4132097
  have hstable : (prefixWord ++ tailWord_4132097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132097).length < 2 ^ (prefixWord ++ tailWord_4132097).sum := by decide
  have hdescent : baseEnd_4132097 < baseStart_4132097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132159 : List Nat := [1, 1, 2, 2, 4, 2, 2, 3, 5]
def baseStart_4132159 : Nat := 118140960795 + 4132159 * 2 ^ 59
def prefixEnd_4132159 : Nat := 4983230072969 + 3 ^ 40 * 4132159 * 2
def baseEnd_4132159 : Nat := 471507490622667476135345

theorem tailTrace_4132159 : CollatzResearch.WordTrace tailWord_4132159 prefixEnd_4132159 471507490622667476135345 := by
  unfold tailWord_4132159
  simp only [CollatzResearch.WordTrace]
  refine ⟨150712220236901134417343531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100474813491267422944895687 150712220236901134417343531)
  ·
    refine ⟨226068330355351701626015297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150712220236901134417343531 226068330355351701626015297)
    ·
      refine ⟨169551247766513776219511473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226068330355351701626015297 169551247766513776219511473)
      ·
        refine ⟨127163435824885332164633605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169551247766513776219511473 127163435824885332164633605)
        ·
          refine ⟨23843144217165999780868801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127163435824885332164633605 23843144217165999780868801)
          ·
            refine ⟨17882358162874499835651601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23843144217165999780868801 17882358162874499835651601)
            ·
              refine ⟨13411768622155874876738701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17882358162874499835651601 13411768622155874876738701)
              ·
                refine ⟨5029413233308453078777013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13411768622155874876738701 5029413233308453078777013)
                ·
                  refine ⟨471507490622667476135345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5029413233308453078777013 471507490622667476135345)
                  ·
                    rfl

theorem cell22_4132159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 5].length) (baseStart_4132159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132159 prefixEnd_4132159 := by exact prefixLift 4132159
  have htrace : WordTrace (prefixWord ++ tailWord_4132159) baseStart_4132159 baseEnd_4132159 := by
    simpa [prefixWord, tailWord_4132159, baseEnd_4132159] using wordTrace_append hprefix tailTrace_4132159
  have hstable : (prefixWord ++ tailWord_4132159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132159).length < 2 ^ (prefixWord ++ tailWord_4132159).sum := by decide
  have hdescent : baseEnd_4132159 < baseStart_4132159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132204 : List Nat := [2, 2, 1, 1, 5, 1, 1, 3, 6]
def baseStart_4132204 : Nat := 118140960795 + 4132204 * 2 ^ 59
def prefixEnd_4132204 : Nat := 4983230072969 + 3 ^ 40 * 4132204 * 2
def baseEnd_4132204 : Nat := 471512625429212437010299

theorem tailTrace_4132204 : CollatzResearch.WordTrace tailWord_4132204 prefixEnd_4132204 471512625429212437010299 := by
  unfold tailWord_4132204
  simp only [CollatzResearch.WordTrace]
  refine ⟨75356930760869053551365833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100475907681158738068487777 75356930760869053551365833)
  ·
    refine ⟨56517698070651790163524375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75356930760869053551365833 56517698070651790163524375)
    ·
      refine ⟨84776547105977685245286563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56517698070651790163524375 84776547105977685245286563)
      ·
        refine ⟨127164820658966527867929845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84776547105977685245286563 127164820658966527867929845)
        ·
          refine ⟨11921701936778111987618423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127164820658966527867929845 11921701936778111987618423)
          ·
            refine ⟨17882552905167167981427635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11921701936778111987618423 17882552905167167981427635)
            ·
              refine ⟨26823829357750751972141453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17882552905167167981427635 26823829357750751972141453)
              ·
                refine ⟨10058936009156531989553045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26823829357750751972141453 10058936009156531989553045)
                ·
                  refine ⟨471512625429212437010299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10058936009156531989553045 471512625429212437010299)
                  ·
                    rfl

theorem cell22_4132204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_4132204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132204 prefixEnd_4132204 := by exact prefixLift 4132204
  have htrace : WordTrace (prefixWord ++ tailWord_4132204) baseStart_4132204 baseEnd_4132204 := by
    simpa [prefixWord, tailWord_4132204, baseEnd_4132204] using wordTrace_append hprefix tailTrace_4132204
  have hstable : (prefixWord ++ tailWord_4132204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132204).length < 2 ^ (prefixWord ++ tailWord_4132204).sum := by decide
  have hdescent : baseEnd_4132204 < baseStart_4132204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132249 : List Nat := [1, 2, 1, 2, 1, 7, 8]
def baseStart_4132249 : Nat := 118140960795 + 4132249 * 2 ^ 59
def prefixEnd_4132249 : Nat := 4983230072969 + 3 ^ 40 * 4132249 * 2
def baseEnd_4132249 : Nat := 52390862248417488653917

theorem tailTrace_4132249 : CollatzResearch.WordTrace tailWord_4132249 prefixEnd_4132249 52390862248417488653917 := by
  unfold tailWord_4132249
  simp only [CollatzResearch.WordTrace]
  refine ⟨150715502806575079788119801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100477001871050053192079867 150715502806575079788119801)
  ·
    refine ⟨113036627104931309841089851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150715502806575079788119801 113036627104931309841089851)
    ·
      refine ⟨169554940657396964761634777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113036627104931309841089851 169554940657396964761634777)
      ·
        refine ⟨127166205493047723571226083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169554940657396964761634777 127166205493047723571226083)
        ·
          refine ⟨190749308239571585356839125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127166205493047723571226083 190749308239571585356839125)
          ·
            refine ⟨4470686911864959031800917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 190749308239571585356839125 4470686911864959031800917)
            ·
              refine ⟨52390862248417488653917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4470686911864959031800917 52390862248417488653917)
              ·
                rfl

theorem cell22_4132249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 8].length) (baseStart_4132249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132249 prefixEnd_4132249 := by exact prefixLift 4132249
  have htrace : WordTrace (prefixWord ++ tailWord_4132249) baseStart_4132249 baseEnd_4132249 := by
    simpa [prefixWord, tailWord_4132249, baseEnd_4132249] using wordTrace_append hprefix tailTrace_4132249
  have hstable : (prefixWord ++ tailWord_4132249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132249).length < 2 ^ (prefixWord ++ tailWord_4132249).sum := by decide
  have hdescent : baseEnd_4132249 < baseStart_4132249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132373 : List Nat := [1, 3, 2, 1, 3, 2, 2, 4, 4]
def baseStart_4132373 : Nat := 118140960795 + 4132373 * 2 ^ 59
def prefixEnd_4132373 : Nat := 4983230072969 + 3 ^ 40 * 4132373 * 2
def baseEnd_4132373 : Nat := 471531909480459067851793

theorem tailTrace_4132373 : CollatzResearch.WordTrace tailWord_4132373 prefixEnd_4132373 471531909480459067851793 := by
  unfold tailWord_4132373
  simp only [CollatzResearch.WordTrace]
  refine ⟨150720025458125848965633773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100480016972083899310422515 150720025458125848965633773)
  ·
    refine ⟨56520009546797193362112665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150720025458125848965633773 56520009546797193362112665)
    ·
      refine ⟨42390007160097895021584499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56520009546797193362112665 42390007160097895021584499)
      ·
        refine ⟨63585010740146842532376749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42390007160097895021584499 63585010740146842532376749)
        ·
          refine ⟨23844379027555065949641281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63585010740146842532376749 23844379027555065949641281)
          ·
            refine ⟨17883284270666299462230961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23844379027555065949641281 17883284270666299462230961)
            ·
              refine ⟨13412463202999724596673221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17883284270666299462230961 13412463202999724596673221)
              ·
                refine ⟨2514836850562448361876229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13412463202999724596673221 2514836850562448361876229)
                ·
                  refine ⟨471531909480459067851793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2514836850562448361876229 471531909480459067851793)
                  ·
                    rfl

theorem cell22_4132373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_4132373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132373 prefixEnd_4132373 := by exact prefixLift 4132373
  have htrace : WordTrace (prefixWord ++ tailWord_4132373) baseStart_4132373 baseEnd_4132373 := by
    simpa [prefixWord, tailWord_4132373, baseEnd_4132373] using wordTrace_append hprefix tailTrace_4132373
  have hstable : (prefixWord ++ tailWord_4132373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132373).length < 2 ^ (prefixWord ++ tailWord_4132373).sum := by decide
  have hdescent : baseEnd_4132373 < baseStart_4132373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132386 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_4132386 : Nat := 118140960795 + 4132386 * 2 ^ 59
def prefixEnd_4132386 : Nat := 4983230072969 + 3 ^ 40 * 4132386 * 2
def baseEnd_4132386 : Nat := 1414600178607049502980339

theorem tailTrace_4132386 : CollatzResearch.WordTrace tailWord_4132386 prefixEnd_4132386 1414600178607049502980339 := by
  unfold tailWord_4132386
  simp only [CollatzResearch.WordTrace]
  refine ⟨37680124901769688046464253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100480333071385834790571341 37680124901769688046464253)
  ·
    refine ⟨14130046838163633017424095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37680124901769688046464253 14130046838163633017424095)
    ·
      refine ⟨21195070257245449526136143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14130046838163633017424095 21195070257245449526136143)
      ·
        refine ⟨31792605385868174289204215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21195070257245449526136143 31792605385868174289204215)
        ·
          refine ⟨47688908078802261433806323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31792605385868174289204215 47688908078802261433806323)
          ·
            refine ⟨71533362118203392150709485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47688908078802261433806323 71533362118203392150709485)
            ·
              refine ⟨26825010794326272056516057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71533362118203392150709485 26825010794326272056516057)
              ·
                refine ⟨20118758095744704042387043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26825010794326272056516057 20118758095744704042387043)
                ·
                  refine ⟨30178137143617056063580565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20118758095744704042387043 30178137143617056063580565)
                  ·
                    refine ⟨1414600178607049502980339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30178137143617056063580565 1414600178607049502980339)
                    ·
                      rfl

theorem cell22_4132386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_4132386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132386 prefixEnd_4132386 := by exact prefixLift 4132386
  have htrace : WordTrace (prefixWord ++ tailWord_4132386) baseStart_4132386 baseEnd_4132386 := by
    simpa [prefixWord, tailWord_4132386, baseEnd_4132386] using wordTrace_append hprefix tailTrace_4132386
  have hstable : (prefixWord ++ tailWord_4132386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132386).length < 2 ^ (prefixWord ++ tailWord_4132386).sum := by decide
  have hdescent : baseEnd_4132386 < baseStart_4132386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132491 : List Nat := [1, 1, 1, 1, 4, 1, 4, 3, 6]
def baseStart_4132491 : Nat := 118140960795 + 4132491 * 2 ^ 59
def prefixEnd_4132491 : Nat := 4983230072969 + 3 ^ 40 * 4132491 * 2
def baseEnd_4132491 : Nat := 471545374084288076368339

theorem tailTrace_4132491 : CollatzResearch.WordTrace tailWord_4132491 prefixEnd_4132491 471545374084288076368339 := by
  unfold tailWord_4132491
  simp only [CollatzResearch.WordTrace]
  refine ⟨150724329271698355118429327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100482886181132236745619551 150724329271698355118429327)
  ·
    refine ⟨226086493907547532677643991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150724329271698355118429327 226086493907547532677643991)
    ·
      refine ⟨339129740861321299016465987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226086493907547532677643991 339129740861321299016465987)
      ·
        refine ⟨508694611291981948524698981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339129740861321299016465987 508694611291981948524698981)
        ·
          refine ⟨95380239617246615348381059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 508694611291981948524698981 95380239617246615348381059)
          ·
            refine ⟨143070359425869923022571589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95380239617246615348381059 143070359425869923022571589)
            ·
              refine ⟨26825692392350610566732173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143070359425869923022571589 26825692392350610566732173)
              ·
                refine ⟨10059634647131478962524565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26825692392350610566732173 10059634647131478962524565)
                ·
                  refine ⟨471545374084288076368339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10059634647131478962524565 471545374084288076368339)
                  ·
                    rfl

theorem cell22_4132491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 6].length) (baseStart_4132491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132491 prefixEnd_4132491 := by exact prefixLift 4132491
  have htrace : WordTrace (prefixWord ++ tailWord_4132491) baseStart_4132491 baseEnd_4132491 := by
    simpa [prefixWord, tailWord_4132491, baseEnd_4132491] using wordTrace_append hprefix tailTrace_4132491
  have hstable : (prefixWord ++ tailWord_4132491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132491).length < 2 ^ (prefixWord ++ tailWord_4132491).sum := by decide
  have hdescent : baseEnd_4132491 < baseStart_4132491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132510 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_4132510 : Nat := 118140960795 + 4132510 * 2 ^ 59
def prefixEnd_4132510 : Nat := 4983230072969 + 3 ^ 40 * 4132510 * 2
def baseEnd_4132510 : Nat := 1414642626341154512879959

theorem tailTrace_4132510 : CollatzResearch.WordTrace tailWord_4132510 prefixEnd_4132510 1414642626341154512879959 := by
  unfold tailWord_4132510
  simp only [CollatzResearch.WordTrace]
  refine ⟨18840627782328690170421373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100483348172419680908913989 18840627782328690170421373)
  ·
    refine ⟨7065235418373258813908015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18840627782328690170421373 7065235418373258813908015)
    ·
      refine ⟨10597853127559888220862023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7065235418373258813908015 10597853127559888220862023)
      ·
        refine ⟨15896779691339832331293035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10597853127559888220862023 15896779691339832331293035)
        ·
          refine ⟨23845169537009748496939553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15896779691339832331293035 23845169537009748496939553)
          ·
            refine ⟨17883877152757311372704665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23845169537009748496939553 17883877152757311372704665)
            ·
              refine ⟨13412907864567983529528499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17883877152757311372704665 13412907864567983529528499)
              ·
                refine ⟨20119361796851975294292749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13412907864567983529528499 20119361796851975294292749)
                ·
                  refine ⟨7544760673819490735359781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20119361796851975294292749 7544760673819490735359781)
                  ·
                    refine ⟨1414642626341154512879959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7544760673819490735359781 1414642626341154512879959)
                    ·
                      rfl

theorem cell22_4132510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_4132510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132510 prefixEnd_4132510 := by exact prefixLift 4132510
  have htrace : WordTrace (prefixWord ++ tailWord_4132510) baseStart_4132510 baseEnd_4132510 := by
    simpa [prefixWord, tailWord_4132510, baseEnd_4132510] using wordTrace_append hprefix tailTrace_4132510
  have hstable : (prefixWord ++ tailWord_4132510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132510).length < 2 ^ (prefixWord ++ tailWord_4132510).sum := by decide
  have hdescent : baseEnd_4132510 < baseStart_4132510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132540 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 4, 3]
def baseStart_4132540 : Nat := 118140960795 + 4132540 * 2 ^ 59
def prefixEnd_4132540 : Nat := 4983230072969 + 3 ^ 40 * 4132540 * 2
def baseEnd_4132540 : Nat := 1414652895954244434629867

theorem tailTrace_4132540 : CollatzResearch.WordTrace tailWord_4132540 prefixEnd_4132540 1414652895954244434629867 := by
  unfold tailWord_4132540
  simp only [CollatzResearch.WordTrace]
  refine ⟨75363058224260418243481537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100484077632347224324642049 75363058224260418243481537)
  ·
    refine ⟨56522293668195313682611153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75363058224260418243481537 56522293668195313682611153)
    ·
      refine ⟨42391720251146485261958365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56522293668195313682611153 42391720251146485261958365)
      ·
        refine ⟨15896895094179931973234387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42391720251146485261958365 15896895094179931973234387)
        ·
          refine ⟨23845342641269897959851581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15896895094179931973234387 23845342641269897959851581)
          ·
            refine ⟨8942003490476211734944343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23845342641269897959851581 8942003490476211734944343)
            ·
              refine ⟨13413005235714317602416515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8942003490476211734944343 13413005235714317602416515)
              ·
                refine ⟨20119507853571476403624773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13413005235714317602416515 20119507853571476403624773)
                ·
                  refine ⟨3772407722544651825679645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20119507853571476403624773 3772407722544651825679645)
                  ·
                    refine ⟨1414652895954244434629867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3772407722544651825679645 1414652895954244434629867)
                    ·
                      rfl

theorem cell22_4132540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_4132540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132540 prefixEnd_4132540 := by exact prefixLift 4132540
  have htrace : WordTrace (prefixWord ++ tailWord_4132540) baseStart_4132540 baseEnd_4132540 := by
    simpa [prefixWord, tailWord_4132540, baseEnd_4132540] using wordTrace_append hprefix tailTrace_4132540
  have hstable : (prefixWord ++ tailWord_4132540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132540).length < 2 ^ (prefixWord ++ tailWord_4132540).sum := by decide
  have hdescent : baseEnd_4132540 < baseStart_4132540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132557 : List Nat := [1, 6, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_4132557 : Nat := 118140960795 + 4132557 * 2 ^ 59
def prefixEnd_4132557 : Nat := 4983230072969 + 3 ^ 40 * 4132557 * 2
def baseEnd_4132557 : Nat := 1414658715401662056954815

theorem tailTrace_4132557 : CollatzResearch.WordTrace tailWord_4132557 prefixEnd_4132557 1414658715401662056954815 := by
  unfold tailWord_4132557
  simp only [CollatzResearch.WordTrace]
  refine ⟨150726736489459248390331925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100484490992972832260221283 150726736489459248390331925)
  ·
    refine ⟨7065315772943402268296809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150726736489459248390331925 7065315772943402268296809)
    ·
      refine ⟨5298986829707551701222607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7065315772943402268296809 5298986829707551701222607)
      ·
        refine ⟨7948480244561327551833911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5298986829707551701222607 7948480244561327551833911)
        ·
          refine ⟨11922720366841991327750867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7948480244561327551833911 11922720366841991327750867)
          ·
            refine ⟨17884080550262986991626301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11922720366841991327750867 17884080550262986991626301)
            ·
              refine ⟨6706530206348620121859863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17884080550262986991626301 6706530206348620121859863)
              ·
                refine ⟨10059795309522930182789795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6706530206348620121859863 10059795309522930182789795)
                ·
                  refine ⟨15089692964284395274184693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10059795309522930182789795 15089692964284395274184693)
                  ·
                    refine ⟨1414658715401662056954815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15089692964284395274184693 1414658715401662056954815)
                    ·
                      rfl

theorem cell22_4132557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_4132557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132557 prefixEnd_4132557 := by exact prefixLift 4132557
  have htrace : WordTrace (prefixWord ++ tailWord_4132557) baseStart_4132557 baseEnd_4132557 := by
    simpa [prefixWord, tailWord_4132557, baseEnd_4132557] using wordTrace_append hprefix tailTrace_4132557
  have hstable : (prefixWord ++ tailWord_4132557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132557).length < 2 ^ (prefixWord ++ tailWord_4132557).sum := by decide
  have hdescent : baseEnd_4132557 < baseStart_4132557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132570 : List Nat := [3, 1, 1, 2, 2, 5, 2, 6]
def baseStart_4132570 : Nat := 118140960795 + 4132570 * 2 ^ 59
def prefixEnd_4132570 : Nat := 4983230072969 + 3 ^ 40 * 4132570 * 2
def baseEnd_4132570 : Nat := 157184796174148261819975

theorem tailTrace_4132570 : CollatzResearch.WordTrace tailWord_4132570 prefixEnd_4132570 157184796174148261819975 := by
  unfold tailWord_4132570
  simp only [CollatzResearch.WordTrace]
  refine ⟨37681802659603037902638791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100484807092274767740370109 37681802659603037902638791)
  ·
    refine ⟨56522703989404556853958187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37681802659603037902638791 56522703989404556853958187)
    ·
      refine ⟨84784055984106835280937281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56522703989404556853958187 84784055984106835280937281)
      ·
        refine ⟨63588041988080126460702961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84784055984106835280937281 63588041988080126460702961)
        ·
          refine ⟨47691031491060094845527221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63588041988080126460702961 47691031491060094845527221)
          ·
            refine ⟨4471034202286883891768177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47691031491060094845527221 4471034202286883891768177)
            ·
              refine ⟨3353275651715162918826133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4471034202286883891768177 3353275651715162918826133)
              ·
                refine ⟨157184796174148261819975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3353275651715162918826133 157184796174148261819975)
                ·
                  rfl

theorem cell22_4132570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 6].length) (baseStart_4132570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132570 prefixEnd_4132570 := by exact prefixLift 4132570
  have htrace : WordTrace (prefixWord ++ tailWord_4132570) baseStart_4132570 baseEnd_4132570 := by
    simpa [prefixWord, tailWord_4132570, baseEnd_4132570] using wordTrace_append hprefix tailTrace_4132570
  have hstable : (prefixWord ++ tailWord_4132570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132570).length < 2 ^ (prefixWord ++ tailWord_4132570).sum := by decide
  have hdescent : baseEnd_4132570 < baseStart_4132570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132662 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_4132662 : Nat := 118140960795 + 4132662 * 2 ^ 59
def prefixEnd_4132662 : Nat := 4983230072969 + 3 ^ 40 * 4132662 * 2
def baseEnd_4132662 : Nat := 1414694659047476783079493

theorem tailTrace_4132662 : CollatzResearch.WordTrace tailWord_4132662 prefixEnd_4132662 1414694659047476783079493 := by
  unfold tailWord_4132662
  simp only [CollatzResearch.WordTrace]
  refine ⟨9420660384629928207681515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100487044102719234215269493 9420660384629928207681515)
  ·
    refine ⟨14130990576944892311522273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9420660384629928207681515 14130990576944892311522273)
    ·
      refine ⟨10598242932708669233641705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14130990576944892311522273 10598242932708669233641705)
      ·
        refine ⟨7948682199531501925231279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10598242932708669233641705 7948682199531501925231279)
        ·
          refine ⟨11923023299297252887846919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7948682199531501925231279 11923023299297252887846919)
          ·
            refine ⟨17884534948945879331770379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11923023299297252887846919 17884534948945879331770379)
            ·
              refine ⟨26826802423418818997655569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17884534948945879331770379 26826802423418818997655569)
              ·
                refine ⟨20120101817564114248241677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26826802423418818997655569 20120101817564114248241677)
                ·
                  refine ⟨7545038181586542843090629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20120101817564114248241677 7545038181586542843090629)
                  ·
                    refine ⟨1414694659047476783079493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7545038181586542843090629 1414694659047476783079493)
                    ·
                      rfl

theorem cell22_4132662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_4132662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132662 prefixEnd_4132662 := by exact prefixLift 4132662
  have htrace : WordTrace (prefixWord ++ tailWord_4132662) baseStart_4132662 baseEnd_4132662 := by
    simpa [prefixWord, tailWord_4132662, baseEnd_4132662] using wordTrace_append hprefix tailTrace_4132662
  have hstable : (prefixWord ++ tailWord_4132662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132662).length < 2 ^ (prefixWord ++ tailWord_4132662).sum := by decide
  have hdescent : baseEnd_4132662 < baseStart_4132662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132675 : List Nat := [1, 1, 1, 3, 1, 6, 2, 1, 1, 5]
def baseStart_4132675 : Nat := 118140960795 + 4132675 * 2 ^ 59
def prefixEnd_4132675 : Nat := 4983230072969 + 3 ^ 40 * 4132675 * 2
def baseEnd_4132675 : Nat := 1414699109213149082504453

theorem tailTrace_4132675 : CollatzResearch.WordTrace tailWord_4132675 prefixEnd_4132675 1414699109213149082504453 := by
  unfold tailWord_4132675
  simp only [CollatzResearch.WordTrace]
  refine ⟨150731040303031754543127479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100487360202021169695418319 150731040303031754543127479)
  ·
    refine ⟨226096560454547631814691219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150731040303031754543127479 226096560454547631814691219)
    ·
      refine ⟨339144840681821447722036829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226096560454547631814691219 339144840681821447722036829)
      ·
        refine ⟨127179315255683042895763811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339144840681821447722036829 127179315255683042895763811)
        ·
          refine ⟨190768972883524564343645717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127179315255683042895763811 190768972883524564343645717)
          ·
            refine ⟨8942295603915213953608393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 190768972883524564343645717 8942295603915213953608393)
            ·
              refine ⟨6706721702936410465206295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8942295603915213953608393 6706721702936410465206295)
              ·
                refine ⟨10060082554404615697809443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6706721702936410465206295 10060082554404615697809443)
                ·
                  refine ⟨15090123831606923546714165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10060082554404615697809443 15090123831606923546714165)
                  ·
                    refine ⟨1414699109213149082504453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15090123831606923546714165 1414699109213149082504453)
                    ·
                      rfl

theorem cell22_4132675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 5].length) (baseStart_4132675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132675 prefixEnd_4132675 := by exact prefixLift 4132675
  have htrace : WordTrace (prefixWord ++ tailWord_4132675) baseStart_4132675 baseEnd_4132675 := by
    simpa [prefixWord, tailWord_4132675, baseEnd_4132675] using wordTrace_append hprefix tailTrace_4132675
  have hstable : (prefixWord ++ tailWord_4132675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132675).length < 2 ^ (prefixWord ++ tailWord_4132675).sum := by decide
  have hdescent : baseEnd_4132675 < baseStart_4132675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132690 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_4132690 : Nat := 118140960795 + 4132690 * 2 ^ 59
def prefixEnd_4132690 : Nat := 4983230072969 + 3 ^ 40 * 4132690 * 2
def baseEnd_4132690 : Nat := 1414704244019694043379407

theorem tailTrace_4132690 : CollatzResearch.WordTrace tailWord_4132690 prefixEnd_4132690 1414704244019694043379407 := by
  unfold tailWord_4132690
  simp only [CollatzResearch.WordTrace]
  refine ⟨37682896849494353026230881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100487724931984941403282349 37682896849494353026230881)
  ·
    refine ⟨28262172637120764769673161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37682896849494353026230881 28262172637120764769673161)
    ·
      refine ⟨21196629477840573577254871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28262172637120764769673161 21196629477840573577254871)
      ·
        refine ⟨31794944216760860365882307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21196629477840573577254871 31794944216760860365882307)
        ·
          refine ⟨47692416325141290548823461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31794944216760860365882307 47692416325141290548823461)
          ·
            refine ⟨8942328060963991977904399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47692416325141290548823461 8942328060963991977904399)
            ·
              refine ⟨13413492091445987966856599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8942328060963991977904399 13413492091445987966856599)
              ·
                refine ⟨20120238137168981950284899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13413492091445987966856599 20120238137168981950284899)
                ·
                  refine ⟨30180357205753472925427349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20120238137168981950284899 30180357205753472925427349)
                  ·
                    refine ⟨1414704244019694043379407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30180357205753472925427349 1414704244019694043379407)
                    ·
                      rfl

theorem cell22_4132690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_4132690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132690 prefixEnd_4132690 := by exact prefixLift 4132690
  have htrace : WordTrace (prefixWord ++ tailWord_4132690) baseStart_4132690 baseEnd_4132690 := by
    simpa [prefixWord, tailWord_4132690, baseEnd_4132690] using wordTrace_append hprefix tailTrace_4132690
  have hstable : (prefixWord ++ tailWord_4132690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132690).length < 2 ^ (prefixWord ++ tailWord_4132690).sum := by decide
  have hdescent : baseEnd_4132690 < baseStart_4132690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132726 : List Nat := [5, 1, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_4132726 : Nat := 118140960795 + 4132726 * 2 ^ 59
def prefixEnd_4132726 : Nat := 4983230072969 + 3 ^ 40 * 4132726 * 2
def baseEnd_4132726 : Nat := 1414716567555401949479297

theorem tailTrace_4132726 : CollatzResearch.WordTrace tailWord_4132726 prefixEnd_4132726 1414716567555401949479297 := by
  unfold tailWord_4132726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9420806276615436890827127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100488600283897993502156021 9420806276615436890827127)
  ·
    refine ⟨14131209414923155336240691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9420806276615436890827127 14131209414923155336240691)
    ·
      refine ⟨21196814122384733004361037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14131209414923155336240691 21196814122384733004361037)
      ·
        refine ⟨7948805295894274876635389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21196814122384733004361037 7948805295894274876635389)
        ·
          refine ⟨2980801985960353078738271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7948805295894274876635389 2980801985960353078738271)
          ·
            refine ⟨4471202978940529618107407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980801985960353078738271 4471202978940529618107407)
            ·
              refine ⟨6706804468410794427161111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471202978940529618107407 6706804468410794427161111)
              ·
                refine ⟨10060206702616191640741667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6706804468410794427161111 10060206702616191640741667)
                ·
                  refine ⟨15090310053924287461112501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10060206702616191640741667 15090310053924287461112501)
                  ·
                    refine ⟨1414716567555401949479297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15090310053924287461112501 1414716567555401949479297)
                    ·
                      rfl

theorem cell22_4132726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_4132726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132726 prefixEnd_4132726 := by exact prefixLift 4132726
  have htrace : WordTrace (prefixWord ++ tailWord_4132726) baseStart_4132726 baseEnd_4132726 := by
    simpa [prefixWord, tailWord_4132726, baseEnd_4132726] using wordTrace_append hprefix tailTrace_4132726
  have hstable : (prefixWord ++ tailWord_4132726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132726).length < 2 ^ (prefixWord ++ tailWord_4132726).sum := by decide
  have hdescent : baseEnd_4132726 < baseStart_4132726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132797 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_4132797 : Nat := 118140960795 + 4132797 * 2 ^ 59
def prefixEnd_4132797 : Nat := 4983230072969 + 3 ^ 40 * 4132797 * 2
def baseEnd_4132797 : Nat := 1414740872306381430954079

theorem tailTrace_4132797 : CollatzResearch.WordTrace tailWord_4132797 prefixEnd_4132797 1414740872306381430954079 := by
  unfold tailWord_4132797
  simp only [CollatzResearch.WordTrace]
  refine ⟨150735490008589769379068645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100490326672393179586045763 150735490008589769379068645)
  ·
    refine ⟨28262904376610581758575371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150735490008589769379068645 28262904376610581758575371)
    ·
      refine ⟨42394356564915872637863057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28262904376610581758575371 42394356564915872637863057)
      ·
        refine ⟨31795767423686904478397293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42394356564915872637863057 31795767423686904478397293)
        ·
          refine ⟨11923412783882589179398985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31795767423686904478397293 11923412783882589179398985)
          ·
            refine ⟨8942559587911941884549239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11923412783882589179398985 8942559587911941884549239)
            ·
              refine ⟨13413839381867912826823859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8942559587911941884549239 13413839381867912826823859)
              ·
                refine ⟨20120759072801869240235789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13413839381867912826823859 20120759072801869240235789)
                ·
                  refine ⟨7545284652300700965088421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20120759072801869240235789 7545284652300700965088421)
                  ·
                    refine ⟨1414740872306381430954079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7545284652300700965088421 1414740872306381430954079)
                    ·
                      rfl

theorem cell22_4132797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_4132797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132797 prefixEnd_4132797 := by exact prefixLift 4132797
  have htrace : WordTrace (prefixWord ++ tailWord_4132797) baseStart_4132797 baseEnd_4132797 := by
    simpa [prefixWord, tailWord_4132797, baseEnd_4132797] using wordTrace_append hprefix tailTrace_4132797
  have hstable : (prefixWord ++ tailWord_4132797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132797).length < 2 ^ (prefixWord ++ tailWord_4132797).sum := by decide
  have hdescent : baseEnd_4132797 < baseStart_4132797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132810 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 3, 5]
def baseStart_4132810 : Nat := 118140960795 + 4132810 * 2 ^ 59
def prefixEnd_4132810 : Nat := 4983230072969 + 3 ^ 40 * 4132810 * 2
def baseEnd_4132810 : Nat := 1414745322472053730379039

theorem tailTrace_4132810 : CollatzResearch.WordTrace tailWord_4132810 prefixEnd_4132810 1414745322472053730379039 := by
  unfold tailWord_4132810
  simp only [CollatzResearch.WordTrace]
  refine ⟨37683991039385668149822971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100490642771695115066194589 37683991039385668149822971)
  ·
    refine ⟨56525986559078502224734457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37683991039385668149822971 56525986559078502224734457)
    ·
      refine ⟨42394489919308876668550843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56525986559078502224734457 42394489919308876668550843)
      ·
        refine ⟨63591734878963315002826265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42394489919308876668550843 63591734878963315002826265)
        ·
          refine ⟨47693801159222486252119699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63591734878963315002826265 47693801159222486252119699)
          ·
            refine ⟨71540701738833729378179549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47693801159222486252119699 71540701738833729378179549)
            ·
              refine ⟨26827763152062648516817331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71540701738833729378179549 26827763152062648516817331)
              ·
                refine ⟨40241644728093972775225997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26827763152062648516817331 40241644728093972775225997)
                ·
                  refine ⟨15090616773035239790709749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40241644728093972775225997 15090616773035239790709749)
                  ·
                    refine ⟨1414745322472053730379039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15090616773035239790709749 1414745322472053730379039)
                    ·
                      rfl

theorem cell22_4132810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_4132810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132810 prefixEnd_4132810 := by exact prefixLift 4132810
  have htrace : WordTrace (prefixWord ++ tailWord_4132810) baseStart_4132810 baseEnd_4132810 := by
    simpa [prefixWord, tailWord_4132810, baseEnd_4132810] using wordTrace_append hprefix tailTrace_4132810
  have hstable : (prefixWord ++ tailWord_4132810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132810).length < 2 ^ (prefixWord ++ tailWord_4132810).sum := by decide
  have hdescent : baseEnd_4132810 < baseStart_4132810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132814 : List Nat := [4, 1, 1, 1, 2, 2, 5, 1, 1, 4]
def baseStart_4132814 : Nat := 118140960795 + 4132814 * 2 ^ 59
def prefixEnd_4132814 : Nat := 4983230072969 + 3 ^ 40 * 4132814 * 2
def baseEnd_4132814 : Nat := 1414746691753799053279027

theorem tailTrace_4132814 : CollatzResearch.WordTrace tailWord_4132814 prefixEnd_4132814 1414746691753799053279027 := by
  unfold tailWord_4132814
  simp only [CollatzResearch.WordTrace]
  refine ⟨18842013756191022660304687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100490740033018787521624997 18842013756191022660304687)
  ·
    refine ⟨28263020634286533990457031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18842013756191022660304687 28263020634286533990457031)
    ·
      refine ⟨42394530951429800985685547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28263020634286533990457031 42394530951429800985685547)
      ·
        refine ⟨63591796427144701478528321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42394530951429800985685547 63591796427144701478528321)
        ·
          refine ⟨47693847320358526108896241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63591796427144701478528321 47693847320358526108896241)
          ·
            refine ⟨35770385490268894581672181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47693847320358526108896241 35770385490268894581672181)
            ·
              refine ⟨3353473639712708867031767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35770385490268894581672181 3353473639712708867031767)
              ·
                refine ⟨5030210459569063300547651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3353473639712708867031767 5030210459569063300547651)
                ·
                  refine ⟨7545315689353594950821477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5030210459569063300547651 7545315689353594950821477)
                  ·
                    refine ⟨1414746691753799053279027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7545315689353594950821477 1414746691753799053279027)
                    ·
                      rfl

theorem cell22_4132814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_4132814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132814 prefixEnd_4132814 := by exact prefixLift 4132814
  have htrace : WordTrace (prefixWord ++ tailWord_4132814) baseStart_4132814 baseEnd_4132814 := by
    simpa [prefixWord, tailWord_4132814, baseEnd_4132814] using wordTrace_append hprefix tailTrace_4132814
  have hstable : (prefixWord ++ tailWord_4132814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132814).length < 2 ^ (prefixWord ++ tailWord_4132814).sum := by decide
  have hdescent : baseEnd_4132814 < baseStart_4132814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132822 : List Nat := [5, 2, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_4132822 : Nat := 118140960795 + 4132822 * 2 ^ 59
def prefixEnd_4132822 : Nat := 4983230072969 + 3 ^ 40 * 4132822 * 2
def baseEnd_4132822 : Nat := 1414749430317289699079003

theorem tailTrace_4132822 : CollatzResearch.WordTrace tailWord_4132822 prefixEnd_4132822 1414749430317289699079003 := by
  unfold tailWord_4132822
  simp only [CollatzResearch.WordTrace]
  refine ⟨9421025114593699915545545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100490934555666132432485813 9421025114593699915545545)
  ·
    refine ⟨7065768835945274936659159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9421025114593699915545545 7065768835945274936659159)
    ·
      refine ⟨10598653253917912404988739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7065768835945274936659159 10598653253917912404988739)
      ·
        refine ⟨15897979880876868607483109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10598653253917912404988739 15897979880876868607483109)
        ·
          refine ⟨2980871227664412863903083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15897979880876868607483109 2980871227664412863903083)
          ·
            refine ⟨4471306841496619295854625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980871227664412863903083 4471306841496619295854625)
            ·
              refine ⟨3353480131122464471890969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4471306841496619295854625 3353480131122464471890969)
              ·
                refine ⟨2515110098341848353918227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3353480131122464471890969 2515110098341848353918227)
                ·
                  refine ⟨3772665147512772530877341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515110098341848353918227 3772665147512772530877341)
                  ·
                    refine ⟨1414749430317289699079003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3772665147512772530877341 1414749430317289699079003)
                    ·
                      rfl

theorem cell22_4132822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_4132822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132822 prefixEnd_4132822 := by exact prefixLift 4132822
  have htrace : WordTrace (prefixWord ++ tailWord_4132822) baseStart_4132822 baseEnd_4132822 := by
    simpa [prefixWord, tailWord_4132822, baseEnd_4132822] using wordTrace_append hprefix tailTrace_4132822
  have hstable : (prefixWord ++ tailWord_4132822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132822).length < 2 ^ (prefixWord ++ tailWord_4132822).sum := by decide
  have hdescent : baseEnd_4132822 < baseStart_4132822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132857 : List Nat := [1, 2, 1, 3, 1, 5, 3, 6]
def baseStart_4132857 : Nat := 118140960795 + 4132857 * 2 ^ 59
def prefixEnd_4132857 : Nat := 4983230072969 + 3 ^ 40 * 4132857 * 2
def baseEnd_4132857 : Nat := 157195712392506808272655

theorem tailTrace_4132857 : CollatzResearch.WordTrace tailWord_4132857 prefixEnd_4132857 157195712392506808272655 := by
  unfold tailWord_4132857
  simp only [CollatzResearch.WordTrace]
  refine ⟨150737678388372399626252825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100491785592248266417501883 150737678388372399626252825)
  ·
    refine ⟨113053258791279299719689619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150737678388372399626252825 113053258791279299719689619)
    ·
      refine ⟨169579888186918949579534429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113053258791279299719689619 169579888186918949579534429)
      ·
        refine ⟨63592458070094606092325411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169579888186918949579534429 63592458070094606092325411)
        ·
          refine ⟨95388687105141909138488117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63592458070094606092325411 95388687105141909138488117)
          ·
            refine ⟨8942689416107053981733261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95388687105141909138488117 8942689416107053981733261)
            ·
              refine ⟨3353508531040145243149973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8942689416107053981733261 3353508531040145243149973)
              ·
                refine ⟨157195712392506808272655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3353508531040145243149973 157195712392506808272655)
                ·
                  rfl

theorem cell22_4132857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 6].length) (baseStart_4132857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132857 prefixEnd_4132857 := by exact prefixLift 4132857
  have htrace : WordTrace (prefixWord ++ tailWord_4132857) baseStart_4132857 baseEnd_4132857 := by
    simpa [prefixWord, tailWord_4132857, baseEnd_4132857] using wordTrace_append hprefix tailTrace_4132857
  have hstable : (prefixWord ++ tailWord_4132857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132857).length < 2 ^ (prefixWord ++ tailWord_4132857).sum := by decide
  have hdescent : baseEnd_4132857 < baseStart_4132857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132872 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 5, 3]
def baseStart_4132872 : Nat := 118140960795 + 4132872 * 2 ^ 59
def prefixEnd_4132872 : Nat := 4983230072969 + 3 ^ 40 * 4132872 * 2
def baseEnd_4132872 : Nat := 1414766546339106235328849

theorem tailTrace_4132872 : CollatzResearch.WordTrace tailWord_4132872 prefixEnd_4132872 1414766546339106235328849 := by
  unfold tailWord_4132872
  simp only [CollatzResearch.WordTrace]
  refine ⟨75369112741659028594024435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100492150322212038125365913 75369112741659028594024435)
  ·
    refine ⟨113053669112488542891036653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75369112741659028594024435 113053669112488542891036653)
    ·
      refine ⟨42395125917183203584138745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113053669112488542891036653 42395125917183203584138745)
      ·
        refine ⟨31796344437887402688104059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42395125917183203584138745 31796344437887402688104059)
        ·
          refine ⟨47694516656831104032156089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31796344437887402688104059 47694516656831104032156089)
          ·
            refine ⟨35770887492623328024117067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47694516656831104032156089 35770887492623328024117067)
            ·
              refine ⟨53656331238934992036175601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35770887492623328024117067 53656331238934992036175601)
              ·
                refine ⟨40242248429201244027131701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53656331238934992036175601 40242248429201244027131701)
                ·
                  refine ⟨3772710790237616627543597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40242248429201244027131701 3772710790237616627543597)
                  ·
                    refine ⟨1414766546339106235328849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3772710790237616627543597 1414766546339106235328849)
                    ·
                      rfl

theorem cell22_4132872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_4132872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132872 prefixEnd_4132872 := by exact prefixLift 4132872
  have htrace : WordTrace (prefixWord ++ tailWord_4132872) baseStart_4132872 baseEnd_4132872 := by
    simpa [prefixWord, tailWord_4132872, baseEnd_4132872] using wordTrace_append hprefix tailTrace_4132872
  have hstable : (prefixWord ++ tailWord_4132872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132872).length < 2 ^ (prefixWord ++ tailWord_4132872).sum := by decide
  have hdescent : baseEnd_4132872 < baseStart_4132872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4132996 : List Nat := [2, 3, 2, 1, 2, 1, 4, 2, 2, 3]
def baseStart_4132996 : Nat := 118140960795 + 4132996 * 2 ^ 59
def prefixEnd_4132996 : Nat := 4983230072969 + 3 ^ 40 * 4132996 * 2
def baseEnd_4132996 : Nat := 1414808994073211245228469

theorem tailTrace_4132996 : CollatzResearch.WordTrace tailWord_4132996 prefixEnd_4132996 1414808994073211245228469 := by
  unfold tailWord_4132996
  simp only [CollatzResearch.WordTrace]
  refine ⟨75371374067434413182781421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100495165423245884243708561 75371374067434413182781421)
  ·
    refine ⟨28264265275287904943543033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75371374067434413182781421 28264265275287904943543033)
    ·
      refine ⟨21198198956465928707657275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28264265275287904943543033 21198198956465928707657275)
      ·
        refine ⟨31797298434698893061485913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21198198956465928707657275 31797298434698893061485913)
        ·
          refine ⟨23847973826024169796114435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31797298434698893061485913 23847973826024169796114435)
          ·
            refine ⟨35771960739036254694171653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23847973826024169796114435 35771960739036254694171653)
            ·
              refine ⟨6707242638569297755157185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35771960739036254694171653 6707242638569297755157185)
              ·
                refine ⟨5030431978926973316367889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6707242638569297755157185 5030431978926973316367889)
                ·
                  refine ⟨3772823984195229987275917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5030431978926973316367889 3772823984195229987275917)
                  ·
                    refine ⟨1414808994073211245228469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3772823984195229987275917 1414808994073211245228469)
                    ·
                      rfl

theorem cell22_4132996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_4132996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4132996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4132996 prefixEnd_4132996 := by exact prefixLift 4132996
  have htrace : WordTrace (prefixWord ++ tailWord_4132996) baseStart_4132996 baseEnd_4132996 := by
    simpa [prefixWord, tailWord_4132996, baseEnd_4132996] using wordTrace_append hprefix tailTrace_4132996
  have hstable : (prefixWord ++ tailWord_4132996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4132996).length < 2 ^ (prefixWord ++ tailWord_4132996).sum := by decide
  have hdescent : baseEnd_4132996 < baseStart_4132996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4132996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133024 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 5, 3]
def baseStart_4133024 : Nat := 118140960795 + 4133024 * 2 ^ 59
def prefixEnd_4133024 : Nat := 4983230072969 + 3 ^ 40 * 4133024 * 2
def baseEnd_4133024 : Nat := 1414818579045428505528383

theorem tailTrace_4133024 : CollatzResearch.WordTrace tailWord_4133024 prefixEnd_4133024 1414818579045428505528383 := by
  unfold tailWord_4133024
  simp only [CollatzResearch.WordTrace]
  refine ⟨75371884689383693573791063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100495846252511591431721417 75371884689383693573791063)
  ·
    refine ⟨113057827034075540360686595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75371884689383693573791063 113057827034075540360686595)
    ·
      refine ⟨169586740551113310541029893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113057827034075540360686595 169586740551113310541029893)
      ·
        refine ⟨31797513853333745726443105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169586740551113310541029893 31797513853333745726443105)
        ·
          refine ⟨23848135390000309294832329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31797513853333745726443105 23848135390000309294832329)
          ·
            refine ⟨17886101542500231971124247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23848135390000309294832329 17886101542500231971124247)
            ·
              refine ⟨26829152313750347956686371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17886101542500231971124247 26829152313750347956686371)
              ·
                refine ⟨40243728470625521935029557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26829152313750347956686371 40243728470625521935029557)
                ·
                  refine ⟨3772849544121142681409021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40243728470625521935029557 3772849544121142681409021)
                  ·
                    refine ⟨1414818579045428505528383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3772849544121142681409021 1414818579045428505528383)
                    ·
                      rfl

theorem cell22_4133024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 5, 3].length) (baseStart_4133024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133024 prefixEnd_4133024 := by exact prefixLift 4133024
  have htrace : WordTrace (prefixWord ++ tailWord_4133024) baseStart_4133024 baseEnd_4133024 := by
    simpa [prefixWord, tailWord_4133024, baseEnd_4133024] using wordTrace_append hprefix tailTrace_4133024
  have hstable : (prefixWord ++ tailWord_4133024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133024).length < 2 ^ (prefixWord ++ tailWord_4133024).sum := by decide
  have hdescent : baseEnd_4133024 < baseStart_4133024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133026 : List Nat := [3, 3, 1, 3, 1, 2, 3, 6]
def baseStart_4133026 : Nat := 118140960795 + 4133026 * 2 ^ 59
def prefixEnd_4133026 : Nat := 4983230072969 + 3 ^ 40 * 4133026 * 2
def baseEnd_4133026 : Nat := 157202140409589018553153

theorem tailTrace_4133026 : CollatzResearch.WordTrace tailWord_4133026 prefixEnd_4133026 157202140409589018553153 := by
  unfold tailWord_4133026
  simp only [CollatzResearch.WordTrace]
  refine ⟨37685960581190035372288733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100495894883173427659436621 37685960581190035372288733)
  ·
    refine ⟨14132235217946263264608275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37685960581190035372288733 14132235217946263264608275)
    ·
      refine ⟨21198352826919394896912413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14132235217946263264608275 21198352826919394896912413)
      ·
        refine ⟨7949382310094773086342155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21198352826919394896912413 7949382310094773086342155)
        ·
          refine ⟨11924073465142159629513233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7949382310094773086342155 11924073465142159629513233)
          ·
            refine ⟨8943055098856619722134925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11924073465142159629513233 8943055098856619722134925)
            ·
              refine ⟨3353645662071232395800597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8943055098856619722134925 3353645662071232395800597)
              ·
                refine ⟨157202140409589018553153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3353645662071232395800597 157202140409589018553153)
                ·
                  rfl

theorem cell22_4133026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 6].length) (baseStart_4133026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133026 prefixEnd_4133026 := by exact prefixLift 4133026
  have htrace : WordTrace (prefixWord ++ tailWord_4133026) baseStart_4133026 baseEnd_4133026 := by
    simpa [prefixWord, tailWord_4133026, baseEnd_4133026] using wordTrace_append hprefix tailTrace_4133026
  have hstable : (prefixWord ++ tailWord_4133026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133026).length < 2 ^ (prefixWord ++ tailWord_4133026).sum := by decide
  have hdescent : baseEnd_4133026 < baseStart_4133026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133028 : List Nat := [2, 3, 1, 2, 5, 1, 1, 1, 2, 4]
def baseStart_4133028 : Nat := 118140960795 + 4133028 * 2 ^ 59
def prefixEnd_4133028 : Nat := 4983230072969 + 3 ^ 40 * 4133028 * 2
def baseEnd_4133028 : Nat := 1414819948327173828428371

theorem tailTrace_4133028 : CollatzResearch.WordTrace tailWord_4133028 prefixEnd_4133028 1414819948327173828428371 := by
  unfold tailWord_4133028
  simp only [CollatzResearch.WordTrace]
  refine ⟨75371957635376447915363869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100495943513835263887151825 75371957635376447915363869)
  ·
    refine ⟨28264484113266167968261451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75371957635376447915363869 28264484113266167968261451)
    ·
      refine ⟨42396726169899251952392177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28264484113266167968261451 42396726169899251952392177)
      ·
        refine ⟨31797544627424438964294133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42396726169899251952392177 31797544627424438964294133)
        ·
          refine ⟨2981019808821041152902575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31797544627424438964294133 2981019808821041152902575)
          ·
            refine ⟨4471529713231561729353863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2981019808821041152902575 4471529713231561729353863)
            ·
              refine ⟨6707294569847342594030795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471529713231561729353863 6707294569847342594030795)
              ·
                refine ⟨10060941854771013891046193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6707294569847342594030795 10060941854771013891046193)
                ·
                  refine ⟨7545706391078260418284645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10060941854771013891046193 7545706391078260418284645)
                  ·
                    refine ⟨1414819948327173828428371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7545706391078260418284645 1414819948327173828428371)
                    ·
                      rfl

theorem cell22_4133028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_4133028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133028 prefixEnd_4133028 := by exact prefixLift 4133028
  have htrace : WordTrace (prefixWord ++ tailWord_4133028) baseStart_4133028 baseEnd_4133028 := by
    simpa [prefixWord, tailWord_4133028, baseEnd_4133028] using wordTrace_append hprefix tailTrace_4133028
  have hstable : (prefixWord ++ tailWord_4133028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133028).length < 2 ^ (prefixWord ++ tailWord_4133028).sum := by decide
  have hdescent : baseEnd_4133028 < baseStart_4133028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133116 : List Nat := [2, 2, 2, 1, 4, 3, 1, 1, 6]
def baseStart_4133116 : Nat := 118140960795 + 4133116 * 2 ^ 59
def prefixEnd_4133116 : Nat := 4983230072969 + 3 ^ 40 * 4133116 * 2
def baseEnd_4133116 : Nat := 471616690841856977409367

theorem tailTrace_4133116 : CollatzResearch.WordTrace tailWord_4133116 prefixEnd_4133116 471616690841856977409367 := by
  unfold tailWord_4133116
  simp only [CollatzResearch.WordTrace]
  refine ⟨75373562447217043429965601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100498083262956057906620801 75373562447217043429965601)
  ·
    refine ⟨56530171835412782572474201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75373562447217043429965601 56530171835412782572474201)
    ·
      refine ⟨42397628876559586929355651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56530171835412782572474201 42397628876559586929355651)
      ·
        refine ⟨63596443314839380394033477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42397628876559586929355651 63596443314839380394033477)
        ·
          refine ⟨11924333121532383823881277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63596443314839380394033477 11924333121532383823881277)
          ·
            refine ⟨4471624920574643933955479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11924333121532383823881277 4471624920574643933955479)
            ·
              refine ⟨6707437380861965900933219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471624920574643933955479 6707437380861965900933219)
              ·
                refine ⟨10061156071292948851399829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6707437380861965900933219 10061156071292948851399829)
                ·
                  refine ⟨471616690841856977409367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10061156071292948851399829 471616690841856977409367)
                  ·
                    rfl

theorem cell22_4133116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_4133116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133116 prefixEnd_4133116 := by exact prefixLift 4133116
  have htrace : WordTrace (prefixWord ++ tailWord_4133116) baseStart_4133116 baseEnd_4133116 := by
    simpa [prefixWord, tailWord_4133116, baseEnd_4133116] using wordTrace_append hprefix tailTrace_4133116
  have hstable : (prefixWord ++ tailWord_4133116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133116).length < 2 ^ (prefixWord ++ tailWord_4133116).sum := by decide
  have hdescent : baseEnd_4133116 < baseStart_4133116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133131 : List Nat := [1, 1, 1, 1, 5, 2, 3, 3, 2, 3]
def baseStart_4133131 : Nat := 118140960795 + 4133131 * 2 ^ 59
def prefixEnd_4133131 : Nat := 4983230072969 + 3 ^ 40 * 4133131 * 2
def baseEnd_4133131 : Nat := 1414855207332115893103055

theorem tailTrace_4133131 : CollatzResearch.WordTrace tailWord_4133131 prefixEnd_4133131 1414855207332115893103055 := by
  unfold tailWord_4133131
  simp only [CollatzResearch.WordTrace]
  refine ⟨150747671989379744421727247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100498447992919829614484831 150747671989379744421727247)
  ·
    refine ⟨226121507984069616632590871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150747671989379744421727247 226121507984069616632590871)
    ·
      refine ⟨339182261976104424948886307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226121507984069616632590871 339182261976104424948886307)
      ·
        refine ⟨508773392964156637423329461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339182261976104424948886307 508773392964156637423329461)
        ·
          refine ⟨47697505590389684758437137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 508773392964156637423329461 47697505590389684758437137)
          ·
            refine ⟨35773129192792263568827853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47697505590389684758437137 35773129192792263568827853)
            ·
              refine ⟨13414923447297098838310445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35773129192792263568827853 13414923447297098838310445)
              ·
                refine ⟨5030596292736412064366417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13414923447297098838310445 5030596292736412064366417)
                ·
                  refine ⟨3772947219552309048274813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5030596292736412064366417 3772947219552309048274813)
                  ·
                    refine ⟨1414855207332115893103055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3772947219552309048274813 1414855207332115893103055)
                    ·
                      rfl

theorem cell22_4133131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 3].length) (baseStart_4133131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133131 prefixEnd_4133131 := by exact prefixLift 4133131
  have htrace : WordTrace (prefixWord ++ tailWord_4133131) baseStart_4133131 baseEnd_4133131 := by
    simpa [prefixWord, tailWord_4133131, baseEnd_4133131] using wordTrace_append hprefix tailTrace_4133131
  have hstable : (prefixWord ++ tailWord_4133131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133131).length < 2 ^ (prefixWord ++ tailWord_4133131).sum := by decide
  have hdescent : baseEnd_4133131 < baseStart_4133131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133223 : List Nat := [1, 1, 5, 1, 3, 3, 1, 2, 5]
def baseStart_4133223 : Nat := 118140960795 + 4133223 * 2 ^ 59
def prefixEnd_4133223 : Nat := 4983230072969 + 3 ^ 40 * 4133223 * 2
def baseEnd_4133223 : Nat := 471628900270752773267591

theorem tailTrace_4133223 : CollatzResearch.WordTrace tailWord_4133223 prefixEnd_4133223 471628900270752773267591 := by
  unfold tailWord_4133223
  simp only [CollatzResearch.WordTrace]
  refine ⟨150751027505046444134076323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100500685003364296089384215 150751027505046444134076323)
  ·
    refine ⟨226126541257569666201114485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150751027505046444134076323 226126541257569666201114485)
    ·
      refine ⟨21199363242897156206354483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226126541257569666201114485 21199363242897156206354483)
      ·
        refine ⟨31799044864345734309531725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21199363242897156206354483 31799044864345734309531725)
        ·
          refine ⟨11924641824129650366074397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31799044864345734309531725 11924641824129650366074397)
          ·
            refine ⟨4471740684048618887277899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11924641824129650366074397 4471740684048618887277899)
            ·
              refine ⟨6707611026072928330916849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471740684048618887277899 6707611026072928330916849)
              ·
                refine ⟨5030708269554696248187637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6707611026072928330916849 5030708269554696248187637)
                ·
                  refine ⟨471628900270752773267591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5030708269554696248187637 471628900270752773267591)
                  ·
                    rfl

theorem cell22_4133223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 5].length) (baseStart_4133223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133223 prefixEnd_4133223 := by exact prefixLift 4133223
  have htrace : WordTrace (prefixWord ++ tailWord_4133223) baseStart_4133223 baseEnd_4133223 := by
    simpa [prefixWord, tailWord_4133223, baseEnd_4133223] using wordTrace_append hprefix tailTrace_4133223
  have hstable : (prefixWord ++ tailWord_4133223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133223).length < 2 ^ (prefixWord ++ tailWord_4133223).sum := by decide
  have hdescent : baseEnd_4133223 < baseStart_4133223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133345 : List Nat := [1, 2, 3, 1, 2, 2, 3, 4, 1, 3]
def baseStart_4133345 : Nat := 118140960795 + 4133345 * 2 ^ 59
def prefixEnd_4133345 : Nat := 4983230072969 + 3 ^ 40 * 4133345 * 2
def baseEnd_4133345 : Nat := 1414928463905490668252399

theorem tailTrace_4133345 : CollatzResearch.WordTrace tailWord_4133345 prefixEnd_4133345 1414928463905490668252399 := by
  unfold tailWord_4133345
  simp only [CollatzResearch.WordTrace]
  refine ⟨150755477210604458970017489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100503651473736305980011659 150755477210604458970017489)
  ·
    refine ⟨113066607907953344227513117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150755477210604458970017489 113066607907953344227513117)
    ·
      refine ⟨42399977965482504085317419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113066607907953344227513117 42399977965482504085317419)
      ·
        refine ⟨63599966948223756127976129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42399977965482504085317419 63599966948223756127976129)
        ·
          refine ⟨47699975211167817095982097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63599966948223756127976129 47699975211167817095982097)
          ·
            refine ⟨35774981408375862821986573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47699975211167817095982097 35774981408375862821986573)
            ·
              refine ⟨13415618028140948558244965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35774981408375862821986573 13415618028140948558244965)
              ·
                refine ⟨2515428380276427854670931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13415618028140948558244965 2515428380276427854670931)
                ·
                  refine ⟨3773142570414641782006397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515428380276427854670931 3773142570414641782006397)
                  ·
                    refine ⟨1414928463905490668252399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3773142570414641782006397 1414928463905490668252399)
                    ·
                      rfl

theorem cell22_4133345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_4133345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133345 prefixEnd_4133345 := by exact prefixLift 4133345
  have htrace : WordTrace (prefixWord ++ tailWord_4133345) baseStart_4133345 baseEnd_4133345 := by
    simpa [prefixWord, tailWord_4133345, baseEnd_4133345] using wordTrace_append hprefix tailTrace_4133345
  have hstable : (prefixWord ++ tailWord_4133345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133345).length < 2 ^ (prefixWord ++ tailWord_4133345).sum := by decide
  have hdescent : baseEnd_4133345 < baseStart_4133345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133356 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 2, 5]
def baseStart_4133356 : Nat := 118140960795 + 4133356 * 2 ^ 59
def prefixEnd_4133356 : Nat := 4983230072969 + 3 ^ 40 * 4133356 * 2
def baseEnd_4133356 : Nat := 1414932229430290306227365

theorem tailTrace_4133356 : CollatzResearch.WordTrace tailWord_4133356 prefixEnd_4133356 1414932229430290306227365 := by
  unfold tailWord_4133356
  simp only [CollatzResearch.WordTrace]
  refine ⟨75377939206782303924333961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100503918942376405232445281 75377939206782303924333961)
  ·
    refine ⟨56533454405086727943250471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75377939206782303924333961 56533454405086727943250471)
    ·
      refine ⟨84800181607630091914875707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56533454405086727943250471 84800181607630091914875707)
      ·
        refine ⟨127200272411445137872313561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84800181607630091914875707 127200272411445137872313561)
        ·
          refine ⟨95400204308583853404235171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127200272411445137872313561 95400204308583853404235171)
          ·
            refine ⟨143100306462875780106352757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95400204308583853404235171 143100306462875780106352757)
            ·
              refine ⟨13415653730894604384970571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143100306462875780106352757 13415653730894604384970571)
              ·
                refine ⟨20123480596341906577455857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13415653730894604384970571 20123480596341906577455857)
                ·
                  refine ⟨15092610447256429933091893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20123480596341906577455857 15092610447256429933091893)
                  ·
                    refine ⟨1414932229430290306227365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15092610447256429933091893 1414932229430290306227365)
                    ·
                      rfl

theorem cell22_4133356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_4133356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133356 prefixEnd_4133356 := by exact prefixLift 4133356
  have htrace : WordTrace (prefixWord ++ tailWord_4133356) baseStart_4133356 baseEnd_4133356 := by
    simpa [prefixWord, tailWord_4133356, baseEnd_4133356] using wordTrace_append hprefix tailTrace_4133356
  have hstable : (prefixWord ++ tailWord_4133356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133356).length < 2 ^ (prefixWord ++ tailWord_4133356).sum := by decide
  have hdescent : baseEnd_4133356 < baseStart_4133356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133358 : List Nat := [4, 1, 2, 1, 2, 2, 2, 3, 5]
def baseStart_4133358 : Nat := 118140960795 + 4133358 * 2 ^ 59
def prefixEnd_4133358 : Nat := 4983230072969 + 3 ^ 40 * 4133358 * 2
def baseEnd_4133358 : Nat := 471644304690387655892453

theorem tailTrace_4133358 : CollatzResearch.WordTrace tailWord_4133358 prefixEnd_4133358 471644304690387655892453 := by
  unfold tailWord_4133358
  simp only [CollatzResearch.WordTrace]
  refine ⟨18844493919944670273780091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100503967573038241460160485 18844493919944670273780091)
  ·
    refine ⟨28266740879917005410670137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18844493919944670273780091 28266740879917005410670137)
    ·
      refine ⟨21200055659937754058002603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28266740879917005410670137 21200055659937754058002603)
      ·
        refine ⟨31800083489906631087003905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21200055659937754058002603 31800083489906631087003905)
        ·
          refine ⟨23850062617429973315252929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31800083489906631087003905 23850062617429973315252929)
          ·
            refine ⟨17887546963072479986439697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23850062617429973315252929 17887546963072479986439697)
            ·
              refine ⟨13415660222304359989829773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17887546963072479986439697 13415660222304359989829773)
              ·
                refine ⟨5030872583364134996186165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13415660222304359989829773 5030872583364134996186165)
                ·
                  refine ⟨471644304690387655892453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5030872583364134996186165 471644304690387655892453)
                  ·
                    rfl

theorem cell22_4133358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_4133358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133358 prefixEnd_4133358 := by exact prefixLift 4133358
  have htrace : WordTrace (prefixWord ++ tailWord_4133358) baseStart_4133358 baseEnd_4133358 := by
    simpa [prefixWord, tailWord_4133358, baseEnd_4133358] using wordTrace_append hprefix tailTrace_4133358
  have hstable : (prefixWord ++ tailWord_4133358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133358).length < 2 ^ (prefixWord ++ tailWord_4133358).sum := by decide
  have hdescent : baseEnd_4133358 < baseStart_4133358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133386 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 8]
def baseStart_4133386 : Nat := 118140960795 + 4133386 * 2 ^ 59
def prefixEnd_4133386 : Nat := 4983230072969 + 3 ^ 40 * 4133386 * 2
def baseEnd_4133386 : Nat := 471647499681126742659091

theorem tailTrace_4133386 : CollatzResearch.WordTrace tailWord_4133386 prefixEnd_4133386 471647499681126742659091 := by
  unfold tailWord_4133386
  simp only [CollatzResearch.WordTrace]
  refine ⟨37689243150863980743065003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100504648402303948648173341 37689243150863980743065003)
  ·
    refine ⟨56533864726295971114597505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37689243150863980743065003 56533864726295971114597505)
    ·
      refine ⟨42400398544721978335948129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56533864726295971114597505 42400398544721978335948129)
      ·
        refine ⟨31800298908541483751961097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42400398544721978335948129 31800298908541483751961097)
        ·
          refine ⟨23850224181406112813970823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31800298908541483751961097 23850224181406112813970823)
          ·
            refine ⟨35775336272109169220956235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23850224181406112813970823 35775336272109169220956235)
            ·
              refine ⟨53663004408163753831434353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35775336272109169220956235 53663004408163753831434353)
              ·
                refine ⟨40247253306122815373575765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53663004408163753831434353 40247253306122815373575765)
                ·
                  refine ⟨471647499681126742659091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40247253306122815373575765 471647499681126742659091)
                  ·
                    rfl

theorem cell22_4133386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_4133386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133386 prefixEnd_4133386 := by exact prefixLift 4133386
  have htrace : WordTrace (prefixWord ++ tailWord_4133386) baseStart_4133386 baseEnd_4133386 := by
    simpa [prefixWord, tailWord_4133386, baseEnd_4133386] using wordTrace_append hprefix tailTrace_4133386
  have hstable : (prefixWord ++ tailWord_4133386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133386).length < 2 ^ (prefixWord ++ tailWord_4133386).sum := by decide
  have hdescent : baseEnd_4133386 < baseStart_4133386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133422 : List Nat := [4, 1, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_4133422 : Nat := 118140960795 + 4133422 * 2 ^ 59
def prefixEnd_4133422 : Nat := 4983230072969 + 3 ^ 40 * 4133422 * 2
def baseEnd_4133422 : Nat := 1414954822579088134077163

theorem tailTrace_4133422 : CollatzResearch.WordTrace tailWord_4133422 prefixEnd_4133422 1414954822579088134077163 := by
  unfold tailWord_4133422
  simp only [CollatzResearch.WordTrace]
  refine ⟨18844785703915687640071315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100505523754217000747047013 18844785703915687640071315)
  ·
    refine ⟨28267178555873531460106973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18844785703915687640071315 28267178555873531460106973)
    ·
      refine ⟨10600191958452574297540115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28267178555873531460106973 10600191958452574297540115)
      ·
        refine ⟨15900287937678861446310173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10600191958452574297540115 15900287937678861446310173)
        ·
          refine ⟨5962607976629573042366315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15900287937678861446310173 5962607976629573042366315)
          ·
            refine ⟨8943911964944359563549473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5962607976629573042366315 8943911964944359563549473)
            ·
              refine ⟨6707933973708269672662105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8943911964944359563549473 6707933973708269672662105)
              ·
                refine ⟨5030950480281202254496579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6707933973708269672662105 5030950480281202254496579)
                ·
                  refine ⟨7546425720421803381744869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5030950480281202254496579 7546425720421803381744869)
                  ·
                    refine ⟨1414954822579088134077163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7546425720421803381744869 1414954822579088134077163)
                    ·
                      rfl

theorem cell22_4133422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_4133422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133422 prefixEnd_4133422 := by exact prefixLift 4133422
  have htrace : WordTrace (prefixWord ++ tailWord_4133422) baseStart_4133422 baseEnd_4133422 := by
    simpa [prefixWord, tailWord_4133422, baseEnd_4133422] using wordTrace_append hprefix tailTrace_4133422
  have hstable : (prefixWord ++ tailWord_4133422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133422).length < 2 ^ (prefixWord ++ tailWord_4133422).sum := by decide
  have hdescent : baseEnd_4133422 < baseStart_4133422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133431 : List Nat := [1, 1, 3, 1, 2, 3, 3, 8]
def baseStart_4133431 : Nat := 118140960795 + 4133431 * 2 ^ 59
def prefixEnd_4133431 : Nat := 4983230072969 + 3 ^ 40 * 4133431 * 2
def baseEnd_4133431 : Nat := 157217544829223901178015

theorem tailTrace_4133431 : CollatzResearch.WordTrace tailWord_4133431 prefixEnd_4133431 157217544829223901178015 := by
  unfold tailWord_4133431
  simp only [CollatzResearch.WordTrace]
  refine ⟨150758613888292895657648147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100505742592195263771765431 150758613888292895657648147)
  ·
    refine ⟨226137920832439343486472221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150758613888292895657648147 226137920832439343486472221)
    ·
      refine ⟨84801720312164753807427083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226137920832439343486472221 84801720312164753807427083)
      ·
        refine ⟨127202580468247130711140625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84801720312164753807427083 127202580468247130711140625)
        ·
          refine ⟨95401935351185348033355469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127202580468247130711140625 95401935351185348033355469)
          ·
            refine ⟨35775725756694505512508301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95401935351185348033355469 35775725756694505512508301)
            ·
              refine ⟨13415897158760439567190613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35775725756694505512508301 13415897158760439567190613)
              ·
                refine ⟨157217544829223901178015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13415897158760439567190613 157217544829223901178015)
                ·
                  rfl

theorem cell22_4133431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 8].length) (baseStart_4133431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133431 prefixEnd_4133431 := by exact prefixLift 4133431
  have htrace : WordTrace (prefixWord ++ tailWord_4133431) baseStart_4133431 baseEnd_4133431 := by
    simpa [prefixWord, tailWord_4133431, baseEnd_4133431] using wordTrace_append hprefix tailTrace_4133431
  have hstable : (prefixWord ++ tailWord_4133431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133431).length < 2 ^ (prefixWord ++ tailWord_4133431).sum := by decide
  have hdescent : baseEnd_4133431 < baseStart_4133431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133433 : List Nat := [1, 2, 1, 5, 1, 1, 2, 3, 2, 4]
def baseStart_4133433 : Nat := 118140960795 + 4133433 * 2 ^ 59
def prefixEnd_4133433 : Nat := 4983230072969 + 3 ^ 40 * 4133433 * 2
def baseEnd_4133433 : Nat := 1414958588103887772052129

theorem tailTrace_4133433 : CollatzResearch.WordTrace tailWord_4133433 prefixEnd_4133433 1414958588103887772052129 := by
  unfold tailWord_4133433
  simp only [CollatzResearch.WordTrace]
  refine ⟨150758686834285649999220953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100505791222857099999480635 150758686834285649999220953)
  ·
    refine ⟨113069015125714237499415715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150758686834285649999220953 113069015125714237499415715)
    ·
      refine ⟨169603522688571356249123573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113069015125714237499415715 169603522688571356249123573)
      ·
        refine ⟨15900330252053564648355335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169603522688571356249123573 15900330252053564648355335)
        ·
          refine ⟨23850495378080346972533003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15900330252053564648355335 23850495378080346972533003)
          ·
            refine ⟨35775743067120520458799505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23850495378080346972533003 35775743067120520458799505)
            ·
              refine ⟨26831807300340390344099629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35775743067120520458799505 26831807300340390344099629)
              ·
                refine ⟨10061927737627646379037361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26831807300340390344099629 10061927737627646379037361)
                ·
                  refine ⟨7546445803220734784278021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10061927737627646379037361 7546445803220734784278021)
                  ·
                    refine ⟨1414958588103887772052129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7546445803220734784278021 1414958588103887772052129)
                    ·
                      rfl

theorem cell22_4133433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_4133433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133433 prefixEnd_4133433 := by exact prefixLift 4133433
  have htrace : WordTrace (prefixWord ++ tailWord_4133433) baseStart_4133433 baseEnd_4133433 := by
    simpa [prefixWord, tailWord_4133433, baseEnd_4133433] using wordTrace_append hprefix tailTrace_4133433
  have hstable : (prefixWord ++ tailWord_4133433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133433).length < 2 ^ (prefixWord ++ tailWord_4133433).sum := by decide
  have hdescent : baseEnd_4133433 < baseStart_4133433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133437 : List Nat := [1, 4, 1, 3, 2, 3, 1, 3, 4]
def baseStart_4133437 : Nat := 118140960795 + 4133437 * 2 ^ 59
def prefixEnd_4133437 : Nat := 4983230072969 + 3 ^ 40 * 4133437 * 2
def baseEnd_4133437 : Nat := 471653319128544364984039

theorem tailTrace_4133437 : CollatzResearch.WordTrace tailWord_4133437 prefixEnd_4133437 471653319128544364984039 := by
  unfold tailWord_4133437
  simp only [CollatzResearch.WordTrace]
  refine ⟨150758832726271158682366565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100505888484180772454911043 150758832726271158682366565)
  ·
    refine ⟨28267281136175842252943731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150758832726271158682366565 28267281136175842252943731)
    ·
      refine ⟨42400921704263763379415597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28267281136175842252943731 42400921704263763379415597)
      ·
        refine ⟨15900345639098911267280849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42400921704263763379415597 15900345639098911267280849)
        ·
          refine ⟨11925259229324183450460637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15900345639098911267280849 11925259229324183450460637)
          ·
            refine ⟨4471972210996568793922739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11925259229324183450460637 4471972210996568793922739)
            ·
              refine ⟨6707958316494853190884109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471972210996568793922739 6707958316494853190884109)
              ·
                refine ⟨2515484368685569946581541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6707958316494853190884109 2515484368685569946581541)
                ·
                  refine ⟨471653319128544364984039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2515484368685569946581541 471653319128544364984039)
                  ·
                    rfl

theorem cell22_4133437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_4133437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133437 prefixEnd_4133437 := by exact prefixLift 4133437
  have htrace : WordTrace (prefixWord ++ tailWord_4133437) baseStart_4133437 baseEnd_4133437 := by
    simpa [prefixWord, tailWord_4133437, baseEnd_4133437] using wordTrace_append hprefix tailTrace_4133437
  have hstable : (prefixWord ++ tailWord_4133437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133437).length < 2 ^ (prefixWord ++ tailWord_4133437).sum := by decide
  have hdescent : baseEnd_4133437 < baseStart_4133437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133491 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 3, 7]
def baseStart_4133491 : Nat := 118140960795 + 4133491 * 2 ^ 59
def prefixEnd_4133491 : Nat := 4983230072969 + 3 ^ 40 * 4133491 * 2
def baseEnd_4133491 : Nat := 1414978442689194954101951

theorem tailTrace_4133491 : CollatzResearch.WordTrace tailWord_4133491 prefixEnd_4133491 1414978442689194954101951 := by
  unfold tailWord_4133491
  simp only [CollatzResearch.WordTrace]
  refine ⟨150760802268075525904832327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100507201512050350603221551 150760802268075525904832327)
  ·
    refine ⟨226141203402113288857248491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150760802268075525904832327 226141203402113288857248491)
    ·
      refine ⟨339211805103169933285872737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226141203402113288857248491 339211805103169933285872737)
      ·
        refine ⟨254408853827377449964404553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339211805103169933285872737 254408853827377449964404553)
        ·
          refine ⟨190806640370533087473303415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254408853827377449964404553 190806640370533087473303415)
          ·
            refine ⟨286209960555799631209955123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190806640370533087473303415 286209960555799631209955123)
            ·
              refine ⟨429314940833699446814932685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286209960555799631209955123 429314940833699446814932685)
              ·
                refine ⟨160993102812637292555599757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 429314940833699446814932685 160993102812637292555599757)
                ·
                  refine ⟨60372413554738984708349909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160993102812637292555599757 60372413554738984708349909)
                  ·
                    refine ⟨1414978442689194954101951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60372413554738984708349909 1414978442689194954101951)
                    ·
                      rfl

theorem cell22_4133491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 7].length) (baseStart_4133491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133491 prefixEnd_4133491 := by exact prefixLift 4133491
  have htrace : WordTrace (prefixWord ++ tailWord_4133491) baseStart_4133491 baseEnd_4133491 := by
    simpa [prefixWord, tailWord_4133491, baseEnd_4133491] using wordTrace_append hprefix tailTrace_4133491
  have hstable : (prefixWord ++ tailWord_4133491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133491).length < 2 ^ (prefixWord ++ tailWord_4133491).sum := by decide
  have hdescent : baseEnd_4133491 < baseStart_4133491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133514 : List Nat := [3, 1, 2, 3, 3, 1, 1, 4, 1, 3]
def baseStart_4133514 : Nat := 118140960795 + 4133514 * 2 ^ 59
def prefixEnd_4133514 : Nat := 4983230072969 + 3 ^ 40 * 4133514 * 2
def baseEnd_4133514 : Nat := 1414986316059230560776881

theorem tailTrace_4133514 : CollatzResearch.WordTrace tailWord_4133514 prefixEnd_4133514 1414986316059230560776881 := by
  unfold tailWord_4133514
  simp only [CollatzResearch.WordTrace]
  refine ⟨37690410286748050208229899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100507760764661467221946397 37690410286748050208229899)
  ·
    refine ⟨56535615430122075312344849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37690410286748050208229899 56535615430122075312344849)
    ·
      refine ⟨42401711572591556484258637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56535615430122075312344849 42401711572591556484258637)
      ·
        refine ⟨15900641839721833681596989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42401711572591556484258637 15900641839721833681596989)
        ·
          refine ⟨5962740689895687630598871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15900641839721833681596989 5962740689895687630598871)
          ·
            refine ⟨8944111034843531445898307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5962740689895687630598871 8944111034843531445898307)
            ·
              refine ⟨13416166552265297168847461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8944111034843531445898307 13416166552265297168847461)
              ·
                refine ⟨2515531228549743219158899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13416166552265297168847461 2515531228549743219158899)
                ·
                  refine ⟨3773296842824614828738349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515531228549743219158899 3773296842824614828738349)
                  ·
                    refine ⟨1414986316059230560776881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3773296842824614828738349 1414986316059230560776881)
                    ·
                      rfl

theorem cell22_4133514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_4133514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133514 prefixEnd_4133514 := by exact prefixLift 4133514
  have htrace : WordTrace (prefixWord ++ tailWord_4133514) baseStart_4133514 baseEnd_4133514 := by
    simpa [prefixWord, tailWord_4133514, baseEnd_4133514] using wordTrace_append hprefix tailTrace_4133514
  have hstable : (prefixWord ++ tailWord_4133514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133514).length < 2 ^ (prefixWord ++ tailWord_4133514).sum := by decide
  have hdescent : baseEnd_4133514 < baseStart_4133514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133540 : List Nat := [2, 3, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_4133540 : Nat := 118140960795 + 4133540 * 2 ^ 59
def prefixEnd_4133540 : Nat := 4983230072969 + 3 ^ 40 * 4133540 * 2
def baseEnd_4133540 : Nat := 1414995216390575159626801

theorem tailTrace_4133540 : CollatzResearch.WordTrace tailWord_4133540 prefixEnd_4133540 1414995216390575159626801 := by
  unfold tailWord_4133540
  simp only [CollatzResearch.WordTrace]
  refine ⟨75381294722449003636683037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100508392963265338182244049 75381294722449003636683037)
  ·
    refine ⟨28267985520918376363756139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75381294722449003636683037 28267985520918376363756139)
    ·
      refine ⟨42401978281377564545634209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28267985520918376363756139 42401978281377564545634209)
      ·
        refine ⟨31801483711033173409225657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42401978281377564545634209 31801483711033173409225657)
        ·
          refine ⟨23851112783274880056919243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31801483711033173409225657 23851112783274880056919243)
          ·
            refine ⟨35776669174912320085378865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23851112783274880056919243 35776669174912320085378865)
            ·
              refine ⟨26832501881184240064034149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35776669174912320085378865 26832501881184240064034149)
              ·
                refine ⟨5031094102722045012006403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26832501881184240064034149 5031094102722045012006403)
                ·
                  refine ⟨7546641154083067518009605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5031094102722045012006403 7546641154083067518009605)
                  ·
                    refine ⟨1414995216390575159626801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7546641154083067518009605 1414995216390575159626801)
                    ·
                      rfl

theorem cell22_4133540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_4133540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133540 prefixEnd_4133540 := by exact prefixLift 4133540
  have htrace : WordTrace (prefixWord ++ tailWord_4133540) baseStart_4133540 baseEnd_4133540 := by
    simpa [prefixWord, tailWord_4133540, baseEnd_4133540] using wordTrace_append hprefix tailTrace_4133540
  have hstable : (prefixWord ++ tailWord_4133540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133540).length < 2 ^ (prefixWord ++ tailWord_4133540).sum := by decide
  have hdescent : baseEnd_4133540 < baseStart_4133540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133555 : List Nat := [1, 1, 1, 2, 3, 4, 1, 5, 4]
def baseStart_4133555 : Nat := 118140960795 + 4133555 * 2 ^ 59
def prefixEnd_4133555 : Nat := 4983230072969 + 3 ^ 40 * 4133555 * 2
def baseEnd_4133555 : Nat := 471666783732373373500585

theorem tailTrace_4133555 : CollatzResearch.WordTrace tailWord_4133555 prefixEnd_4133555 471666783732373373500585 := by
  unfold tailWord_4133555
  simp only [CollatzResearch.WordTrace]
  refine ⟨150763136539843664835162119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100508757693229109890108079 150763136539843664835162119)
  ·
    refine ⟨226144704809765497252743179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150763136539843664835162119 226144704809765497252743179)
    ·
      refine ⟨339217057214648245879114769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226144704809765497252743179 339217057214648245879114769)
      ·
        refine ⟨254412792910986184409336077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339217057214648245879114769 254412792910986184409336077)
        ·
          refine ⟨95404797341619819153501029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254412792910986184409336077 95404797341619819153501029)
          ·
            refine ⟨17888399501553716091281443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95404797341619819153501029 17888399501553716091281443)
            ·
              refine ⟨26832599252330574136922165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17888399501553716091281443 26832599252330574136922165)
              ·
                refine ⟨2515556179905991325336453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26832599252330574136922165 2515556179905991325336453)
                ·
                  refine ⟨471666783732373373500585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2515556179905991325336453 471666783732373373500585)
                  ·
                    rfl

theorem cell22_4133555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 4].length) (baseStart_4133555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133555 prefixEnd_4133555 := by exact prefixLift 4133555
  have htrace : WordTrace (prefixWord ++ tailWord_4133555) baseStart_4133555 baseEnd_4133555 := by
    simpa [prefixWord, tailWord_4133555, baseEnd_4133555] using wordTrace_append hprefix tailTrace_4133555
  have hstable : (prefixWord ++ tailWord_4133555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133555).length < 2 ^ (prefixWord ++ tailWord_4133555).sum := by decide
  have hdescent : baseEnd_4133555 < baseStart_4133555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133557 : List Nat := [1, 3, 3, 3, 1, 2, 1, 3, 1, 4]
def baseStart_4133557 : Nat := 118140960795 + 4133557 * 2 ^ 59
def prefixEnd_4133557 : Nat := 4983230072969 + 3 ^ 40 * 4133557 * 2
def baseEnd_4133557 : Nat := 1415001035837992781951749

theorem tailTrace_4133557 : CollatzResearch.WordTrace tailWord_4133557 prefixEnd_4133557 1415001035837992781951749 := by
  unfold tailWord_4133557
  simp only [CollatzResearch.WordTrace]
  refine ⟨150763209485836419176734925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100508806323890946117823283 150763209485836419176734925)
  ·
    refine ⟨56536203557188657191275597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150763209485836419176734925 56536203557188657191275597)
    ·
      refine ⟨21201076333945746446728349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56536203557188657191275597 21201076333945746446728349)
      ·
        refine ⟨7950403625229654917523131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21201076333945746446728349 7950403625229654917523131)
        ·
          refine ⟨11925605437844482376284697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7950403625229654917523131 11925605437844482376284697)
          ·
            refine ⟨8944204078383361782213523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11925605437844482376284697 8944204078383361782213523)
            ·
              refine ⟨13416306117575042673320285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8944204078383361782213523 13416306117575042673320285)
              ·
                refine ⟨5031114794090641002495107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13416306117575042673320285 5031114794090641002495107)
                ·
                  refine ⟨7546672191135961503742661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5031114794090641002495107 7546672191135961503742661)
                  ·
                    refine ⟨1415001035837992781951749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7546672191135961503742661 1415001035837992781951749)
                    ·
                      rfl

theorem cell22_4133557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_4133557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133557 prefixEnd_4133557 := by exact prefixLift 4133557
  have htrace : WordTrace (prefixWord ++ tailWord_4133557) baseStart_4133557 baseEnd_4133557 := by
    simpa [prefixWord, tailWord_4133557, baseEnd_4133557] using wordTrace_append hprefix tailTrace_4133557
  have hstable : (prefixWord ++ tailWord_4133557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133557).length < 2 ^ (prefixWord ++ tailWord_4133557).sum := by decide
  have hdescent : baseEnd_4133557 < baseStart_4133557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133572 : List Nat := [2, 3, 3, 1, 1, 2, 2, 4, 4]
def baseStart_4133572 : Nat := 118140960795 + 4133572 * 2 ^ 59
def prefixEnd_4133572 : Nat := 4983230072969 + 3 ^ 40 * 4133572 * 2
def baseEnd_4133572 : Nat := 471668723548179247608901

theorem tailTrace_4133572 : CollatzResearch.WordTrace tailWord_4133572 prefixEnd_4133572 471668723548179247608901 := by
  unfold tailWord_4133572
  simp only [CollatzResearch.WordTrace]
  refine ⟨75381878290391038369265485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100509171053854717825687313 75381878290391038369265485)
  ·
    refine ⟨28268204358896639388474557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75381878290391038369265485 28268204358896639388474557)
    ·
      refine ⟨10600576634586239770677959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28268204358896639388474557 10600576634586239770677959)
      ·
        refine ⟨15900864951879359656016939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10600576634586239770677959 15900864951879359656016939)
        ·
          refine ⟨23851297427819039484025409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15900864951879359656016939 23851297427819039484025409)
          ·
            refine ⟨17888473070864279613019057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23851297427819039484025409 17888473070864279613019057)
            ·
              refine ⟨13416354803148209709764293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17888473070864279613019057 13416354803148209709764293)
              ·
                refine ⟨2515566525590289320580805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13416354803148209709764293 2515566525590289320580805)
                ·
                  refine ⟨471668723548179247608901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2515566525590289320580805 471668723548179247608901)
                  ·
                    rfl

theorem cell22_4133572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_4133572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133572 prefixEnd_4133572 := by exact prefixLift 4133572
  have htrace : WordTrace (prefixWord ++ tailWord_4133572) baseStart_4133572 baseEnd_4133572 := by
    simpa [prefixWord, tailWord_4133572, baseEnd_4133572] using wordTrace_append hprefix tailTrace_4133572
  have hstable : (prefixWord ++ tailWord_4133572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133572).length < 2 ^ (prefixWord ++ tailWord_4133572).sum := by decide
  have hdescent : baseEnd_4133572 < baseStart_4133572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133643 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 1, 7]
def baseStart_4133643 : Nat := 118140960795 + 4133643 * 2 ^ 59
def prefixEnd_4133643 : Nat := 4983230072969 + 3 ^ 40 * 4133643 * 2
def baseEnd_4133643 : Nat := 1415030475395517224301485

theorem tailTrace_4133643 : CollatzResearch.WordTrace tailWord_4133643 prefixEnd_4133643 1415030475395517224301485 := by
  unfold tailWord_4133643
  simp only [CollatzResearch.WordTrace]
  refine ⟨150766346163524855864365583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100510897442349903909577055 150766346163524855864365583)
  ·
    refine ⟨226149519245287283796548375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150766346163524855864365583 226149519245287283796548375)
    ·
      refine ⟨339224278867930925694822563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226149519245287283796548375 339224278867930925694822563)
      ·
        refine ⟨508836418301896388542233845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339224278867930925694822563 508836418301896388542233845)
        ·
          refine ⟨47703414215802786425834423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 508836418301896388542233845 47703414215802786425834423)
          ·
            refine ⟨71555121323704179638751635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47703414215802786425834423 71555121323704179638751635)
            ·
              refine ⟨107332681985556269458127453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71555121323704179638751635 107332681985556269458127453)
              ·
                refine ⟨40249755744583601046797795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107332681985556269458127453 40249755744583601046797795)
                ·
                  refine ⟨60374633616875401570196693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40249755744583601046797795 60374633616875401570196693)
                  ·
                    refine ⟨1415030475395517224301485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60374633616875401570196693 1415030475395517224301485)
                    ·
                      rfl

theorem cell22_4133643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 7].length) (baseStart_4133643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133643 prefixEnd_4133643 := by exact prefixLift 4133643
  have htrace : WordTrace (prefixWord ++ tailWord_4133643) baseStart_4133643 baseEnd_4133643 := by
    simpa [prefixWord, tailWord_4133643, baseEnd_4133643] using wordTrace_append hprefix tailTrace_4133643
  have hstable : (prefixWord ++ tailWord_4133643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133643).length < 2 ^ (prefixWord ++ tailWord_4133643).sum := by decide
  have hdescent : baseEnd_4133643 < baseStart_4133643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133673 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 8]
def baseStart_4133673 : Nat := 118140960795 + 4133673 * 2 ^ 59
def prefixEnd_4133673 : Nat := 4983230072969 + 3 ^ 40 * 4133673 * 2
def baseEnd_4133673 : Nat := 471680248336202382017131

theorem tailTrace_4133673 : CollatzResearch.WordTrace tailWord_4133673 prefixEnd_4133673 471680248336202382017131 := by
  unfold tailWord_4133673
  simp only [CollatzResearch.WordTrace]
  refine ⟨150767440353416170987957673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100511626902277447325305115 150767440353416170987957673)
  ·
    refine ⟨113075580265062128240968255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150767440353416170987957673 113075580265062128240968255)
    ·
      refine ⟨169613370397593192361452383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113075580265062128240968255 169613370397593192361452383)
      ·
        refine ⟨254420055596389788542178575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169613370397593192361452383 254420055596389788542178575)
        ·
          refine ⟨381630083394584682813267863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254420055596389788542178575 381630083394584682813267863)
          ·
            refine ⟨572445125091877024219901795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381630083394584682813267863 572445125091877024219901795)
            ·
              refine ⟨858667687637815536329852693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572445125091877024219901795 858667687637815536329852693)
              ·
                refine ⟨40250047858022603265461845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 858667687637815536329852693 40250047858022603265461845)
                ·
                  refine ⟨471680248336202382017131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40250047858022603265461845 471680248336202382017131)
                  ·
                    rfl

theorem cell22_4133673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 8].length) (baseStart_4133673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133673 prefixEnd_4133673 := by exact prefixLift 4133673
  have htrace : WordTrace (prefixWord ++ tailWord_4133673) baseStart_4133673 baseEnd_4133673 := by
    simpa [prefixWord, tailWord_4133673, baseEnd_4133673] using wordTrace_append hprefix tailTrace_4133673
  have hstable : (prefixWord ++ tailWord_4133673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133673).length < 2 ^ (prefixWord ++ tailWord_4133673).sum := by decide
  have hdescent : baseEnd_4133673 < baseStart_4133673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133705 : List Nat := [1, 2, 1, 1, 2, 5, 1, 3, 1, 5]
def baseStart_4133705 : Nat := 118140960795 + 4133705 * 2 ^ 59
def prefixEnd_4133705 : Nat := 4983230072969 + 3 ^ 40 * 4133705 * 2
def baseEnd_4133705 : Nat := 1415051699262569729251295

theorem tailTrace_4133705 : CollatzResearch.WordTrace tailWord_4133705 prefixEnd_4133705 1415051699262569729251295 := by
  unfold tailWord_4133705
  simp only [CollatzResearch.WordTrace]
  refine ⟨150768607489300240453122569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100512404992866826968748379 150768607489300240453122569)
  ·
    refine ⟨113076455616975180339841927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150768607489300240453122569 113076455616975180339841927)
    ·
      refine ⟨169614683425462770509762891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113076455616975180339841927 169614683425462770509762891)
      ·
        refine ⟨254422025138194155764644337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169614683425462770509762891 254422025138194155764644337)
        ·
          refine ⟨190816518853645616823483253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254422025138194155764644337 190816518853645616823483253)
          ·
            refine ⟨17889048642529276577201555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190816518853645616823483253 17889048642529276577201555)
            ·
              refine ⟨26833572963793914865802333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17889048642529276577201555 26833572963793914865802333)
              ·
                refine ⟨10062589861422718074675875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26833572963793914865802333 10062589861422718074675875)
                ·
                  refine ⟨15093884792134077112013813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10062589861422718074675875 15093884792134077112013813)
                  ·
                    refine ⟨1415051699262569729251295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15093884792134077112013813 1415051699262569729251295)
                    ·
                      rfl

theorem cell22_4133705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_4133705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133705 prefixEnd_4133705 := by exact prefixLift 4133705
  have htrace : WordTrace (prefixWord ++ tailWord_4133705) baseStart_4133705 baseEnd_4133705 := by
    simpa [prefixWord, tailWord_4133705, baseEnd_4133705] using wordTrace_append hprefix tailTrace_4133705
  have hstable : (prefixWord ++ tailWord_4133705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133705).length < 2 ^ (prefixWord ++ tailWord_4133705).sum := by decide
  have hdescent : baseEnd_4133705 < baseStart_4133705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133724 : List Nat := [2, 2, 4, 2, 1, 1, 1, 5, 4]
def baseStart_4133724 : Nat := 118140960795 + 4133724 * 2 ^ 59
def prefixEnd_4133724 : Nat := 4983230072969 + 3 ^ 40 * 4133724 * 2
def baseEnd_4133724 : Nat := 471686067783620004342079

theorem tailTrace_4133724 : CollatzResearch.WordTrace tailWord_4133724 prefixEnd_4133724 471686067783620004342079 := by
  unfold tailWord_4133724
  simp only [CollatzResearch.WordTrace]
  refine ⟨75384650238115703349032113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100512866984154271132042817 75384650238115703349032113)
  ·
    refine ⟨56538487678586777511774085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75384650238115703349032113 56538487678586777511774085)
    ·
      refine ⟨10600966439735020783457641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56538487678586777511774085 10600966439735020783457641)
      ·
        refine ⟨7950724829801265587593231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10600966439735020783457641 7950724829801265587593231)
        ·
          refine ⟨11926087244701898381389847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7950724829801265587593231 11926087244701898381389847)
          ·
            refine ⟨17889130867052847572084771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11926087244701898381389847 17889130867052847572084771)
            ·
              refine ⟨26833696300579271358127157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17889130867052847572084771 26833696300579271358127157)
              ·
                refine ⟨2515659028179306689824421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26833696300579271358127157 2515659028179306689824421)
                ·
                  refine ⟨471686067783620004342079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2515659028179306689824421 471686067783620004342079)
                  ·
                    rfl

theorem cell22_4133724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_4133724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133724 prefixEnd_4133724 := by exact prefixLift 4133724
  have htrace : WordTrace (prefixWord ++ tailWord_4133724) baseStart_4133724 baseEnd_4133724 := by
    simpa [prefixWord, tailWord_4133724, baseEnd_4133724] using wordTrace_append hprefix tailTrace_4133724
  have hstable : (prefixWord ++ tailWord_4133724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133724).length < 2 ^ (prefixWord ++ tailWord_4133724).sum := by decide
  have hdescent : baseEnd_4133724 < baseStart_4133724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133735 : List Nat := [1, 1, 5, 1, 2, 3, 9]
def baseStart_4133735 : Nat := 118140960795 + 4133735 * 2 ^ 59
def prefixEnd_4133735 : Nat := 4983230072969 + 3 ^ 40 * 4133735 * 2
def baseEnd_4133735 : Nat := 52409702550950357444489

theorem tailTrace_4133735 : CollatzResearch.WordTrace tailWord_4133735 prefixEnd_4133735 52409702550950357444489 := by
  unfold tailWord_4133735
  simp only [CollatzResearch.WordTrace]
  refine ⟨150769701679191555576714659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100513134452794370384476439 150769701679191555576714659)
  ·
    refine ⟨226154552518787333365071989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150769701679191555576714659 226154552518787333365071989)
    ·
      refine ⟨21201989298636312502975499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226154552518787333365071989 21201989298636312502975499)
      ·
        refine ⟨31802983947954468754463249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21201989298636312502975499 31802983947954468754463249)
        ·
          refine ⟨23852237960965851565847437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31802983947954468754463249 23852237960965851565847437)
          ·
            refine ⟨8944589235362194337192789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23852237960965851565847437 8944589235362194337192789)
            ·
              refine ⟨52409702550950357444489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8944589235362194337192789 52409702550950357444489)
              ·
                rfl

theorem cell22_4133735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 9].length) (baseStart_4133735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133735 prefixEnd_4133735 := by exact prefixLift 4133735
  have htrace : WordTrace (prefixWord ++ tailWord_4133735) baseStart_4133735 baseEnd_4133735 := by
    simpa [prefixWord, tailWord_4133735, baseEnd_4133735] using wordTrace_append hprefix tailTrace_4133735
  have hstable : (prefixWord ++ tailWord_4133735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133735).length < 2 ^ (prefixWord ++ tailWord_4133735).sum := by decide
  have hdescent : baseEnd_4133735 < baseStart_4133735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133795 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 4, 5]
def baseStart_4133795 : Nat := 118140960795 + 4133795 * 2 ^ 59
def prefixEnd_4133795 : Nat := 4983230072969 + 3 ^ 40 * 4133795 * 2
def baseEnd_4133795 : Nat := 1415082508101839494501019

theorem tailTrace_4133795 : CollatzResearch.WordTrace tailWord_4133795 prefixEnd_4133795 1415082508101839494501019 := by
  unfold tailWord_4133795
  simp only [CollatzResearch.WordTrace]
  refine ⟨150771890058974185823898839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100514593372649457215932559 150771890058974185823898839)
  ·
    refine ⟨226157835088461278735848259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150771890058974185823898839 226157835088461278735848259)
    ·
      refine ⟨339236752632691918103772389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226157835088461278735848259 339236752632691918103772389)
      ·
        refine ⟨63606891118629734644457323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339236752632691918103772389 63606891118629734644457323)
        ·
          refine ⟨95410336677944601966685985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63606891118629734644457323 95410336677944601966685985)
          ·
            refine ⟨71557752508458451475014489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95410336677944601966685985 71557752508458451475014489)
            ·
              refine ⟨53668314381343838606260867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71557752508458451475014489 53668314381343838606260867)
              ·
                refine ⟨80502471572015757909391301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53668314381343838606260867 80502471572015757909391301)
                ·
                  refine ⟨15094213419752954608010869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80502471572015757909391301 15094213419752954608010869)
                  ·
                    refine ⟨1415082508101839494501019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15094213419752954608010869 1415082508101839494501019)
                    ·
                      rfl

theorem cell22_4133795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 5].length) (baseStart_4133795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133795 prefixEnd_4133795 := by exact prefixLift 4133795
  have htrace : WordTrace (prefixWord ++ tailWord_4133795) baseStart_4133795 baseEnd_4133795 := by
    simpa [prefixWord, tailWord_4133795, baseEnd_4133795] using wordTrace_append hprefix tailTrace_4133795
  have hstable : (prefixWord ++ tailWord_4133795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133795).length < 2 ^ (prefixWord ++ tailWord_4133795).sum := by decide
  have hdescent : baseEnd_4133795 < baseStart_4133795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133801 : List Nat := [1, 2, 1, 1, 1, 1, 9, 2, 1, 3]
def baseStart_4133801 : Nat := 118140960795 + 4133801 * 2 ^ 59
def prefixEnd_4133801 : Nat := 4983230072969 + 3 ^ 40 * 4133801 * 2
def baseEnd_4133801 : Nat := 1415084562024457478851001

theorem tailTrace_4133801 : CollatzResearch.WordTrace tailWord_4133801 prefixEnd_4133801 1415084562024457478851001 := by
  unfold tailWord_4133801
  simp only [CollatzResearch.WordTrace]
  refine ⟨150772108896952448848617257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100514739264634965899078171 150772108896952448848617257)
  ·
    refine ⟨113079081672714336636462943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150772108896952448848617257 113079081672714336636462943)
    ·
      refine ⟨169618622509071504954694415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113079081672714336636462943 169618622509071504954694415)
      ·
        refine ⟨254427933763607257432041623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169618622509071504954694415 254427933763607257432041623)
        ·
          refine ⟨381641900645410886148062435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254427933763607257432041623 381641900645410886148062435)
          ·
            refine ⟨572462850968116329222093653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381641900645410886148062435 572462850968116329222093653)
            ·
              refine ⟨3354274517391306616535705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 572462850968116329222093653 3354274517391306616535705)
              ·
                refine ⟨2515705888043479962401779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3354274517391306616535705 2515705888043479962401779)
                ·
                  refine ⟨3773558832065219943602669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515705888043479962401779 3773558832065219943602669)
                  ·
                    refine ⟨1415084562024457478851001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3773558832065219943602669 1415084562024457478851001)
                    ·
                      rfl

theorem cell22_4133801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 1, 3].length) (baseStart_4133801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133801 prefixEnd_4133801 := by exact prefixLift 4133801
  have htrace : WordTrace (prefixWord ++ tailWord_4133801) baseStart_4133801 baseEnd_4133801 := by
    simpa [prefixWord, tailWord_4133801, baseEnd_4133801] using wordTrace_append hprefix tailTrace_4133801
  have hstable : (prefixWord ++ tailWord_4133801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133801).length < 2 ^ (prefixWord ++ tailWord_4133801).sum := by decide
  have hdescent : baseEnd_4133801 < baseStart_4133801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133810 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_4133810 : Nat := 118140960795 + 4133810 * 2 ^ 59
def prefixEnd_4133810 : Nat := 4983230072969 + 3 ^ 40 * 4133810 * 2
def baseEnd_4133810 : Nat := 1415087642908384455375973

theorem tailTrace_4133810 : CollatzResearch.WordTrace tailWord_4133810 prefixEnd_4133810 1415087642908384455375973 := by
  unfold tailWord_4133810
  simp only [CollatzResearch.WordTrace]
  refine ⟨37693109288479960846423721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100514958102613228923796589 37693109288479960846423721)
  ·
    refine ⟨28269831966359970634817791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37693109288479960846423721 28269831966359970634817791)
    ·
      refine ⟨42404747949539955952226687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28269831966359970634817791 42404747949539955952226687)
      ·
        refine ⟨63607121924309933928340031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42404747949539955952226687 63607121924309933928340031)
        ·
          refine ⟨95410682886464900892510047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63607121924309933928340031 95410682886464900892510047)
          ·
            refine ⟨143116024329697351338765071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95410682886464900892510047 143116024329697351338765071)
            ·
              refine ⟨214674036494546027008147607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143116024329697351338765071 214674036494546027008147607)
              ·
                refine ⟨322011054741819040512221411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214674036494546027008147607 322011054741819040512221411)
                ·
                  refine ⟨483016582112728560768332117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322011054741819040512221411 483016582112728560768332117)
                  ·
                    refine ⟨1415087642908384455375973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 483016582112728560768332117 1415087642908384455375973)
                    ·
                      rfl

theorem cell22_4133810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_4133810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133810 prefixEnd_4133810 := by exact prefixLift 4133810
  have htrace : WordTrace (prefixWord ++ tailWord_4133810) baseStart_4133810 baseEnd_4133810 := by
    simpa [prefixWord, tailWord_4133810, baseEnd_4133810] using wordTrace_append hprefix tailTrace_4133810
  have hstable : (prefixWord ++ tailWord_4133810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133810).length < 2 ^ (prefixWord ++ tailWord_4133810).sum := by decide
  have hdescent : baseEnd_4133810 < baseStart_4133810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133859 : List Nat := [1, 1, 1, 6, 1, 1, 3, 4, 4]
def baseStart_4133859 : Nat := 118140960795 + 4133859 * 2 ^ 59
def prefixEnd_4133859 : Nat := 4983230072969 + 3 ^ 40 * 4133859 * 2
def baseEnd_4133859 : Nat := 471701472203254886966941

theorem tailTrace_4133859 : CollatzResearch.WordTrace tailWord_4133859 prefixEnd_4133859 471701472203254886966941 := by
  unfold tailWord_4133859
  simp only [CollatzResearch.WordTrace]
  refine ⟨150774224330742324754228631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100516149553828216502819087 150774224330742324754228631)
  ·
    refine ⟨226161336496113487131342947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150774224330742324754228631 226161336496113487131342947)
    ·
      refine ⟨339242004744170230697014421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226161336496113487131342947 339242004744170230697014421)
      ·
        refine ⟨15901968972382979563922551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 339242004744170230697014421 15901968972382979563922551)
        ·
          refine ⟨23852953458574469345883827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15901968972382979563922551 23852953458574469345883827)
          ·
            refine ⟨35779430187861704018825741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23852953458574469345883827 35779430187861704018825741)
            ·
              refine ⟨13417286320448139007059653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35779430187861704018825741 13417286320448139007059653)
              ·
                refine ⟨2515741185084026063823685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13417286320448139007059653 2515741185084026063823685)
                ·
                  refine ⟨471701472203254886966941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2515741185084026063823685 471701472203254886966941)
                  ·
                    rfl

theorem cell22_4133859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 4].length) (baseStart_4133859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133859 prefixEnd_4133859 := by exact prefixLift 4133859
  have htrace : WordTrace (prefixWord ++ tailWord_4133859) baseStart_4133859 baseEnd_4133859 := by
    simpa [prefixWord, tailWord_4133859, baseEnd_4133859] using wordTrace_append hprefix tailTrace_4133859
  have hstable : (prefixWord ++ tailWord_4133859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133859).length < 2 ^ (prefixWord ++ tailWord_4133859).sum := by decide
  have hdescent : baseEnd_4133859 < baseStart_4133859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133889 : List Nat := [1, 2, 4, 1, 2, 2, 3, 1, 2, 4]
def baseStart_4133889 : Nat := 118140960795 + 4133889 * 2 ^ 59
def prefixEnd_4133889 : Nat := 4983230072969 + 3 ^ 40 * 4133889 * 2
def baseEnd_4133889 : Nat := 1415114686222854582650731

theorem tailTrace_4133889 : CollatzResearch.WordTrace tailWord_4133889 prefixEnd_4133889 1415114686222854582650731 := by
  unfold tailWord_4133889
  simp only [CollatzResearch.WordTrace]
  refine ⟨150775318520633639877820721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100516879013755759918547147 150775318520633639877820721)
  ·
    refine ⟨113081488890475229908365541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150775318520633639877820721 113081488890475229908365541)
    ·
      refine ⟨21202779166964105607818539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113081488890475229908365541 21202779166964105607818539)
      ·
        refine ⟨31804168750446158411727809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21202779166964105607818539 31804168750446158411727809)
        ·
          refine ⟨23853126562834618808795857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31804168750446158411727809 23853126562834618808795857)
          ·
            refine ⟨17889844922125964106596893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23853126562834618808795857 17889844922125964106596893)
            ·
              refine ⟨6708691845797236539973835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17889844922125964106596893 6708691845797236539973835)
              ·
                refine ⟨10063037768695854809960753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6708691845797236539973835 10063037768695854809960753)
                ·
                  refine ⟨7547278326521891107470565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10063037768695854809960753 7547278326521891107470565)
                  ·
                    refine ⟨1415114686222854582650731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7547278326521891107470565 1415114686222854582650731)
                    ·
                      rfl

theorem cell22_4133889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_4133889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133889 prefixEnd_4133889 := by exact prefixLift 4133889
  have htrace : WordTrace (prefixWord ++ tailWord_4133889) baseStart_4133889 baseEnd_4133889 := by
    simpa [prefixWord, tailWord_4133889, baseEnd_4133889] using wordTrace_append hprefix tailTrace_4133889
  have hstable : (prefixWord ++ tailWord_4133889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133889).length < 2 ^ (prefixWord ++ tailWord_4133889).sum := by decide
  have hdescent : baseEnd_4133889 < baseStart_4133889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133919 : List Nat := [1, 1, 2, 4, 1, 3, 1, 3, 3, 3]
def baseStart_4133919 : Nat := 118140960795 + 4133919 * 2 ^ 59
def prefixEnd_4133919 : Nat := 4983230072969 + 3 ^ 40 * 4133919 * 2
def baseEnd_4133919 : Nat := 1415124955835944504400639

theorem tailTrace_4133919 : CollatzResearch.WordTrace tailWord_4133919 prefixEnd_4133919 1415124955835944504400639 := by
  unfold tailWord_4133919
  simp only [CollatzResearch.WordTrace]
  refine ⟨150776412710524955001412811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100517608473683303334275207 150776412710524955001412811)
  ·
    refine ⟨226164619065787432502119217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150776412710524955001412811 226164619065787432502119217)
    ·
      refine ⟨169623464299340574376589413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226164619065787432502119217 169623464299340574376589413)
      ·
        refine ⟨31804399556126357695610515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169623464299340574376589413 31804399556126357695610515)
        ·
          refine ⟨47706599334189536543415773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31804399556126357695610515 47706599334189536543415773)
          ·
            refine ⟨17889974750321076203780915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47706599334189536543415773 17889974750321076203780915)
            ·
              refine ⟨26834962125481614305671373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17889974750321076203780915 26834962125481614305671373)
              ·
                refine ⟨10063110797055605364626765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26834962125481614305671373 10063110797055605364626765)
                ·
                  refine ⟨3773666548895852011735037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10063110797055605364626765 3773666548895852011735037)
                  ·
                    refine ⟨1415124955835944504400639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3773666548895852011735037 1415124955835944504400639)
                    ·
                      rfl

theorem cell22_4133919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 3].length) (baseStart_4133919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133919 prefixEnd_4133919 := by exact prefixLift 4133919
  have htrace : WordTrace (prefixWord ++ tailWord_4133919) baseStart_4133919 baseEnd_4133919 := by
    simpa [prefixWord, tailWord_4133919, baseEnd_4133919] using wordTrace_append hprefix tailTrace_4133919
  have hstable : (prefixWord ++ tailWord_4133919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133919).length < 2 ^ (prefixWord ++ tailWord_4133919).sum := by decide
  have hdescent : baseEnd_4133919 < baseStart_4133919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133970 : List Nat := [3, 2, 2, 1, 3, 2, 3, 2, 1, 3]
def baseStart_4133970 : Nat := 118140960795 + 4133970 * 2 ^ 59
def prefixEnd_4133970 : Nat := 4983230072969 + 3 ^ 40 * 4133970 * 2
def baseEnd_4133970 : Nat := 1415142414178197371375483

theorem tailTrace_4133970 : CollatzResearch.WordTrace tailWord_4133970 prefixEnd_4133970 1415142414178197371375483 := by
  unfold tailWord_4133970
  simp only [CollatzResearch.WordTrace]
  refine ⟨37694568208335047677879841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100518848555560127141012909 37694568208335047677879841)
  ·
    refine ⟨28270926156251285758409881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37694568208335047677879841 28270926156251285758409881)
    ·
      refine ⟨21203194617188464318807411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28270926156251285758409881 21203194617188464318807411)
      ·
        refine ⟨31804791925782696478211117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21203194617188464318807411 31804791925782696478211117)
        ·
          refine ⟨11926796972168511179329169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31804791925782696478211117 11926796972168511179329169)
          ·
            refine ⟨8945097729126383384496877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11926796972168511179329169 8945097729126383384496877)
            ·
              refine ⟨3354411648422393769186329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8945097729126383384496877 3354411648422393769186329)
              ·
                refine ⟨2515808736316795326889747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3354411648422393769186329 2515808736316795326889747)
                ·
                  refine ⟨3773713104475192990334621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515808736316795326889747 3773713104475192990334621)
                  ·
                    refine ⟨1415142414178197371375483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3773713104475192990334621 1415142414178197371375483)
                    ·
                      rfl

theorem cell22_4133970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_4133970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133970 prefixEnd_4133970 := by exact prefixLift 4133970
  have htrace : WordTrace (prefixWord ++ tailWord_4133970) baseStart_4133970 baseEnd_4133970 := by
    simpa [prefixWord, tailWord_4133970, baseEnd_4133970] using wordTrace_append hprefix tailTrace_4133970
  have hstable : (prefixWord ++ tailWord_4133970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133970).length < 2 ^ (prefixWord ++ tailWord_4133970).sum := by decide
  have hdescent : baseEnd_4133970 < baseStart_4133970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4133977 : List Nat := [1, 2, 1, 2, 2, 1, 2, 5, 6]
def baseStart_4133977 : Nat := 118140960795 + 4133977 * 2 ^ 59
def prefixEnd_4133977 : Nat := 4983230072969 + 3 ^ 40 * 4133977 * 2
def baseEnd_4133977 : Nat := 471714936807083895483487

theorem tailTrace_4133977 : CollatzResearch.WordTrace tailWord_4133977 prefixEnd_4133977 471714936807083895483487 := by
  unfold tailWord_4133977
  simp only [CollatzResearch.WordTrace]
  refine ⟨150778528144314830907024185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100519018762876553938016123 150778528144314830907024185)
  ·
    refine ⟨113083896108236123180268139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150778528144314830907024185 113083896108236123180268139)
    ·
      refine ⟨169625844162354184770402209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113083896108236123180268139 169625844162354184770402209)
      ·
        refine ⟨127219383121765638577801657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169625844162354184770402209 127219383121765638577801657)
        ·
          refine ⟨95414537341324228933351243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127219383121765638577801657 95414537341324228933351243)
          ·
            refine ⟨143121806011986343400026865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95414537341324228933351243 143121806011986343400026865)
            ·
              refine ⟨107341354508989757550020149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143121806011986343400026865 107341354508989757550020149)
              ·
                refine ⟨10063251985217789770314389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107341354508989757550020149 10063251985217789770314389)
                ·
                  refine ⟨471714936807083895483487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10063251985217789770314389 471714936807083895483487)
                  ·
                    rfl

theorem cell22_4133977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 6].length) (baseStart_4133977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4133977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4133977 prefixEnd_4133977 := by exact prefixLift 4133977
  have htrace : WordTrace (prefixWord ++ tailWord_4133977) baseStart_4133977 baseEnd_4133977 := by
    simpa [prefixWord, tailWord_4133977, baseEnd_4133977] using wordTrace_append hprefix tailTrace_4133977
  have hstable : (prefixWord ++ tailWord_4133977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4133977).length < 2 ^ (prefixWord ++ tailWord_4133977).sum := by decide
  have hdescent : baseEnd_4133977 < baseStart_4133977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4133977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134039 : List Nat := [1, 1, 3, 3, 3, 1, 3, 7]
def baseStart_4134039 : Nat := 118140960795 + 4134039 * 2 ^ 59
def prefixEnd_4134039 : Nat := 4983230072969 + 3 ^ 40 * 4134039 * 2
def baseEnd_4134039 : Nat := 157240670476478243488919

theorem tailTrace_4134039 : CollatzResearch.WordTrace tailWord_4134039 prefixEnd_4134039 157240670476478243488919 := by
  unfold tailWord_4134039
  simp only [CollatzResearch.WordTrace]
  refine ⟨150780789470090215495781171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100520526313393476997187447 150780789470090215495781171)
  ·
    refine ⟨226171184205135323243671757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150780789470090215495781171 226171184205135323243671757)
    ·
      refine ⟨84814194076925746216376909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226171184205135323243671757 84814194076925746216376909)
      ·
        refine ⟨31805322778847154831141341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84814194076925746216376909 31805322778847154831141341)
        ·
          refine ⟨11926996042067683061678003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31805322778847154831141341 11926996042067683061678003)
          ·
            refine ⟨17890494063101524592517005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11926996042067683061678003 17890494063101524592517005)
            ·
              refine ⟨6708935273663071722193877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17890494063101524592517005 6708935273663071722193877)
              ·
                refine ⟨157240670476478243488919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6708935273663071722193877 157240670476478243488919)
                ·
                  rfl

theorem cell22_4134039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 7].length) (baseStart_4134039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134039 prefixEnd_4134039 := by exact prefixLift 4134039
  have htrace : WordTrace (prefixWord ++ tailWord_4134039) baseStart_4134039 baseEnd_4134039 := by
    simpa [prefixWord, tailWord_4134039, baseEnd_4134039] using wordTrace_append hprefix tailTrace_4134039
  have hstable : (prefixWord ++ tailWord_4134039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134039).length < 2 ^ (prefixWord ++ tailWord_4134039).sum := by decide
  have hdescent : baseEnd_4134039 < baseStart_4134039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134058 : List Nat := [3, 1, 5, 1, 1, 1, 3, 1, 2, 4]
def baseStart_4134058 : Nat := 118140960795 + 4134058 * 2 ^ 59
def prefixEnd_4134058 : Nat := 4983230072969 + 3 ^ 40 * 4134058 * 2
def baseEnd_4134058 : Nat := 1415172538376594475175213

theorem tailTrace_4134058 : CollatzResearch.WordTrace tailWord_4134058 prefixEnd_4134058 1415172538376594475175213 := by
  unfold tailWord_4134058
  simp only [CollatzResearch.WordTrace]
  refine ⟨37695370614255345435180707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100520988304680921160481885 37695370614255345435180707)
  ·
    refine ⟨56543055921383018152771061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37695370614255345435180707 56543055921383018152771061)
    ·
      refine ⟨5300911492629657951822287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56543055921383018152771061 5300911492629657951822287)
      ·
        refine ⟨7951367238944486927733431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5300911492629657951822287 7951367238944486927733431)
        ·
          refine ⟨11927050858416730391600147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7951367238944486927733431 11927050858416730391600147)
          ·
            refine ⟨17890576287625095587400221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11927050858416730391600147 17890576287625095587400221)
            ·
              refine ⟨6708966107859410845275083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17890576287625095587400221 6708966107859410845275083)
              ·
                refine ⟨10063449161789116267912625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6708966107859410845275083 10063449161789116267912625)
                ·
                  refine ⟨7547586871341837200934469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10063449161789116267912625 7547586871341837200934469)
                  ·
                    refine ⟨1415172538376594475175213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7547586871341837200934469 1415172538376594475175213)
                    ·
                      rfl

theorem cell22_4134058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_4134058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134058 prefixEnd_4134058 := by exact prefixLift 4134058
  have htrace : WordTrace (prefixWord ++ tailWord_4134058) baseStart_4134058 baseEnd_4134058 := by
    simpa [prefixWord, tailWord_4134058, baseEnd_4134058] using wordTrace_append hprefix tailTrace_4134058
  have hstable : (prefixWord ++ tailWord_4134058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134058).length < 2 ^ (prefixWord ++ tailWord_4134058).sum := by decide
  have hdescent : baseEnd_4134058 < baseStart_4134058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134088 : List Nat := [2, 1, 3, 1, 2, 1, 4, 4, 1, 3]
def baseStart_4134088 : Nat := 118140960795 + 4134088 * 2 ^ 59
def prefixEnd_4134088 : Nat := 4983230072969 + 3 ^ 40 * 4134088 * 2
def baseEnd_4134088 : Nat := 1415182807989684396925121

theorem tailTrace_4134088 : CollatzResearch.WordTrace tailWord_4134088 prefixEnd_4134088 1415182807989684396925121 := by
  unfold tailWord_4134088
  simp only [CollatzResearch.WordTrace]
  refine ⟨75391288323456348432157459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100521717764608464576209945 75391288323456348432157459)
  ·
    refine ⟨113086932485184522648236189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75391288323456348432157459 113086932485184522648236189)
    ·
      refine ⟨42407599681944195993088571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113086932485184522648236189 42407599681944195993088571)
      ·
        refine ⟨63611399522916293989632857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42407599681944195993088571 63611399522916293989632857)
        ·
          refine ⟨47708549642187220492224643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63611399522916293989632857 47708549642187220492224643)
          ·
            refine ⟨71562824463280830738336965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47708549642187220492224643 71562824463280830738336965)
            ·
              refine ⟨13418029586865155763438181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71562824463280830738336965 13418029586865155763438181)
              ·
                refine ⟨2515880547537216705644659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13418029586865155763438181 2515880547537216705644659)
                ·
                  refine ⟨3773820821305825058466989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515880547537216705644659 3773820821305825058466989)
                  ·
                    refine ⟨1415182807989684396925121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3773820821305825058466989 1415182807989684396925121)
                    ·
                      rfl

theorem cell22_4134088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_4134088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134088 prefixEnd_4134088 := by exact prefixLift 4134088
  have htrace : WordTrace (prefixWord ++ tailWord_4134088) baseStart_4134088 baseEnd_4134088 := by
    simpa [prefixWord, tailWord_4134088, baseEnd_4134088] using wordTrace_append hprefix tailTrace_4134088
  have hstable : (prefixWord ++ tailWord_4134088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134088).length < 2 ^ (prefixWord ++ tailWord_4134088).sum := by decide
  have hdescent : baseEnd_4134088 < baseStart_4134088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134131 : List Nat := [1, 1, 1, 2, 2, 5, 2, 3, 1, 4]
def baseStart_4134131 : Nat := 118140960795 + 4134131 * 2 ^ 59
def prefixEnd_4134131 : Nat := 4983230072969 + 3 ^ 40 * 4134131 * 2
def baseEnd_4134131 : Nat := 1415197527768446618099989

theorem tailTrace_4134131 : CollatzResearch.WordTrace tailWord_4134131 prefixEnd_4134131 1415197527768446618099989 := by
  unfold tailWord_4134131
  simp only [CollatzResearch.WordTrace]
  refine ⟨150784144985756915208130247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100522763323837943472086831 150784144985756915208130247)
  ·
    refine ⟨226176217478635372812195371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150784144985756915208130247 226176217478635372812195371)
    ·
      refine ⟨339264326217953059218293057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226176217478635372812195371 339264326217953059218293057)
      ·
        refine ⟨254448244663464794413719793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339264326217953059218293057 254448244663464794413719793)
        ·
          refine ⟨190836183497598595810289845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254448244663464794413719793 190836183497598595810289845)
          ·
            refine ⟨17890892202899868357214673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190836183497598595810289845 17890892202899868357214673)
            ·
              refine ⟨13418169152174901267911005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17890892202899868357214673 13418169152174901267911005)
              ·
                refine ⟨5031813432065587975466627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13418169152174901267911005 5031813432065587975466627)
                ·
                  refine ⟨7547720148098381963199941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5031813432065587975466627 7547720148098381963199941)
                  ·
                    refine ⟨1415197527768446618099989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7547720148098381963199941 1415197527768446618099989)
                    ·
                      rfl

theorem cell22_4134131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 4].length) (baseStart_4134131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134131 prefixEnd_4134131 := by exact prefixLift 4134131
  have htrace : WordTrace (prefixWord ++ tailWord_4134131) baseStart_4134131 baseEnd_4134131 := by
    simpa [prefixWord, tailWord_4134131, baseEnd_4134131] using wordTrace_append hprefix tailTrace_4134131
  have hstable : (prefixWord ++ tailWord_4134131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134131).length < 2 ^ (prefixWord ++ tailWord_4134131).sum := by decide
  have hdescent : baseEnd_4134131 < baseStart_4134131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134178 : List Nat := [3, 3, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_4134178 : Nat := 118140960795 + 4134178 * 2 ^ 59
def prefixEnd_4134178 : Nat := 4983230072969 + 3 ^ 40 * 4134178 * 2
def baseEnd_4134178 : Nat := 1415213616828954162174845

theorem tailTrace_4134178 : CollatzResearch.WordTrace tailWord_4134178 prefixEnd_4134178 1415213616828954162174845 := by
  unfold tailWord_4134178
  simp only [CollatzResearch.WordTrace]
  refine ⟨37696464804146660558772797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100523906144391094823394125 37696464804146660558772797)
  ·
    refine ⟨14136174301554997709539799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37696464804146660558772797 14136174301554997709539799)
    ·
      refine ⟨21204261452332496564309699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14136174301554997709539799 21204261452332496564309699)
      ·
        refine ⟨31806392178498744846464549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21204261452332496564309699 31806392178498744846464549)
        ·
          refine ⟨5963698533468514658712103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31806392178498744846464549 5963698533468514658712103)
          ·
            refine ⟨8945547800202771988068155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5963698533468514658712103 8945547800202771988068155)
            ·
              refine ⟨13418321700304157982102233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8945547800202771988068155 13418321700304157982102233)
              ·
                refine ⟨10063741275228118486576675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13418321700304157982102233 10063741275228118486576675)
                ·
                  refine ⟨15095611912842177729865013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10063741275228118486576675 15095611912842177729865013)
                  ·
                    refine ⟨1415213616828954162174845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15095611912842177729865013 1415213616828954162174845)
                    ·
                      rfl

theorem cell22_4134178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_4134178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134178 prefixEnd_4134178 := by exact prefixLift 4134178
  have htrace : WordTrace (prefixWord ++ tailWord_4134178) baseStart_4134178 baseEnd_4134178 := by
    simpa [prefixWord, tailWord_4134178, baseEnd_4134178] using wordTrace_append hprefix tailTrace_4134178
  have hstable : (prefixWord ++ tailWord_4134178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134178).length < 2 ^ (prefixWord ++ tailWord_4134178).sum := by decide
  have hdescent : baseEnd_4134178 < baseStart_4134178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134240 : List Nat := [2, 1, 1, 3, 4, 1, 1, 5, 1, 3]
def baseStart_4134240 : Nat := 118140960795 + 4134240 * 2 ^ 59
def prefixEnd_4134240 : Nat := 4983230072969 + 3 ^ 40 * 4134240 * 2
def baseEnd_4134240 : Nat := 1415234840696006667124655

theorem tailTrace_4134240 : CollatzResearch.WordTrace tailWord_4134240 prefixEnd_4134240 1415234840696006667124655 := by
  unfold tailWord_4134240
  simp only [CollatzResearch.WordTrace]
  refine ⟨75394060271181013411924087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100525413694908017882565449 75394060271181013411924087)
  ·
    refine ⟨113091090406771520117886131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75394060271181013411924087 113091090406771520117886131)
    ·
      refine ⟨169636635610157280176829197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113091090406771520117886131 169636635610157280176829197)
      ·
        refine ⟨63613738353808980066310949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169636635610157280176829197 63613738353808980066310949)
        ·
          refine ⟨11927575941339183762433303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63613738353808980066310949 11927575941339183762433303)
          ·
            refine ⟨17891363912008775643649955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11927575941339183762433303 17891363912008775643649955)
            ·
              refine ⟨26837045868013163465474933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17891363912008775643649955 26837045868013163465474933)
              ·
                refine ⟨2515973050126234074888275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26837045868013163465474933 2515973050126234074888275)
                ·
                  refine ⟨3773959575189351112332413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515973050126234074888275 3773959575189351112332413)
                  ·
                    refine ⟨1415234840696006667124655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3773959575189351112332413 1415234840696006667124655)
                    ·
                      rfl

theorem cell22_4134240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 1, 3].length) (baseStart_4134240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134240 prefixEnd_4134240 := by exact prefixLift 4134240
  have htrace : WordTrace (prefixWord ++ tailWord_4134240) baseStart_4134240 baseEnd_4134240 := by
    simpa [prefixWord, tailWord_4134240, baseEnd_4134240] using wordTrace_append hprefix tailTrace_4134240
  have hstable : (prefixWord ++ tailWord_4134240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134240).length < 2 ^ (prefixWord ++ tailWord_4134240).sum := by decide
  have hdescent : baseEnd_4134240 < baseStart_4134240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134253 : List Nat := [1, 5, 1, 1, 1, 3, 3, 2, 5]
def baseStart_4134253 : Nat := 118140960795 + 4134253 * 2 ^ 59
def prefixEnd_4134253 : Nat := 4983230072969 + 3 ^ 40 * 4134253 * 2
def baseEnd_4134253 : Nat := 471746430287226322183205

theorem tailTrace_4134253 : CollatzResearch.WordTrace tailWord_4134253 prefixEnd_4134253 471746430287226322183205 := by
  unfold tailWord_4134253
  simp only [CollatzResearch.WordTrace]
  refine ⟨150788594691314930044071413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100525729794209953362714275 150788594691314930044071413)
  ·
    refine ⟨14136430752310774691631695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150788594691314930044071413 14136430752310774691631695)
    ·
      refine ⟨21204646128466162037447543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14136430752310774691631695 21204646128466162037447543)
      ·
        refine ⟨31806969192699243056171315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21204646128466162037447543 31806969192699243056171315)
        ·
          refine ⟨47710453789048864584256973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31806969192699243056171315 47710453789048864584256973)
          ·
            refine ⟨17891420170893324219096365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47710453789048864584256973 17891420170893324219096365)
            ·
              refine ⟨6709282564084996582161137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17891420170893324219096365 6709282564084996582161137)
              ·
                refine ⟨5031961923063747436620853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6709282564084996582161137 5031961923063747436620853)
                ·
                  refine ⟨471746430287226322183205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5031961923063747436620853 471746430287226322183205)
                  ·
                    rfl

theorem cell22_4134253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_4134253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134253 prefixEnd_4134253 := by exact prefixLift 4134253
  have htrace : WordTrace (prefixWord ++ tailWord_4134253) baseStart_4134253 baseEnd_4134253 := by
    simpa [prefixWord, tailWord_4134253, baseEnd_4134253] using wordTrace_append hprefix tailTrace_4134253
  have hstable : (prefixWord ++ tailWord_4134253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134253).length < 2 ^ (prefixWord ++ tailWord_4134253).sum := by decide
  have hdescent : baseEnd_4134253 < baseStart_4134253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134283 : List Nat := [1, 1, 1, 1, 4, 3, 4, 2, 1, 4]
def baseStart_4134283 : Nat := 118140960795 + 4134283 * 2 ^ 59
def prefixEnd_4134283 : Nat := 4983230072969 + 3 ^ 40 * 4134283 * 2
def baseEnd_4134283 : Nat := 1415249560474768888299523

theorem tailTrace_4134283 : CollatzResearch.WordTrace tailWord_4134283 prefixEnd_4134283 1415249560474768888299523 := by
  unfold tailWord_4134283
  simp only [CollatzResearch.WordTrace]
  refine ⟨150789688881206245167663503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100526459254137496778442335 150789688881206245167663503)
  ·
    refine ⟨226184533321809367751495255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150789688881206245167663503 226184533321809367751495255)
    ·
      refine ⟨339276799982714051627242883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226184533321809367751495255 339276799982714051627242883)
      ·
        refine ⟨508915199974071077440864325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339276799982714051627242883 508915199974071077440864325)
        ·
          refine ⟨95421599995138327020162061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 508915199974071077440864325 95421599995138327020162061)
          ·
            refine ⟨35783099998176872632560773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95421599995138327020162061 35783099998176872632560773)
            ·
              refine ⟨6709331249658163618605145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35783099998176872632560773 6709331249658163618605145)
              ·
                refine ⟨5031998437243622713953859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6709331249658163618605145 5031998437243622713953859)
                ·
                  refine ⟨7547997655865434070930789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5031998437243622713953859 7547997655865434070930789)
                  ·
                    refine ⟨1415249560474768888299523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7547997655865434070930789 1415249560474768888299523)
                    ·
                      rfl

theorem cell22_4134283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 4].length) (baseStart_4134283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134283 prefixEnd_4134283 := by exact prefixLift 4134283
  have htrace : WordTrace (prefixWord ++ tailWord_4134283) baseStart_4134283 baseEnd_4134283 := by
    simpa [prefixWord, tailWord_4134283, baseEnd_4134283] using wordTrace_append hprefix tailTrace_4134283
  have hstable : (prefixWord ++ tailWord_4134283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134283).length < 2 ^ (prefixWord ++ tailWord_4134283).sum := by decide
  have hdescent : baseEnd_4134283 < baseStart_4134283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134373 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 2, 6]
def baseStart_4134373 : Nat := 118140960795 + 4134373 * 2 ^ 59
def prefixEnd_4134373 : Nat := 4983230072969 + 3 ^ 40 * 4134373 * 2
def baseEnd_4134373 : Nat := 1415280369314038653549247

theorem tailTrace_4134373 : CollatzResearch.WordTrace tailWord_4134373 prefixEnd_4134373 1415280369314038653549247 := by
  unfold tailWord_4134373
  simp only [CollatzResearch.WordTrace]
  refine ⟨150792971450880190538439773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100528647633920127025626515 150792971450880190538439773)
  ·
    refine ⟨56547364294080071451914915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150792971450880190538439773 56547364294080071451914915)
    ·
      refine ⟨84821046441120107177872373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56547364294080071451914915 84821046441120107177872373)
      ·
        refine ⟨7951973103855010047925535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84821046441120107177872373 7951973103855010047925535)
        ·
          refine ⟨11927959655782515071888303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7951973103855010047925535 11927959655782515071888303)
          ·
            refine ⟨17891939483673772607832455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11927959655782515071888303 17891939483673772607832455)
            ·
              refine ⟨26837909225510658911748683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17891939483673772607832455 26837909225510658911748683)
              ·
                refine ⟨40256863838265988367623025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26837909225510658911748683 40256863838265988367623025)
                ·
                  refine ⟨30192647878699491275717269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40256863838265988367623025 30192647878699491275717269)
                  ·
                    refine ⟨1415280369314038653549247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30192647878699491275717269 1415280369314038653549247)
                    ·
                      rfl

theorem cell22_4134373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_4134373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134373 prefixEnd_4134373 := by exact prefixLift 4134373
  have htrace : WordTrace (prefixWord ++ tailWord_4134373) baseStart_4134373 baseEnd_4134373 := by
    simpa [prefixWord, tailWord_4134373, baseEnd_4134373] using wordTrace_append hprefix tailTrace_4134373
  have hstable : (prefixWord ++ tailWord_4134373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134373).length < 2 ^ (prefixWord ++ tailWord_4134373).sum := by decide
  have hdescent : baseEnd_4134373 < baseStart_4134373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134433 : List Nat := [1, 2, 3, 2, 2, 2, 1, 3, 6]
def baseStart_4134433 : Nat := 118140960795 + 4134433 * 2 ^ 59
def prefixEnd_4134433 : Nat := 4983230072969 + 3 ^ 40 * 4134433 * 2
def baseEnd_4134433 : Nat := 471766969513406165683021

theorem tailTrace_4134433 : CollatzResearch.WordTrace tailWord_4134433 prefixEnd_4134433 471766969513406165683021 := by
  unfold tailWord_4134433
  simp only [CollatzResearch.WordTrace]
  refine ⟨150795159830662820785623953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100530106553775213857082635 150795159830662820785623953)
  ·
    refine ⟨113096369872997115589217965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150795159830662820785623953 113096369872997115589217965)
    ·
      refine ⟨42411138702373918345956737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113096369872997115589217965 42411138702373918345956737)
      ·
        refine ⟨31808354026780438759467553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42411138702373918345956737 31808354026780438759467553)
        ·
          refine ⟨23856265520085329069600665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31808354026780438759467553 23856265520085329069600665)
          ·
            refine ⟨17892199140063996802200499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23856265520085329069600665 17892199140063996802200499)
            ·
              refine ⟨26838298710095995203300749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17892199140063996802200499 26838298710095995203300749)
              ·
                refine ⟨10064362016285998201237781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26838298710095995203300749 10064362016285998201237781)
                ·
                  refine ⟨471766969513406165683021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10064362016285998201237781 471766969513406165683021)
                  ·
                    rfl

theorem cell22_4134433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 6].length) (baseStart_4134433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134433 prefixEnd_4134433 := by exact prefixLift 4134433
  have htrace : WordTrace (prefixWord ++ tailWord_4134433) baseStart_4134433 baseEnd_4134433 := by
    simpa [prefixWord, tailWord_4134433, baseEnd_4134433] using wordTrace_append hprefix tailTrace_4134433
  have hstable : (prefixWord ++ tailWord_4134433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134433).length < 2 ^ (prefixWord ++ tailWord_4134433).sum := by decide
  have hdescent : baseEnd_4134433 < baseStart_4134433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134463 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 1, 6]
def baseStart_4134463 : Nat := 118140960795 + 4134463 * 2 ^ 59
def prefixEnd_4134463 : Nat := 4983230072969 + 3 ^ 40 * 4134463 * 2
def baseEnd_4134463 : Nat := 1415311178153308418798971

theorem tailTrace_4134463 : CollatzResearch.WordTrace tailWord_4134463 prefixEnd_4134463 1415311178153308418798971 := by
  unfold tailWord_4134463
  simp only [CollatzResearch.WordTrace]
  refine ⟨150796254020554135909216043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100530836013702757272810695 150796254020554135909216043)
  ·
    refine ⟨226194381030831203863824065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150796254020554135909216043 226194381030831203863824065)
    ·
      refine ⟨169645785773123402897868049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226194381030831203863824065 169645785773123402897868049)
      ·
        refine ⟨127234339329842552173401037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169645785773123402897868049 127234339329842552173401037)
        ·
          refine ⟨47712877248690957065025389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127234339329842552173401037 47712877248690957065025389)
          ·
            refine ⟨17892328968259108899384521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47712877248690957065025389 17892328968259108899384521)
            ·
              refine ⟨13419246726194331674538391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17892328968259108899384521 13419246726194331674538391)
              ·
                refine ⟨20128870089291497511807587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13419246726194331674538391 20128870089291497511807587)
                ·
                  refine ⟨30193305133937246267711381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20128870089291497511807587 30193305133937246267711381)
                  ·
                    refine ⟨1415311178153308418798971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30193305133937246267711381 1415311178153308418798971)
                    ·
                      rfl

theorem cell22_4134463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_4134463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134463 prefixEnd_4134463 := by exact prefixLift 4134463
  have htrace : WordTrace (prefixWord ++ tailWord_4134463) baseStart_4134463 baseEnd_4134463 := by
    simpa [prefixWord, tailWord_4134463, baseEnd_4134463] using wordTrace_append hprefix tailTrace_4134463
  have hstable : (prefixWord ++ tailWord_4134463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134463).length < 2 ^ (prefixWord ++ tailWord_4134463).sum := by decide
  have hdescent : baseEnd_4134463 < baseStart_4134463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134465 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 6, 3]
def baseStart_4134465 : Nat := 118140960795 + 4134465 * 2 ^ 59
def prefixEnd_4134465 : Nat := 4983230072969 + 3 ^ 40 * 4134465 * 2
def baseEnd_4134465 : Nat := 1415311862794181080248965

theorem tailTrace_4134465 : CollatzResearch.WordTrace tailWord_4134465 prefixEnd_4134465 1415311862794181080248965 := by
  unfold tailWord_4134465
  simp only [CollatzResearch.WordTrace]
  refine ⟨150796326966546890250788849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100530884644364593500525899 150796326966546890250788849)
  ·
    refine ⟨113097245224910167688091637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150796326966546890250788849 113097245224910167688091637)
    ·
      refine ⟨10602866739835328220758591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113097245224910167688091637 10602866739835328220758591)
      ·
        refine ⟨15904300109752992331137887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10602866739835328220758591 15904300109752992331137887)
        ·
          refine ⟨23856450164629488496706831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15904300109752992331137887 23856450164629488496706831)
          ·
            refine ⟨35784675246944232745060247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23856450164629488496706831 35784675246944232745060247)
            ·
              refine ⟨53677012870416349117590371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35784675246944232745060247 53677012870416349117590371)
              ·
                refine ⟨80515519305624523676385557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53677012870416349117590371 80515519305624523676385557)
                ·
                  refine ⟨3774164967451149547330573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80515519305624523676385557 3774164967451149547330573)
                  ·
                    refine ⟨1415311862794181080248965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3774164967451149547330573 1415311862794181080248965)
                    ·
                      rfl

theorem cell22_4134465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_4134465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134465 prefixEnd_4134465 := by exact prefixLift 4134465
  have htrace : WordTrace (prefixWord ++ tailWord_4134465) baseStart_4134465 baseEnd_4134465 := by
    simpa [prefixWord, tailWord_4134465, baseEnd_4134465] using wordTrace_append hprefix tailTrace_4134465
  have hstable : (prefixWord ++ tailWord_4134465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134465).length < 2 ^ (prefixWord ++ tailWord_4134465).sum := by decide
  have hdescent : baseEnd_4134465 < baseStart_4134465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134499 : List Nat := [1, 1, 1, 5, 1, 5, 2, 1, 2, 3]
def baseStart_4134499 : Nat := 118140960795 + 4134499 * 2 ^ 59
def prefixEnd_4134499 : Nat := 4983230072969 + 3 ^ 40 * 4134499 * 2
def baseEnd_4134499 : Nat := 1415323501689016324898861

theorem tailTrace_4134499 : CollatzResearch.WordTrace tailWord_4134499 prefixEnd_4134499 1415323501689016324898861 := by
  unfold tailWord_4134499
  simp only [CollatzResearch.WordTrace]
  refine ⟨150797567048423714057526551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100531711365615809371684367 150797567048423714057526551)
  ·
    refine ⟨226196350572635571086289827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150797567048423714057526551 226196350572635571086289827)
    ·
      refine ⟨339294525858953356629434741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226196350572635571086289827 339294525858953356629434741)
      ·
        refine ⟨31808861799276877184009507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 339294525858953356629434741 31808861799276877184009507)
        ·
          refine ⟨47713292698915315776014261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31808861799276877184009507 47713292698915315776014261)
          ·
            refine ⟨4473121190523310854001337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47713292698915315776014261 4473121190523310854001337)
            ·
              refine ⟨3354840892892483140501003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4473121190523310854001337 3354840892892483140501003)
              ·
                refine ⟨5032261339338724710751505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3354840892892483140501003 5032261339338724710751505)
                ·
                  refine ⟨3774196004504043533063629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5032261339338724710751505 3774196004504043533063629)
                  ·
                    refine ⟨1415323501689016324898861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3774196004504043533063629 1415323501689016324898861)
                    ·
                      rfl

theorem cell22_4134499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 2, 3].length) (baseStart_4134499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134499 prefixEnd_4134499 := by exact prefixLift 4134499
  have htrace : WordTrace (prefixWord ++ tailWord_4134499) baseStart_4134499 baseEnd_4134499 := by
    simpa [prefixWord, tailWord_4134499, baseEnd_4134499] using wordTrace_append hprefix tailTrace_4134499
  have hstable : (prefixWord ++ tailWord_4134499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134499).length < 2 ^ (prefixWord ++ tailWord_4134499).sum := by decide
  have hdescent : baseEnd_4134499 < baseStart_4134499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134540 : List Nat := [2, 2, 1, 2, 1, 1, 6, 2, 5]
def baseStart_4134540 : Nat := 118140960795 + 4134540 * 2 ^ 59
def prefixEnd_4134540 : Nat := 4983230072969 + 3 ^ 40 * 4134540 * 2
def baseEnd_4134540 : Nat := 471779178942301961541245

theorem tailTrace_4134540 : CollatzResearch.WordTrace tailWord_4134540 prefixEnd_4134540 471779178942301961541245 := by
  unfold tailWord_4134540
  simp only [CollatzResearch.WordTrace]
  refine ⟨75399531220637589029884537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100532708294183452039846049 75399531220637589029884537)
  ·
    refine ⟨56549648415478191772413403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75399531220637589029884537 56549648415478191772413403)
    ·
      refine ⟨84824472623217287658620105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56549648415478191772413403 84824472623217287658620105)
      ·
        refine ⟨63618354467412965743965079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84824472623217287658620105 63618354467412965743965079)
        ·
          refine ⟨95427531701119448615947619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63618354467412965743965079 95427531701119448615947619)
          ·
            refine ⟨143141297551679172923921429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95427531701119448615947619 143141297551679172923921429)
            ·
              refine ⟨6709748322734961230808817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 143141297551679172923921429 6709748322734961230808817)
              ·
                refine ⟨5032311242051220923106613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6709748322734961230808817 5032311242051220923106613)
                ·
                  refine ⟨471779178942301961541245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5032311242051220923106613 471779178942301961541245)
                  ·
                    rfl

theorem cell22_4134540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_4134540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134540 prefixEnd_4134540 := by exact prefixLift 4134540
  have htrace : WordTrace (prefixWord ++ tailWord_4134540) baseStart_4134540 baseEnd_4134540 := by
    simpa [prefixWord, tailWord_4134540, baseEnd_4134540] using wordTrace_append hprefix tailTrace_4134540
  have hstable : (prefixWord ++ tailWord_4134540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134540).length < 2 ^ (prefixWord ++ tailWord_4134540).sum := by decide
  have hdescent : baseEnd_4134540 < baseStart_4134540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134602 : List Nat := [3, 1, 2, 1, 5, 1, 2, 1, 6]
def baseStart_4134602 : Nat := 118140960795 + 4134602 * 2 ^ 59
def prefixEnd_4134602 : Nat := 4983230072969 + 3 ^ 40 * 4134602 * 2
def baseEnd_4134602 : Nat := 471786253564652796524515

theorem tailTrace_4134602 : CollatzResearch.WordTrace tailWord_4134602 prefixEnd_4134602 471786253564652796524515 := by
  unfold tailWord_4134602
  simp only [CollatzResearch.WordTrace]
  refine ⟨37700330941762640662131515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100534215844700375099017373 37700330941762640662131515)
  ·
    refine ⟨56550496412643960993197273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37700330941762640662131515 56550496412643960993197273)
    ·
      refine ⟨42412872309482970744897955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56550496412643960993197273 42412872309482970744897955)
      ·
        refine ⟨63619308464224456117346933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42412872309482970744897955 63619308464224456117346933)
        ·
          refine ⟨5964310168521042761001275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63619308464224456117346933 5964310168521042761001275)
          ·
            refine ⟨8946465252781564141501913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5964310168521042761001275 8946465252781564141501913)
            ·
              refine ⟨6709848939586173106126435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8946465252781564141501913 6709848939586173106126435)
              ·
                refine ⟨10064773409379259659189653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6709848939586173106126435 10064773409379259659189653)
                ·
                  refine ⟨471786253564652796524515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10064773409379259659189653 471786253564652796524515)
                  ·
                    rfl

theorem cell22_4134602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_4134602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134602 prefixEnd_4134602 := by exact prefixLift 4134602
  have htrace : WordTrace (prefixWord ++ tailWord_4134602) baseStart_4134602 baseEnd_4134602 := by
    simpa [prefixWord, tailWord_4134602, baseEnd_4134602] using wordTrace_append hprefix tailTrace_4134602
  have hstable : (prefixWord ++ tailWord_4134602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134602).length < 2 ^ (prefixWord ++ tailWord_4134602).sum := by decide
  have hdescent : baseEnd_4134602 < baseStart_4134602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134617 : List Nat := [1, 2, 1, 2, 3, 5, 1, 1, 1, 5]
def baseStart_4134617 : Nat := 118140960795 + 4134617 * 2 ^ 59
def prefixEnd_4134617 : Nat := 4983230072969 + 3 ^ 40 * 4134617 * 2
def baseEnd_4134617 : Nat := 1415363895500503350448499

theorem tailTrace_4134617 : CollatzResearch.WordTrace tailWord_4134617 prefixEnd_4134617 1415363895500503350448499 := by
  unfold tailWord_4134617
  simp only [CollatzResearch.WordTrace]
  refine ⟨150801870861996220210322105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100534580574664146806881403 150801870861996220210322105)
  ·
    refine ⟨113101403146497165157741579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150801870861996220210322105 113101403146497165157741579)
    ·
      refine ⟨169652104719745747736612369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113101403146497165157741579 169652104719745747736612369)
      ·
        refine ⟨127239078539809310802459277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169652104719745747736612369 127239078539809310802459277)
        ·
          refine ⟨47714654452428491550922229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127239078539809310802459277 47714654452428491550922229)
          ·
            refine ⟨4473248854915171082898959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47714654452428491550922229 4473248854915171082898959)
            ·
              refine ⟨6709873282372756624348439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4473248854915171082898959 6709873282372756624348439)
              ·
                refine ⟨10064809923559134936522659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6709873282372756624348439 10064809923559134936522659)
                ·
                  refine ⟨15097214885338702404783989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10064809923559134936522659 15097214885338702404783989)
                  ·
                    refine ⟨1415363895500503350448499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15097214885338702404783989 1415363895500503350448499)
                    ·
                      rfl

theorem cell22_4134617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 5].length) (baseStart_4134617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134617 prefixEnd_4134617 := by exact prefixLift 4134617
  have htrace : WordTrace (prefixWord ++ tailWord_4134617) baseStart_4134617 baseEnd_4134617 := by
    simpa [prefixWord, tailWord_4134617, baseEnd_4134617] using wordTrace_append hprefix tailTrace_4134617
  have hstable : (prefixWord ++ tailWord_4134617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134617).length < 2 ^ (prefixWord ++ tailWord_4134617).sum := by decide
  have hdescent : baseEnd_4134617 < baseStart_4134617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134621 : List Nat := [1, 4, 3, 3, 1, 1, 2, 2, 1, 4]
def baseStart_4134621 : Nat := 118140960795 + 4134621 * 2 ^ 59
def prefixEnd_4134621 : Nat := 4983230072969 + 3 ^ 40 * 4134621 * 2
def baseEnd_4134621 : Nat := 1415365264782248673348487

theorem tailTrace_4134621 : CollatzResearch.WordTrace tailWord_4134621 prefixEnd_4134621 1415365264782248673348487 := by
  unfold tailWord_4134621
  simp only [CollatzResearch.WordTrace]
  refine ⟨150802016753981728893467717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100534677835987819262311811 150802016753981728893467717)
  ·
    refine ⟨28275378141371574167525197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150802016753981728893467717 28275378141371574167525197)
    ·
      refine ⟨10603266803014340312821949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28275378141371574167525197 10603266803014340312821949)
      ·
        refine ⟨3976225051130377617308231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10603266803014340312821949 3976225051130377617308231)
        ·
          refine ⟨5964337576695566425962347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3976225051130377617308231 5964337576695566425962347)
          ·
            refine ⟨8946506365043349638943521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5964337576695566425962347 8946506365043349638943521)
            ·
              refine ⟨6709879773782512229207641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8946506365043349638943521 6709879773782512229207641)
              ·
                refine ⟨5032409830336884171905731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6709879773782512229207641 5032409830336884171905731)
                ·
                  refine ⟨7548614745505326257858597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5032409830336884171905731 7548614745505326257858597)
                  ·
                    refine ⟨1415365264782248673348487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7548614745505326257858597 1415365264782248673348487)
                    ·
                      rfl

theorem cell22_4134621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_4134621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134621 prefixEnd_4134621 := by exact prefixLift 4134621
  have htrace : WordTrace (prefixWord ++ tailWord_4134621) baseStart_4134621 baseEnd_4134621 := by
    simpa [prefixWord, tailWord_4134621, baseEnd_4134621] using wordTrace_append hprefix tailTrace_4134621
  have hstable : (prefixWord ++ tailWord_4134621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134621).length < 2 ^ (prefixWord ++ tailWord_4134621).sum := by decide
  have hdescent : baseEnd_4134621 < baseStart_4134621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134709 : List Nat := [1, 3, 3, 1, 4, 1, 2, 2, 5]
def baseStart_4134709 : Nat := 118140960795 + 4134709 * 2 ^ 59
def prefixEnd_4134709 : Nat := 4983230072969 + 3 ^ 40 * 4134709 * 2
def baseEnd_4134709 : Nat := 471798462993548592382739

theorem tailTrace_4134709 : CollatzResearch.WordTrace tailWord_4134709 prefixEnd_4134709 471798462993548592382739 := by
  unfold tailWord_4134709
  simp only [CollatzResearch.WordTrace]
  refine ⟨150805226377662919922671181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100536817585108613281780787 150805226377662919922671181)
  ·
    refine ⟨56551959891623594971001693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150805226377662919922671181 56551959891623594971001693)
    ·
      refine ⟨21206984959358848114125635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56551959891623594971001693 21206984959358848114125635)
      ·
        refine ⟨31810477439038272171188453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21206984959358848114125635 31810477439038272171188453)
        ·
          refine ⟨5964464519819676032097835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31810477439038272171188453 5964464519819676032097835)
          ·
            refine ⟨8946696779729514048146753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5964464519819676032097835 8946696779729514048146753)
            ·
              refine ⟨6710022584797135536110065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8946696779729514048146753 6710022584797135536110065)
              ·
                refine ⟨5032516938597851652082549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6710022584797135536110065 5032516938597851652082549)
                ·
                  refine ⟨471798462993548592382739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5032516938597851652082549 471798462993548592382739)
                  ·
                    rfl

theorem cell22_4134709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_4134709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134709 prefixEnd_4134709 := by exact prefixLift 4134709
  have htrace : WordTrace (prefixWord ++ tailWord_4134709) baseStart_4134709 baseEnd_4134709 := by
    simpa [prefixWord, tailWord_4134709, baseEnd_4134709] using wordTrace_append hprefix tailTrace_4134709
  have hstable : (prefixWord ++ tailWord_4134709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134709).length < 2 ^ (prefixWord ++ tailWord_4134709).sum := by decide
  have hdescent : baseEnd_4134709 < baseStart_4134709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134713 : List Nat := [1, 2, 1, 7, 1, 1, 1, 4, 1, 3]
def baseStart_4134713 : Nat := 118140960795 + 4134713 * 2 ^ 59
def prefixEnd_4134713 : Nat := 4983230072969 + 3 ^ 40 * 4134713 * 2
def baseEnd_4134713 : Nat := 1415396758262391100048205

theorem tailTrace_4134713 : CollatzResearch.WordTrace tailWord_4134713 prefixEnd_4134713 1415396758262391100048205 := by
  unfold tailWord_4134713
  simp only [CollatzResearch.WordTrace]
  refine ⟨150805372269648428605816793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100536914846432285737211195 150805372269648428605816793)
  ·
    refine ⟨113104029202236321454362595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150805372269648428605816793 113104029202236321454362595)
    ·
      refine ⟨169656043803354482181543893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113104029202236321454362595 169656043803354482181543893)
      ·
        refine ⟨3976313526641120676129935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 169656043803354482181543893 3976313526641120676129935)
        ·
          refine ⟨5964470289961681014194903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3976313526641120676129935 5964470289961681014194903)
          ·
            refine ⟨8946705434942521521292355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5964470289961681014194903 8946705434942521521292355)
            ·
              refine ⟨13420058152413782281938533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8946705434942521521292355 13420058152413782281938533)
              ·
                refine ⟨2516260903577584177863475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13420058152413782281938533 2516260903577584177863475)
                ·
                  refine ⟨3774391355366376266795213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2516260903577584177863475 3774391355366376266795213)
                  ·
                    refine ⟨1415396758262391100048205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3774391355366376266795213 1415396758262391100048205)
                    ·
                      rfl

theorem cell22_4134713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 1, 3].length) (baseStart_4134713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134713 prefixEnd_4134713 := by exact prefixLift 4134713
  have htrace : WordTrace (prefixWord ++ tailWord_4134713) baseStart_4134713 baseEnd_4134713 := by
    simpa [prefixWord, tailWord_4134713, baseEnd_4134713] using wordTrace_append hprefix tailTrace_4134713
  have hstable : (prefixWord ++ tailWord_4134713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134713).length < 2 ^ (prefixWord ++ tailWord_4134713).sum := by decide
  have hdescent : baseEnd_4134713 < baseStart_4134713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134726 : List Nat := [6, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_4134726 : Nat := 118140960795 + 4134726 * 2 ^ 59
def prefixEnd_4134726 : Nat := 4983230072969 + 3 ^ 40 * 4134726 * 2
def baseEnd_4134726 : Nat := 471800402809354466491055

theorem tailTrace_4134726 : CollatzResearch.WordTrace tailWord_4134726 prefixEnd_4134726 471800402809354466491055 := by
  unfold tailWord_4134726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4712682700581291619563751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100537230945734221217360021 4712682700581291619563751)
  ·
    refine ⟨7069024050871937429345627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4712682700581291619563751 7069024050871937429345627)
    ·
      refine ⟨10603536076307906144018441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7069024050871937429345627 10603536076307906144018441)
      ·
        refine ⟨7952652057230929608013831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10603536076307906144018441 7952652057230929608013831)
        ·
          refine ⟨11928978085846394412020747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7952652057230929608013831 11928978085846394412020747)
          ·
            refine ⟨17893467128769591618031121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11928978085846394412020747 17893467128769591618031121)
            ·
              refine ⟨13420100346577193713523341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17893467128769591618031121 13420100346577193713523341)
              ·
                refine ⟨5032537629966447642571253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13420100346577193713523341 5032537629966447642571253)
                ·
                  refine ⟨471800402809354466491055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5032537629966447642571253 471800402809354466491055)
                  ·
                    rfl

theorem cell22_4134726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_4134726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134726 prefixEnd_4134726 := by exact prefixLift 4134726
  have htrace : WordTrace (prefixWord ++ tailWord_4134726) baseStart_4134726 baseEnd_4134726 := by
    simpa [prefixWord, tailWord_4134726, baseEnd_4134726] using wordTrace_append hprefix tailTrace_4134726
  have hstable : (prefixWord ++ tailWord_4134726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134726).length < 2 ^ (prefixWord ++ tailWord_4134726).sum := by decide
  have hdescent : baseEnd_4134726 < baseStart_4134726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134737 : List Nat := [1, 2, 2, 1, 5, 2, 1, 2, 6]
def baseStart_4134737 : Nat := 118140960795 + 4134737 * 2 ^ 59
def prefixEnd_4134737 : Nat := 4983230072969 + 3 ^ 40 * 4134737 * 2
def baseEnd_4134737 : Nat := 471801657984287679149377

theorem tailTrace_4134737 : CollatzResearch.WordTrace tailWord_4134737 prefixEnd_4134737 471801657984287679149377 := by
  unfold tailWord_4134737
  simp only [CollatzResearch.WordTrace]
  refine ⟨150806247621561480704690465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100537498414374320469793643 150806247621561480704690465)
  ·
    refine ⟨113104685716171110528517849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150806247621561480704690465 113104685716171110528517849)
    ·
      refine ⟨84828514287128332896388387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113104685716171110528517849 84828514287128332896388387)
      ·
        refine ⟨127242771430692499344582581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84828514287128332896388387 127242771430692499344582581)
        ·
          refine ⟨11929009821627421813554617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127242771430692499344582581 11929009821627421813554617)
          ·
            refine ⟨8946757366220566360165963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11929009821627421813554617 8946757366220566360165963)
            ·
              refine ⟨13420136049330849540248945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8946757366220566360165963 13420136049330849540248945)
              ·
                refine ⟨10065102036998137155186709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13420136049330849540248945 10065102036998137155186709)
                ·
                  refine ⟨471801657984287679149377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10065102036998137155186709 471801657984287679149377)
                  ·
                    rfl

theorem cell22_4134737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 6].length) (baseStart_4134737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134737 prefixEnd_4134737 := by exact prefixLift 4134737
  have htrace : WordTrace (prefixWord ++ tailWord_4134737) baseStart_4134737 baseEnd_4134737 := by
    simpa [prefixWord, tailWord_4134737, baseEnd_4134737] using wordTrace_append hprefix tailTrace_4134737
  have hstable : (prefixWord ++ tailWord_4134737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134737).length < 2 ^ (prefixWord ++ tailWord_4134737).sum := by decide
  have hdescent : baseEnd_4134737 < baseStart_4134737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134752 : List Nat := [2, 1, 1, 3, 3, 2, 2, 2, 1, 5]
def baseStart_4134752 : Nat := 118140960795 + 4134752 * 2 ^ 59
def prefixEnd_4134752 : Nat := 4983230072969 + 3 ^ 40 * 4134752 * 2
def baseEnd_4134752 : Nat := 1415410108759407998323085

theorem tailTrace_4134752 : CollatzResearch.WordTrace tailWord_4134752 prefixEnd_4134752 1415410108759407998323085 := by
  unfold tailWord_4134752
  simp only [CollatzResearch.WordTrace]
  refine ⟨75403397358253569133243255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100537863144338092177657673 75403397358253569133243255)
  ·
    refine ⟨113105096037380353699864883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75403397358253569133243255 113105096037380353699864883)
    ·
      refine ⟨169657644056070530549797325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113105096037380353699864883 169657644056070530549797325)
      ·
        refine ⟨63621616521026448956173997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169657644056070530549797325 63621616521026448956173997)
        ·
          refine ⟨23858106195384918358565249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63621616521026448956173997 23858106195384918358565249)
          ·
            refine ⟨17893579646538688768923937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23858106195384918358565249 17893579646538688768923937)
            ·
              refine ⟨13420184734904016576692953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17893579646538688768923937 13420184734904016576692953)
              ·
                refine ⟨10065138551178012432519715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13420184734904016576692953 10065138551178012432519715)
                ·
                  refine ⟨15097707826767018648779573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10065138551178012432519715 15097707826767018648779573)
                  ·
                    refine ⟨1415410108759407998323085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15097707826767018648779573 1415410108759407998323085)
                    ·
                      rfl

theorem cell22_4134752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_4134752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134752 prefixEnd_4134752 := by exact prefixLift 4134752
  have htrace : WordTrace (prefixWord ++ tailWord_4134752) baseStart_4134752 baseEnd_4134752 := by
    simpa [prefixWord, tailWord_4134752, baseEnd_4134752] using wordTrace_append hprefix tailTrace_4134752
  have hstable : (prefixWord ++ tailWord_4134752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134752).length < 2 ^ (prefixWord ++ tailWord_4134752).sum := by decide
  have hdescent : baseEnd_4134752 < baseStart_4134752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134857 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 3, 4]
def baseStart_4134857 : Nat := 118140960795 + 4134857 * 2 ^ 59
def prefixEnd_4134857 : Nat := 4983230072969 + 3 ^ 40 * 4134857 * 2
def baseEnd_4134857 : Nat := 1415446052405222724447763

theorem tailTrace_4134857 : CollatzResearch.WordTrace tailWord_4134857 prefixEnd_4134857 1415446052405222724447763 := by
  unfold tailWord_4134857
  simp only [CollatzResearch.WordTrace]
  refine ⟨150810624381126741199058825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100540416254084494132705883 150810624381126741199058825)
  ·
    refine ⟨113107968285845055899294119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150810624381126741199058825 113107968285845055899294119)
    ·
      refine ⟨169661952428767583848941179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113107968285845055899294119 169661952428767583848941179)
      ·
        refine ⟨254492928643151375773411769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169661952428767583848941179 254492928643151375773411769)
        ·
          refine ⟨190869696482363531830058827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254492928643151375773411769 190869696482363531830058827)
          ·
            refine ⟨286304544723545297745088241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190869696482363531830058827 286304544723545297745088241)
            ·
              refine ⟨214728408542658973308816181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286304544723545297745088241 214728408542658973308816181)
              ·
                refine ⟨20130788300874278747701517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214728408542658973308816181 20130788300874278747701517)
                ·
                  refine ⟨7549045612827854530388069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20130788300874278747701517 7549045612827854530388069)
                  ·
                    refine ⟨1415446052405222724447763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7549045612827854530388069 1415446052405222724447763)
                    ·
                      rfl

theorem cell22_4134857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_4134857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134857 prefixEnd_4134857 := by exact prefixLift 4134857
  have htrace : WordTrace (prefixWord ++ tailWord_4134857) baseStart_4134857 baseEnd_4134857 := by
    simpa [prefixWord, tailWord_4134857, baseEnd_4134857] using wordTrace_append hprefix tailTrace_4134857
  have hstable : (prefixWord ++ tailWord_4134857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134857).length < 2 ^ (prefixWord ++ tailWord_4134857).sum := by decide
  have hdescent : baseEnd_4134857 < baseStart_4134857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134919 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 1, 6]
def baseStart_4134919 : Nat := 118140960795 + 4134919 * 2 ^ 59
def prefixEnd_4134919 : Nat := 4983230072969 + 3 ^ 40 * 4134919 * 2
def baseEnd_4134919 : Nat := 1415467276272275229397573

theorem tailTrace_4134919 : CollatzResearch.WordTrace tailWord_4134919 prefixEnd_4134919 1415467276272275229397573 := by
  unfold tailWord_4134919
  simp only [CollatzResearch.WordTrace]
  refine ⟨150812885706902125787815811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100541923804601417191877207 150812885706902125787815811)
  ·
    refine ⟨226219328560353188681723717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150812885706902125787815811 226219328560353188681723717)
    ·
      refine ⟨42416124105066222877823197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226219328560353188681723717 42416124105066222877823197)
      ·
        refine ⟨15906046539399833579183699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42416124105066222877823197 15906046539399833579183699)
        ·
          refine ⟨23859069809099750368775549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15906046539399833579183699 23859069809099750368775549)
          ·
            refine ⟨8947151178412406388290831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23859069809099750368775549 8947151178412406388290831)
            ·
              refine ⟨13420726767618609582436247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8947151178412406388290831 13420726767618609582436247)
              ·
                refine ⟨20131090151427914373654371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13420726767618609582436247 20131090151427914373654371)
                ·
                  refine ⟨30196635227141871560481557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20131090151427914373654371 30196635227141871560481557)
                  ·
                    refine ⟨1415467276272275229397573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30196635227141871560481557 1415467276272275229397573)
                    ·
                      rfl

theorem cell22_4134919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_4134919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134919 prefixEnd_4134919 := by exact prefixLift 4134919
  have htrace : WordTrace (prefixWord ++ tailWord_4134919) baseStart_4134919 baseEnd_4134919 := by
    simpa [prefixWord, tailWord_4134919, baseEnd_4134919] using wordTrace_append hprefix tailTrace_4134919
  have hstable : (prefixWord ++ tailWord_4134919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134919).length < 2 ^ (prefixWord ++ tailWord_4134919).sum := by decide
  have hdescent : baseEnd_4134919 < baseStart_4134919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134938 : List Nat := [3, 1, 1, 3, 1, 5, 1, 2, 2, 3]
def baseStart_4134938 : Nat := 118140960795 + 4134938 * 2 ^ 59
def prefixEnd_4134938 : Nat := 4983230072969 + 3 ^ 40 * 4134938 * 2
def baseEnd_4134938 : Nat := 1415473780360565513172515

theorem tailTrace_4134938 : CollatzResearch.WordTrace tailWord_4134938 prefixEnd_4134938 1415473780360565513172515 := by
  unfold tailWord_4134938
  simp only [CollatzResearch.WordTrace]
  refine ⟨37703394673458323008189367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100542385795888861355171645 37703394673458323008189367)
  ·
    refine ⟨56555092010187484512284051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37703394673458323008189367 56555092010187484512284051)
    ·
      refine ⟨84832638015281226768426077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56555092010187484512284051 84832638015281226768426077)
      ·
        refine ⟨31812239255730460038159779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84832638015281226768426077 31812239255730460038159779)
        ·
          refine ⟨47718358883595690057239669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31812239255730460038159779 47718358883595690057239669)
          ·
            refine ⟨4473596145337095942866219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47718358883595690057239669 4473596145337095942866219)
            ·
              refine ⟨6710394218005643914299329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4473596145337095942866219 6710394218005643914299329)
              ·
                refine ⟨5032795663504232935724497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6710394218005643914299329 5032795663504232935724497)
                ·
                  refine ⟨3774596747628174701793373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5032795663504232935724497 3774596747628174701793373)
                  ·
                    refine ⟨1415473780360565513172515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3774596747628174701793373 1415473780360565513172515)
                    ·
                      rfl

theorem cell22_4134938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_4134938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134938 prefixEnd_4134938 := by exact prefixLift 4134938
  have htrace : WordTrace (prefixWord ++ tailWord_4134938) baseStart_4134938 baseEnd_4134938 := by
    simpa [prefixWord, tailWord_4134938, baseEnd_4134938] using wordTrace_append hprefix tailTrace_4134938
  have hstable : (prefixWord ++ tailWord_4134938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134938).length < 2 ^ (prefixWord ++ tailWord_4134938).sum := by decide
  have hdescent : baseEnd_4134938 < baseStart_4134938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4134968 : List Nat := [2, 1, 2, 1, 7, 1, 2, 6]
def baseStart_4134968 : Nat := 118140960795 + 4134968 * 2 ^ 59
def prefixEnd_4134968 : Nat := 4983230072969 + 3 ^ 40 * 4134968 * 2
def baseEnd_4134968 : Nat := 157276005552628381658047

theorem tailTrace_4134968 : CollatzResearch.WordTrace tailWord_4134968 prefixEnd_4134968 157276005552628381658047 := by
  unfold tailWord_4134968
  simp only [CollatzResearch.WordTrace]
  refine ⟨75407336441862303578174779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100543115255816404770899705 75407336441862303578174779)
  ·
    refine ⟨113111004662793455367262169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75407336441862303578174779 113111004662793455367262169)
    ·
      refine ⟨84833253497095091525446627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113111004662793455367262169 84833253497095091525446627)
      ·
        refine ⟨127249880245642637288169941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84833253497095091525446627 127249880245642637288169941)
        ·
          refine ⟨2982419068257249311441483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 127249880245642637288169941 2982419068257249311441483)
          ·
            refine ⟨4473628602385873967162225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2982419068257249311441483 4473628602385873967162225)
            ·
              refine ⟨3355221451789405475371669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4473628602385873967162225 3355221451789405475371669)
              ·
                refine ⟨157276005552628381658047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3355221451789405475371669 157276005552628381658047)
                ·
                  rfl

theorem cell22_4134968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 6].length) (baseStart_4134968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4134968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4134968 prefixEnd_4134968 := by exact prefixLift 4134968
  have htrace : WordTrace (prefixWord ++ tailWord_4134968) baseStart_4134968 baseEnd_4134968 := by
    simpa [prefixWord, tailWord_4134968, baseEnd_4134968] using wordTrace_append hprefix tailTrace_4134968
  have hstable : (prefixWord ++ tailWord_4134968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4134968).length < 2 ^ (prefixWord ++ tailWord_4134968).sum := by decide
  have hdescent : baseEnd_4134968 < baseStart_4134968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4134968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135000 : List Nat := [2, 1, 2, 2, 1, 5, 3, 2, 1, 3]
def baseStart_4135000 : Nat := 118140960795 + 4135000 * 2 ^ 59
def prefixEnd_4135000 : Nat := 4983230072969 + 3 ^ 40 * 4135000 * 2
def baseEnd_4135000 : Nat := 1415495004227618018122325

theorem tailTrace_4135000 : CollatzResearch.WordTrace tailWord_4135000 prefixEnd_4135000 1415495004227618018122325 := by
  unfold tailWord_4135000
  simp only [CollatzResearch.WordTrace]
  refine ⟨75407920009804338310757227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100543893346405784414342969 75407920009804338310757227)
  ·
    refine ⟨113111880014706507466135841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75407920009804338310757227 113111880014706507466135841)
    ·
      refine ⟨84833910011029880599601881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113111880014706507466135841 84833910011029880599601881)
      ·
        refine ⟨63625432508272410449701411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84833910011029880599601881 63625432508272410449701411)
        ·
          refine ⟨95438148762408615674552117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63625432508272410449701411 95438148762408615674552117)
          ·
            refine ⟨8947326446475807719489261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95438148762408615674552117 8947326446475807719489261)
            ·
              refine ⟨3355247417428427894808473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8947326446475807719489261 3355247417428427894808473)
              ·
                refine ⟨2516435563071320921106355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3355247417428427894808473 2516435563071320921106355)
                ·
                  refine ⟨3774653344606981381659533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2516435563071320921106355 3774653344606981381659533)
                  ·
                    refine ⟨1415495004227618018122325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3774653344606981381659533 1415495004227618018122325)
                    ·
                      rfl

theorem cell22_4135000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 1, 3].length) (baseStart_4135000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135000 prefixEnd_4135000 := by exact prefixLift 4135000
  have htrace : WordTrace (prefixWord ++ tailWord_4135000) baseStart_4135000 baseEnd_4135000 := by
    simpa [prefixWord, tailWord_4135000, baseEnd_4135000] using wordTrace_append hprefix tailTrace_4135000
  have hstable : (prefixWord ++ tailWord_4135000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135000).length < 2 ^ (prefixWord ++ tailWord_4135000).sum := by decide
  have hdescent : baseEnd_4135000 < baseStart_4135000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135006 : List Nat := [4, 4, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_4135006 : Nat := 118140960795 + 4135006 * 2 ^ 59
def prefixEnd_4135006 : Nat := 4983230072969 + 3 ^ 40 * 4135006 * 2
def baseEnd_4135006 : Nat := 1415497058150236002472307

theorem tailTrace_4135006 : CollatzResearch.WordTrace tailWord_4135006 prefixEnd_4135006 1415497058150236002472307 := by
  unfold tailWord_4135006
  simp only [CollatzResearch.WordTrace]
  refine ⟨18852007357198367455779109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100544039238391293097488581 18852007357198367455779109)
  ·
    refine ⟨3534751379474693897958583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18852007357198367455779109 3534751379474693897958583)
    ·
      refine ⟨5302127069212040846937875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3534751379474693897958583 5302127069212040846937875)
      ·
        refine ⟨7953190603818061270406813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5302127069212040846937875 7953190603818061270406813)
        ·
          refine ⟨2982446476431772976402555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7953190603818061270406813 2982446476431772976402555)
          ·
            refine ⟨4473669714647659464603833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2982446476431772976402555 4473669714647659464603833)
            ·
              refine ⟨3355252285985744598452875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4473669714647659464603833 3355252285985744598452875)
              ·
                refine ⟨5032878428978616897679313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3355252285985744598452875 5032878428978616897679313)
                ·
                  refine ⟨3774658821733962673259485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5032878428978616897679313 3774658821733962673259485)
                  ·
                    refine ⟨1415497058150236002472307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3774658821733962673259485 1415497058150236002472307)
                    ·
                      rfl

theorem cell22_4135006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_4135006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135006 prefixEnd_4135006 := by exact prefixLift 4135006
  have htrace : WordTrace (prefixWord ++ tailWord_4135006) baseStart_4135006 baseEnd_4135006 := by
    simpa [prefixWord, tailWord_4135006, baseEnd_4135006] using wordTrace_append hprefix tailTrace_4135006
  have hstable : (prefixWord ++ tailWord_4135006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135006).length < 2 ^ (prefixWord ++ tailWord_4135006).sum := by decide
  have hdescent : baseEnd_4135006 < baseStart_4135006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135009 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 3, 4]
def baseStart_4135009 : Nat := 118140960795 + 4135009 * 2 ^ 59
def prefixEnd_4135009 : Nat := 4983230072969 + 3 ^ 40 * 4135009 * 2
def baseEnd_4135009 : Nat := 1415498085111544994647297

theorem tailTrace_4135009 : CollatzResearch.WordTrace tailWord_4135009 prefixEnd_4135009 1415498085111544994647297 := by
  unfold tailWord_4135009
  simp only [CollatzResearch.WordTrace]
  refine ⟨150816168276576071158592081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100544112184384047439061387 150816168276576071158592081)
  ·
    refine ⟨113112126207432053368944061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150816168276576071158592081 113112126207432053368944061)
    ·
      refine ⟨42417047327787020013354023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113112126207432053368944061 42417047327787020013354023)
      ·
        refine ⟨63625570991680530020031035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42417047327787020013354023 63625570991680530020031035)
        ·
          refine ⟨95438356487520795030046553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63625570991680530020031035 95438356487520795030046553)
          ·
            refine ⟨71578767365640596272534915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95438356487520795030046553 71578767365640596272534915)
            ·
              refine ⟨107368151048460894408802373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71578767365640596272534915 107368151048460894408802373)
              ·
                refine ⟨20131528321586417701650445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107368151048460894408802373 20131528321586417701650445)
                ·
                  refine ⟨7549323120594906638118917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20131528321586417701650445 7549323120594906638118917)
                  ·
                    refine ⟨1415498085111544994647297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7549323120594906638118917 1415498085111544994647297)
                    ·
                      rfl

theorem cell22_4135009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_4135009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135009 prefixEnd_4135009 := by exact prefixLift 4135009
  have htrace : WordTrace (prefixWord ++ tailWord_4135009) baseStart_4135009 baseEnd_4135009 := by
    simpa [prefixWord, tailWord_4135009, baseEnd_4135009] using wordTrace_append hprefix tailTrace_4135009
  have hstable : (prefixWord ++ tailWord_4135009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135009).length < 2 ^ (prefixWord ++ tailWord_4135009).sum := by decide
  have hdescent : baseEnd_4135009 < baseStart_4135009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135013 : List Nat := [1, 3, 1, 3, 2, 4, 2, 1, 5]
def baseStart_4135013 : Nat := 118140960795 + 4135013 * 2 ^ 59
def prefixEnd_4135013 : Nat := 4983230072969 + 3 ^ 40 * 4135013 * 2
def baseEnd_4135013 : Nat := 471833151464430105849095

theorem tailTrace_4135013 : CollatzResearch.WordTrace tailWord_4135013 prefixEnd_4135013 471833151464430105849095 := by
  unfold tailWord_4135013
  simp only [CollatzResearch.WordTrace]
  refine ⟨150816314168561579841737693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100544209445707719894491795 150816314168561579841737693)
  ·
    refine ⟨56556117813210592440651635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150816314168561579841737693 56556117813210592440651635)
    ·
      refine ⟨84834176719815888660977453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56556117813210592440651635 84834176719815888660977453)
      ·
        refine ⟨31812816269930958247866545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84834176719815888660977453 31812816269930958247866545)
        ·
          refine ⟨23859612202448218685899909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31812816269930958247866545 23859612202448218685899909)
          ·
            refine ⟨4473677287959041003606233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23859612202448218685899909 4473677287959041003606233)
            ·
              refine ⟨3355257965969280752704675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4473677287959041003606233 3355257965969280752704675)
              ·
                refine ⟨5032886948953921129057013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3355257965969280752704675 5032886948953921129057013)
                ·
                  refine ⟨471833151464430105849095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5032886948953921129057013 471833151464430105849095)
                  ·
                    rfl

theorem cell22_4135013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_4135013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135013 prefixEnd_4135013 := by exact prefixLift 4135013
  have htrace : WordTrace (prefixWord ++ tailWord_4135013) baseStart_4135013 baseEnd_4135013 := by
    simpa [prefixWord, tailWord_4135013, baseEnd_4135013] using wordTrace_append hprefix tailTrace_4135013
  have hstable : (prefixWord ++ tailWord_4135013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135013).length < 2 ^ (prefixWord ++ tailWord_4135013).sum := by decide
  have hdescent : baseEnd_4135013 < baseStart_4135013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135026 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_4135026 : Nat := 118140960795 + 4135026 * 2 ^ 59
def prefixEnd_4135026 : Nat := 4983230072969 + 3 ^ 40 * 4135026 * 2
def baseEnd_4135026 : Nat := 1415503904558962616972245

theorem tailTrace_4135026 : CollatzResearch.WordTrace tailWord_4135026 prefixEnd_4135026 1415503904558962616972245 := by
  unfold tailWord_4135026
  simp only [CollatzResearch.WordTrace]
  refine ⟨37704197079378620765490233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100544525545009655374640621 37704197079378620765490233)
  ·
    refine ⟨28278147809533965574117675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37704197079378620765490233 28278147809533965574117675)
    ·
      refine ⟨42417221714300948361176513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28278147809533965574117675 42417221714300948361176513)
      ·
        refine ⟨31812916285725711270882385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42417221714300948361176513 31812916285725711270882385)
        ·
          refine ⟨23859687214294283453161789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31812916285725711270882385 23859687214294283453161789)
          ·
            refine ⟨8947382705360356294935671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23859687214294283453161789 8947382705360356294935671)
            ·
              refine ⟨13421074058040534442403507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8947382705360356294935671 13421074058040534442403507)
              ·
                refine ⟨20131611087060801663605261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13421074058040534442403507 20131611087060801663605261)
                ·
                  refine ⟨7549354157647800623851973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20131611087060801663605261 7549354157647800623851973)
                  ·
                    refine ⟨1415503904558962616972245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7549354157647800623851973 1415503904558962616972245)
                    ·
                      rfl

theorem cell22_4135026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_4135026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135026 prefixEnd_4135026 := by exact prefixLift 4135026
  have htrace : WordTrace (prefixWord ++ tailWord_4135026) baseStart_4135026 baseEnd_4135026 := by
    simpa [prefixWord, tailWord_4135026, baseEnd_4135026] using wordTrace_append hprefix tailTrace_4135026
  have hstable : (prefixWord ++ tailWord_4135026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135026).length < 2 ^ (prefixWord ++ tailWord_4135026).sum := by decide
  have hdescent : baseEnd_4135026 < baseStart_4135026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135043 : List Nat := [1, 1, 1, 3, 3, 4, 3, 1, 1, 4]
def baseStart_4135043 : Nat := 118140960795 + 4135043 * 2 ^ 59
def prefixEnd_4135043 : Nat := 4983230072969 + 3 ^ 40 * 4135043 * 2
def baseEnd_4135043 : Nat := 1415509724006380239297193

theorem tailTrace_4135043 : CollatzResearch.WordTrace tailWord_4135043 prefixEnd_4135043 1415509724006380239297193 := by
  unfold tailWord_4135043
  simp only [CollatzResearch.WordTrace]
  refine ⟨150817408358452894965329783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100544938905635263310219855 150817408358452894965329783)
  ·
    refine ⟨226226112537679342447994675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150817408358452894965329783 226226112537679342447994675)
    ·
      refine ⟨339339168806519013671992013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226226112537679342447994675 339339168806519013671992013)
      ·
        refine ⟨127252188302444630126997005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339339168806519013671992013 127252188302444630126997005)
        ·
          refine ⟨47719570613416736297623877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127252188302444630126997005 47719570613416736297623877)
          ·
            refine ⟨8947419490015638055804477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47719570613416736297623877 8947419490015638055804477)
            ·
              refine ⟨3355282308755864270926679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8947419490015638055804477 3355282308755864270926679)
              ·
                refine ⟨5032923463133796406390019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3355282308755864270926679 5032923463133796406390019)
                ·
                  refine ⟨7549385194700694609585029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5032923463133796406390019 7549385194700694609585029)
                  ·
                    refine ⟨1415509724006380239297193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7549385194700694609585029 1415509724006380239297193)
                    ·
                      rfl

theorem cell22_4135043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 1, 4].length) (baseStart_4135043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135043 prefixEnd_4135043 := by exact prefixLift 4135043
  have htrace : WordTrace (prefixWord ++ tailWord_4135043) baseStart_4135043 baseEnd_4135043 := by
    simpa [prefixWord, tailWord_4135043, baseEnd_4135043] using wordTrace_append hprefix tailTrace_4135043
  have hstable : (prefixWord ++ tailWord_4135043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135043).length < 2 ^ (prefixWord ++ tailWord_4135043).sum := by decide
  have hdescent : baseEnd_4135043 < baseStart_4135043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135058 : List Nat := [3, 2, 3, 1, 1, 1, 3, 4, 4]
def baseStart_4135058 : Nat := 118140960795 + 4135058 * 2 ^ 59
def prefixEnd_4135058 : Nat := 4983230072969 + 3 ^ 40 * 4135058 * 2
def baseEnd_4135058 : Nat := 471838286270975066724049

theorem tailTrace_4135058 : CollatzResearch.WordTrace tailWord_4135058 prefixEnd_4135058 471838286270975066724049 := by
  unfold tailWord_4135058
  simp only [CollatzResearch.WordTrace]
  refine ⟨37704488863349638131781457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100545303635599035018083885 37704488863349638131781457)
  ·
    refine ⟨28278366647512228598836093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37704488863349638131781457 28278366647512228598836093)
    ·
      refine ⟨10604387492817085724563535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28278366647512228598836093 10604387492817085724563535)
      ·
        refine ⟨15906581239225628586845303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10604387492817085724563535 15906581239225628586845303)
        ·
          refine ⟨23859871858838442880267955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15906581239225628586845303 23859871858838442880267955)
          ·
            refine ⟨35789807788257664320401933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23859871858838442880267955 35789807788257664320401933)
            ·
              refine ⟨13421177920596624120150725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35789807788257664320401933 13421177920596624120150725)
              ·
                refine ⟨2516470860111867022528261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13421177920596624120150725 2516470860111867022528261)
                ·
                  refine ⟨471838286270975066724049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2516470860111867022528261 471838286270975066724049)
                  ·
                    rfl

theorem cell22_4135058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_4135058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135058 prefixEnd_4135058 := by exact prefixLift 4135058
  have htrace : WordTrace (prefixWord ++ tailWord_4135058) baseStart_4135058 baseEnd_4135058 := by
    simpa [prefixWord, tailWord_4135058, baseEnd_4135058] using wordTrace_append hprefix tailTrace_4135058
  have hstable : (prefixWord ++ tailWord_4135058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135058).length < 2 ^ (prefixWord ++ tailWord_4135058).sum := by decide
  have hdescent : baseEnd_4135058 < baseStart_4135058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135073 : List Nat := [1, 2, 3, 3, 1, 2, 2, 3, 2, 3]
def baseStart_4135073 : Nat := 118140960795 + 4135073 * 2 ^ 59
def prefixEnd_4135073 : Nat := 4983230072969 + 3 ^ 40 * 4135073 * 2
def baseEnd_4135073 : Nat := 1415519993619470161047101

theorem tailTrace_4135073 : CollatzResearch.WordTrace tailWord_4135073 prefixEnd_4135073 1415519993619470161047101 := by
  unfold tailWord_4135073
  simp only [CollatzResearch.WordTrace]
  refine ⟨150818502548344210088921873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100545668365562806725947915 150818502548344210088921873)
  ·
    refine ⟨113113876911258157566691405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150818502548344210088921873 113113876911258157566691405)
    ·
      refine ⟨42417703841721809087509277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113113876911258157566691405 42417703841721809087509277)
      ·
        refine ⟨15906638940645678407815979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42417703841721809087509277 15906638940645678407815979)
        ·
          refine ⟨23859958410968517611723969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15906638940645678407815979 23859958410968517611723969)
          ·
            refine ⟨17894968808226388208792977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23859958410968517611723969 17894968808226388208792977)
            ·
              refine ⟨13421226606169791156594733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17894968808226388208792977 13421226606169791156594733)
              ·
                refine ⟨5032959977313671683723025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13421226606169791156594733 5032959977313671683723025)
                ·
                  refine ⟨3774719982985253762792269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5032959977313671683723025 3774719982985253762792269)
                  ·
                    refine ⟨1415519993619470161047101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3774719982985253762792269 1415519993619470161047101)
                    ·
                      rfl

theorem cell22_4135073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_4135073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135073 prefixEnd_4135073 := by exact prefixLift 4135073
  have htrace : WordTrace (prefixWord ++ tailWord_4135073) baseStart_4135073 baseEnd_4135073 := by
    simpa [prefixWord, tailWord_4135073, baseEnd_4135073] using wordTrace_append hprefix tailTrace_4135073
  have hstable : (prefixWord ++ tailWord_4135073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135073).length < 2 ^ (prefixWord ++ tailWord_4135073).sum := by decide
  have hdescent : baseEnd_4135073 < baseStart_4135073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135101 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 7, 3]
def baseStart_4135101 : Nat := 118140960795 + 4135101 * 2 ^ 59
def prefixEnd_4135101 : Nat := 4983230072969 + 3 ^ 40 * 4135101 * 2
def baseEnd_4135101 : Nat := 1415529578591687421347015

theorem tailTrace_4135101 : CollatzResearch.WordTrace tailWord_4135101 prefixEnd_4135101 1415529578591687421347015 := by
  unfold tailWord_4135101
  simp only [CollatzResearch.WordTrace]
  refine ⟨150819523792242770870941157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100546349194828513913960771 150819523792242770870941157)
  ·
    refine ⟨28278660711045519538301467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150819523792242770870941157 28278660711045519538301467)
    ·
      refine ⟨42417991066568279307452201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28278660711045519538301467 42417991066568279307452201)
      ·
        refine ⟨31813493299926209480589151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42417991066568279307452201 31813493299926209480589151)
        ·
          refine ⟨47720239949889314220883727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31813493299926209480589151 47720239949889314220883727)
          ·
            refine ⟨71580359924833971331325591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47720239949889314220883727 71580359924833971331325591)
            ·
              refine ⟨107370539887250956996988387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71580359924833971331325591 107370539887250956996988387)
              ·
                refine ⟨161055809830876435495482581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107370539887250956996988387 161055809830876435495482581)
                ·
                  refine ⟨3774745542911166456925373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 161055809830876435495482581 3774745542911166456925373)
                  ·
                    refine ⟨1415529578591687421347015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3774745542911166456925373 1415529578591687421347015)
                    ·
                      rfl

theorem cell22_4135101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_4135101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135101 prefixEnd_4135101 := by exact prefixLift 4135101
  have htrace : WordTrace (prefixWord ++ tailWord_4135101) baseStart_4135101 baseEnd_4135101 := by
    simpa [prefixWord, tailWord_4135101, baseEnd_4135101] using wordTrace_append hprefix tailTrace_4135101
  have hstable : (prefixWord ++ tailWord_4135101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135101).length < 2 ^ (prefixWord ++ tailWord_4135101).sum := by decide
  have hdescent : baseEnd_4135101 < baseStart_4135101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135118 : List Nat := [4, 1, 1, 1, 4, 1, 1, 3, 3, 3]
def baseStart_4135118 : Nat := 118140960795 + 4135118 * 2 ^ 59
def prefixEnd_4135118 : Nat := 4983230072969 + 3 ^ 40 * 4135118 * 2
def baseEnd_4135118 : Nat := 1415535398039105043671963

theorem tailTrace_4135118 : CollatzResearch.WordTrace tailWord_4135118 prefixEnd_4135118 1415535398039105043671963 := by
  unfold tailWord_4135118
  simp only [CollatzResearch.WordTrace]
  refine ⟨18852517979147647846788751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100546762555454121849540005 18852517979147647846788751)
  ·
    refine ⟨28278776968721471770183127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18852517979147647846788751 28278776968721471770183127)
    ·
      refine ⟨42418165453082207655274691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28278776968721471770183127 42418165453082207655274691)
      ·
        refine ⟨63627248179623311482912037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42418165453082207655274691 63627248179623311482912037)
        ·
          refine ⟨11930109033679370903046007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63627248179623311482912037 11930109033679370903046007)
          ·
            refine ⟨17895163550519056354569011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11930109033679370903046007 17895163550519056354569011)
            ·
              refine ⟨26842745325778584531853517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17895163550519056354569011 26842745325778584531853517)
              ·
                refine ⟨10066029497166969199445069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26842745325778584531853517 10066029497166969199445069)
                ·
                  refine ⟨3774761061437613449791901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10066029497166969199445069 3774761061437613449791901)
                  ·
                    refine ⟨1415535398039105043671963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3774761061437613449791901 1415535398039105043671963)
                    ·
                      rfl

theorem cell22_4135118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_4135118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135118 prefixEnd_4135118 := by exact prefixLift 4135118
  have htrace : WordTrace (prefixWord ++ tailWord_4135118) baseStart_4135118 baseEnd_4135118 := by
    simpa [prefixWord, tailWord_4135118, baseEnd_4135118] using wordTrace_append hprefix tailTrace_4135118
  have hstable : (prefixWord ++ tailWord_4135118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135118).length < 2 ^ (prefixWord ++ tailWord_4135118).sum := by decide
  have hdescent : baseEnd_4135118 < baseStart_4135118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135225 : List Nat := [1, 2, 1, 6, 1, 1, 1, 4, 2, 3]
def baseStart_4135225 : Nat := 118140960795 + 4135225 * 2 ^ 59
def prefixEnd_4135225 : Nat := 4983230072969 + 3 ^ 40 * 4135225 * 2
def baseEnd_4135225 : Nat := 1415572026325792431246635

theorem tailTrace_4135225 : CollatzResearch.WordTrace tailWord_4135225 prefixEnd_4135225 1415572026325792431246635 := by
  unfold tailWord_4135225
  simp only [CollatzResearch.WordTrace]
  refine ⟨150824046443793540048455129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100549364295862360032303419 150824046443793540048455129)
  ·
    refine ⟨113118034832845155036341347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150824046443793540048455129 113118034832845155036341347)
    ·
      refine ⟨169677052249267732554512021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113118034832845155036341347 169677052249267732554512021)
      ·
        refine ⟨7953611824184424963492751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 169677052249267732554512021 7953611824184424963492751)
        ·
          refine ⟨11930417736276637445239127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7953611824184424963492751 11930417736276637445239127)
          ·
            refine ⟨17895626604414956167858691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11930417736276637445239127 17895626604414956167858691)
            ·
              refine ⟨26843439906622434251788037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17895626604414956167858691 26843439906622434251788037)
              ·
                refine ⟨5033144982491706422210257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26843439906622434251788037 5033144982491706422210257)
                ·
                  refine ⟨3774858736868779816657693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5033144982491706422210257 3774858736868779816657693)
                  ·
                    refine ⟨1415572026325792431246635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3774858736868779816657693 1415572026325792431246635)
                    ·
                      rfl

theorem cell22_4135225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 3].length) (baseStart_4135225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135225 prefixEnd_4135225 := by exact prefixLift 4135225
  have htrace : WordTrace (prefixWord ++ tailWord_4135225) baseStart_4135225 baseEnd_4135225 := by
    simpa [prefixWord, tailWord_4135225, baseEnd_4135225] using wordTrace_append hprefix tailTrace_4135225
  have hstable : (prefixWord ++ tailWord_4135225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135225).length < 2 ^ (prefixWord ++ tailWord_4135225).sum := by decide
  have hdescent : baseEnd_4135225 < baseStart_4135225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135300 : List Nat := [2, 3, 2, 1, 1, 2, 5, 1, 5]
def baseStart_4135300 : Nat := 118140960795 + 4135300 * 2 ^ 59
def prefixEnd_4135300 : Nat := 4983230072969 + 3 ^ 40 * 4135300 * 2
def baseEnd_4135300 : Nat := 471865900119505745207135

theorem tailTrace_4135300 : CollatzResearch.WordTrace tailWord_4135300 prefixEnd_4135300 471865900119505745207135 := by
  unfold tailWord_4135300
  simp only [CollatzResearch.WordTrace]
  refine ⟨75413390959260913928717677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100551187945681218571623569 75413390959260913928717677)
  ·
    refine ⟨28280021609722842723269129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75413390959260913928717677 28280021609722842723269129)
    ·
      refine ⟨21210016207292132042451847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28280021609722842723269129 21210016207292132042451847)
      ·
        refine ⟨31815024310938198063677771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21210016207292132042451847 31815024310938198063677771)
        ·
          refine ⟨47722536466407297095516657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31815024310938198063677771 47722536466407297095516657)
          ·
            refine ⟨35791902349805472821637493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47722536466407297095516657 35791902349805472821637493)
            ·
              refine ⟨3355490845294263077028515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35791902349805472821637493 3355490845294263077028515)
              ·
                refine ⟨5033236267941394615542773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3355490845294263077028515 5033236267941394615542773)
                ·
                  refine ⟨471865900119505745207135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5033236267941394615542773 471865900119505745207135)
                  ·
                    rfl

theorem cell22_4135300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_4135300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135300 prefixEnd_4135300 := by exact prefixLift 4135300
  have htrace : WordTrace (prefixWord ++ tailWord_4135300) baseStart_4135300 baseEnd_4135300 := by
    simpa [prefixWord, tailWord_4135300, baseEnd_4135300] using wordTrace_append hprefix tailTrace_4135300
  have hstable : (prefixWord ++ tailWord_4135300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135300).length < 2 ^ (prefixWord ++ tailWord_4135300).sum := by decide
  have hdescent : baseEnd_4135300 < baseStart_4135300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135330 : List Nat := [3, 3, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_4135330 : Nat := 118140960795 + 4135330 * 2 ^ 59
def prefixEnd_4135330 : Nat := 4983230072969 + 3 ^ 40 * 4135330 * 2
def baseEnd_4135330 : Nat := 1415607969971607157371313

theorem tailTrace_4135330 : CollatzResearch.WordTrace tailWord_4135330 prefixEnd_4135330 1415607969971607157371313 := by
  unfold tailWord_4135330
  simp only [CollatzResearch.WordTrace]
  refine ⟨37706969027103285745256861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100551917405608761987351629 37706969027103285745256861)
  ·
    refine ⟨14140113385163732154471323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37706969027103285745256861 14140113385163732154471323)
    ·
      refine ⟨21210170077745598231706985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14140113385163732154471323 21210170077745598231706985)
      ·
        refine ⟨15907627558309198673780239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21210170077745598231706985 15907627558309198673780239)
        ·
          refine ⟨23861441337463798010670359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15907627558309198673780239 23861441337463798010670359)
          ·
            refine ⟨35792162006195697016005539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23861441337463798010670359 35792162006195697016005539)
            ·
              refine ⟨53688243009293545524008309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35792162006195697016005539 53688243009293545524008309)
              ·
                refine ⟨5033272782121269892875779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53688243009293545524008309 5033272782121269892875779)
                ·
                  refine ⟨7549909173181904839313669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5033272782121269892875779 7549909173181904839313669)
                  ·
                    refine ⟨1415607969971607157371313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7549909173181904839313669 1415607969971607157371313)
                    ·
                      rfl

theorem cell22_4135330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_4135330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135330 prefixEnd_4135330 := by exact prefixLift 4135330
  have htrace : WordTrace (prefixWord ++ tailWord_4135330) baseStart_4135330 baseEnd_4135330 := by
    simpa [prefixWord, tailWord_4135330, baseEnd_4135330] using wordTrace_append hprefix tailTrace_4135330
  have hstable : (prefixWord ++ tailWord_4135330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135330).length < 2 ^ (prefixWord ++ tailWord_4135330).sum := by decide
  have hdescent : baseEnd_4135330 < baseStart_4135330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135338 : List Nat := [3, 1, 6, 1, 2, 1, 1, 1, 3, 3]
def baseStart_4135338 : Nat := 118140960795 + 4135338 * 2 ^ 59
def prefixEnd_4135338 : Nat := 4983230072969 + 3 ^ 40 * 4135338 * 2
def baseEnd_4135338 : Nat := 1415610708535097803171289

theorem tailTrace_4135338 : CollatzResearch.WordTrace tailWord_4135338 prefixEnd_4135338 1415610708535097803171289 := by
  unfold tailWord_4135338
  simp only [CollatzResearch.WordTrace]
  refine ⟨37707041973096040086829667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100552111928256106898212445 37707041973096040086829667)
  ·
    refine ⟨56560562959644060130244501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37707041973096040086829667 56560562959644060130244501)
    ·
      refine ⟨2651276388733315318605211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56560562959644060130244501 2651276388733315318605211)
      ·
        refine ⟨3976914583099972977907817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2651276388733315318605211 3976914583099972977907817)
        ·
          refine ⟨2982685937324979733430863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3976914583099972977907817 2982685937324979733430863)
          ·
            refine ⟨4474028905987469600146295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2982685937324979733430863 4474028905987469600146295)
            ·
              refine ⟨6711043358981204400219443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4474028905987469600146295 6711043358981204400219443)
              ·
                refine ⟨10066565038471806600329165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6711043358981204400219443 10066565038471806600329165)
                ·
                  refine ⟨3774961889426927475123437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10066565038471806600329165 3774961889426927475123437)
                  ·
                    refine ⟨1415610708535097803171289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3774961889426927475123437 1415610708535097803171289)
                    ·
                      rfl

theorem cell22_4135338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_4135338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135338 prefixEnd_4135338 := by exact prefixLift 4135338
  have htrace : WordTrace (prefixWord ++ tailWord_4135338) baseStart_4135338 baseEnd_4135338 := by
    simpa [prefixWord, tailWord_4135338, baseEnd_4135338] using wordTrace_append hprefix tailTrace_4135338
  have hstable : (prefixWord ++ tailWord_4135338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135338).length < 2 ^ (prefixWord ++ tailWord_4135338).sum := by decide
  have hdescent : baseEnd_4135338 < baseStart_4135338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135345 : List Nat := [1, 2, 2, 4, 1, 4, 1, 1, 6]
def baseStart_4135345 : Nat := 118140960795 + 4135345 * 2 ^ 59
def prefixEnd_4135345 : Nat := 4983230072969 + 3 ^ 40 * 4135345 * 2
def baseEnd_4135345 : Nat := 471871034926050706082089

theorem tailTrace_4135345 : CollatzResearch.WordTrace tailWord_4135345 prefixEnd_4135345 471871034926050706082089 := by
  unfold tailWord_4135345
  simp only [CollatzResearch.WordTrace]
  refine ⟨150828423203358800542823489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100552282135572533695215659 150828423203358800542823489)
  ·
    refine ⟨113121317402519100407117617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150828423203358800542823489 113121317402519100407117617)
    ·
      refine ⟨84840988051889325305338213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113121317402519100407117617 84840988051889325305338213)
      ·
        refine ⟨15907685259729248494750915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84840988051889325305338213 15907685259729248494750915)
        ·
          refine ⟨23861527889593872742126373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15907685259729248494750915 23861527889593872742126373)
          ·
            refine ⟨4474036479298851139148695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23861527889593872742126373 4474036479298851139148695)
            ·
              refine ⟨6711054718948276708723043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4474036479298851139148695 6711054718948276708723043)
              ·
                refine ⟨10066582078422415063084565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6711054718948276708723043 10066582078422415063084565)
                ·
                  refine ⟨471871034926050706082089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10066582078422415063084565 471871034926050706082089)
                  ·
                    rfl

theorem cell22_4135345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 6].length) (baseStart_4135345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135345 prefixEnd_4135345 := by exact prefixLift 4135345
  have htrace : WordTrace (prefixWord ++ tailWord_4135345) baseStart_4135345 baseEnd_4135345 := by
    simpa [prefixWord, tailWord_4135345, baseEnd_4135345] using wordTrace_append hprefix tailTrace_4135345
  have hstable : (prefixWord ++ tailWord_4135345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135345).length < 2 ^ (prefixWord ++ tailWord_4135345).sum := by decide
  have hdescent : baseEnd_4135345 < baseStart_4135345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135358 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_4135358 : Nat := 118140960795 + 4135358 * 2 ^ 59
def prefixEnd_4135358 : Nat := 4983230072969 + 3 ^ 40 * 4135358 * 2
def baseEnd_4135358 : Nat := 1415617554943824417671227

theorem tailTrace_4135358 : CollatzResearch.WordTrace tailWord_4135358 prefixEnd_4135358 1415617554943824417671227 := by
  unfold tailWord_4135358
  simp only [CollatzResearch.WordTrace]
  refine ⟨18853612169038962970380841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100552598234874469175364485 18853612169038962970380841)
  ·
    refine ⟨14140209126779222227785631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18853612169038962970380841 14140209126779222227785631)
    ·
      refine ⟨21210313690168833341678447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14140209126779222227785631 21210313690168833341678447)
      ·
        refine ⟨31815470535253250012517671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21210313690168833341678447 31815470535253250012517671)
        ·
          refine ⟨47723205802879875018776507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31815470535253250012517671 47723205802879875018776507)
          ·
            refine ⟨71584808704319812528164761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47723205802879875018776507 71584808704319812528164761)
            ·
              refine ⟨53688606528239859396123571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71584808704319812528164761 53688606528239859396123571)
              ·
                refine ⟨80532909792359789094185357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53688606528239859396123571 80532909792359789094185357)
                ·
                  refine ⟨30199841172134920910319509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80532909792359789094185357 30199841172134920910319509)
                  ·
                    refine ⟨1415617554943824417671227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30199841172134920910319509 1415617554943824417671227)
                    ·
                      rfl

theorem cell22_4135358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_4135358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135358 prefixEnd_4135358 := by exact prefixLift 4135358
  have htrace : WordTrace (prefixWord ++ tailWord_4135358) baseStart_4135358 baseEnd_4135358 := by
    simpa [prefixWord, tailWord_4135358, baseEnd_4135358] using wordTrace_append hprefix tailTrace_4135358
  have hstable : (prefixWord ++ tailWord_4135358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135358).length < 2 ^ (prefixWord ++ tailWord_4135358).sum := by decide
  have hdescent : baseEnd_4135358 < baseStart_4135358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135364 : List Nat := [2, 3, 3, 2, 2, 2, 1, 2, 1, 4]
def baseStart_4135364 : Nat := 118140960795 + 4135364 * 2 ^ 59
def prefixEnd_4135364 : Nat := 4983230072969 + 3 ^ 40 * 4135364 * 2
def baseEnd_4135364 : Nat := 1415619608866442402021209

theorem tailTrace_4135364 : CollatzResearch.WordTrace tailWord_4135364 prefixEnd_4135364 1415619608866442402021209 := by
  unfold tailWord_4135364
  simp only [CollatzResearch.WordTrace]
  refine ⟨75414558095144983393882573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100552744126859977858510097 75414558095144983393882573)
  ·
    refine ⟨28280459285679368772705965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75414558095144983393882573 28280459285679368772705965)
    ·
      refine ⟨10605172232129763289764737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28280459285679368772705965 10605172232129763289764737)
      ·
        refine ⟨7953879174097322467323553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10605172232129763289764737 7953879174097322467323553)
        ·
          refine ⟨5965409380572991850492665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7953879174097322467323553 5965409380572991850492665)
          ·
            refine ⟨4474057035429743887869499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5965409380572991850492665 4474057035429743887869499)
            ·
              refine ⟨6711085553144615831804249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4474057035429743887869499 6711085553144615831804249)
              ·
                refine ⟨5033314164858461873853187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6711085553144615831804249 5033314164858461873853187)
                ·
                  refine ⟨7549971247287692810779781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5033314164858461873853187 7549971247287692810779781)
                  ·
                    refine ⟨1415619608866442402021209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7549971247287692810779781 1415619608866442402021209)
                    ·
                      rfl

theorem cell22_4135364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_4135364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135364 prefixEnd_4135364 := by exact prefixLift 4135364
  have htrace : WordTrace (prefixWord ++ tailWord_4135364) baseStart_4135364 baseEnd_4135364 := by
    simpa [prefixWord, tailWord_4135364, baseEnd_4135364] using wordTrace_append hprefix tailTrace_4135364
  have hstable : (prefixWord ++ tailWord_4135364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135364).length < 2 ^ (prefixWord ++ tailWord_4135364).sum := by decide
  have hdescent : baseEnd_4135364 < baseStart_4135364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135426 : List Nat := [3, 4, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_4135426 : Nat := 118140960795 + 4135426 * 2 ^ 59
def prefixEnd_4135426 : Nat := 4983230072969 + 3 ^ 40 * 4135426 * 2
def baseEnd_4135426 : Nat := 1415640832733494906971019

theorem tailTrace_4135426 : CollatzResearch.WordTrace tailWord_4135426 prefixEnd_4135426 1415640832733494906971019 := by
  unfold tailWord_4135426
  simp only [CollatzResearch.WordTrace]
  refine ⟨37707844379016337844130533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100554251677376900917681421 37707844379016337844130533)
  ·
    refine ⟨7070220821065563345774475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37707844379016337844130533 7070220821065563345774475)
    ·
      refine ⟨10605331231598345018661713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7070220821065563345774475 10605331231598345018661713)
      ·
        refine ⟨7953998423698758763996285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10605331231598345018661713 7953998423698758763996285)
        ·
          refine ⟨2982749408887034536498607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7953998423698758763996285 2982749408887034536498607)
          ·
            refine ⟨4474124113330551804747911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2982749408887034536498607 4474124113330551804747911)
            ·
              refine ⟨6711186169995827707121867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4474124113330551804747911 6711186169995827707121867)
              ·
                refine ⟨10066779254993741560682801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6711186169995827707121867 10066779254993741560682801)
                ·
                  refine ⟨7550084441245306170512101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10066779254993741560682801 7550084441245306170512101)
                  ·
                    refine ⟨1415640832733494906971019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7550084441245306170512101 1415640832733494906971019)
                    ·
                      rfl

theorem cell22_4135426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_4135426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135426 prefixEnd_4135426 := by exact prefixLift 4135426
  have htrace : WordTrace (prefixWord ++ tailWord_4135426) baseStart_4135426 baseEnd_4135426 := by
    simpa [prefixWord, tailWord_4135426, baseEnd_4135426] using wordTrace_append hprefix tailTrace_4135426
  have hstable : (prefixWord ++ tailWord_4135426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135426).length < 2 ^ (prefixWord ++ tailWord_4135426).sum := by decide
  have hdescent : baseEnd_4135426 < baseStart_4135426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135452 : List Nat := [2, 2, 3, 1, 2, 4, 1, 2, 5]
def baseStart_4135452 : Nat := 118140960795 + 4135452 * 2 ^ 59
def prefixEnd_4135452 : Nat := 4983230072969 + 3 ^ 40 * 4135452 * 2
def baseEnd_4135452 : Nat := 471883244354946501940313

theorem tailTrace_4135452 : CollatzResearch.WordTrace tailWord_4135452 prefixEnd_4135452 471883244354946501940313 := by
  unfold tailWord_4135452
  simp only [CollatzResearch.WordTrace]
  refine ⟨75416162906985578908484305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100554883875980771877979073 75416162906985578908484305)
  ·
    refine ⟨56562122180239184181363229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75416162906985578908484305 56562122180239184181363229)
    ·
      refine ⟨21210795817589694068011211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56562122180239184181363229 21210795817589694068011211)
      ·
        refine ⟨31816193726384541102016817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21210795817589694068011211 31816193726384541102016817)
        ·
          refine ⟨23862145294788405826512613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31816193726384541102016817 23862145294788405826512613)
          ·
            refine ⟨4474152242772826092471115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23862145294788405826512613 4474152242772826092471115)
            ·
              refine ⟨6711228364159239138706673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4474152242772826092471115 6711228364159239138706673)
              ·
                refine ⟨5033421273119429354030005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6711228364159239138706673 5033421273119429354030005)
                ·
                  refine ⟨471883244354946501940313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5033421273119429354030005 471883244354946501940313)
                  ·
                    rfl

theorem cell22_4135452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_4135452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135452 prefixEnd_4135452 := by exact prefixLift 4135452
  have htrace : WordTrace (prefixWord ++ tailWord_4135452) baseStart_4135452 baseEnd_4135452 := by
    simpa [prefixWord, tailWord_4135452, baseEnd_4135452] using wordTrace_append hprefix tailTrace_4135452
  have hstable : (prefixWord ++ tailWord_4135452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135452).length < 2 ^ (prefixWord ++ tailWord_4135452).sum := by decide
  have hdescent : baseEnd_4135452 < baseStart_4135452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135482 : List Nat := [3, 1, 1, 1, 3, 4, 2, 2, 1, 4]
def baseStart_4135482 : Nat := 118140960795 + 4135482 * 2 ^ 59
def prefixEnd_4135482 : Nat := 4983230072969 + 3 ^ 40 * 4135482 * 2
def baseEnd_4135482 : Nat := 1415660002677929427570847

theorem tailTrace_4135482 : CollatzResearch.WordTrace tailWord_4135482 prefixEnd_4135482 1415660002677929427570847 := by
  unfold tailWord_4135482
  simp only [CollatzResearch.WordTrace]
  refine ⟨37708355000965618235140175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100555613335908315293707133 37708355000965618235140175)
  ·
    refine ⟨56562532501448427352710263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37708355000965618235140175 56562532501448427352710263)
    ·
      refine ⟨84843798752172641029065395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56562532501448427352710263 84843798752172641029065395)
      ·
        refine ⟨127265698128258961543598093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84843798752172641029065395 127265698128258961543598093)
        ·
          refine ⟨47724636798097110578849285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127265698128258961543598093 47724636798097110578849285)
          ·
            refine ⟨8948369399643208233534241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47724636798097110578849285 8948369399643208233534241)
            ·
              refine ⟨6711277049732406175150681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8948369399643208233534241 6711277049732406175150681)
              ·
                refine ⟨5033457787299304631363011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6711277049732406175150681 5033457787299304631363011)
                ·
                  refine ⟨7550186680948956947044517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5033457787299304631363011 7550186680948956947044517)
                  ·
                    refine ⟨1415660002677929427570847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7550186680948956947044517 1415660002677929427570847)
                    ·
                      rfl

theorem cell22_4135482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_4135482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135482 prefixEnd_4135482 := by exact prefixLift 4135482
  have htrace : WordTrace (prefixWord ++ tailWord_4135482) baseStart_4135482 baseEnd_4135482 := by
    simpa [prefixWord, tailWord_4135482, baseEnd_4135482] using wordTrace_append hprefix tailTrace_4135482
  have hstable : (prefixWord ++ tailWord_4135482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135482).length < 2 ^ (prefixWord ++ tailWord_4135482).sum := by decide
  have hdescent : baseEnd_4135482 < baseStart_4135482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135572 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_4135572 : Nat := 118140960795 + 4135572 * 2 ^ 59
def prefixEnd_4135572 : Nat := 4983230072969 + 3 ^ 40 * 4135572 * 2
def baseEnd_4135572 : Nat := 1415690811517199192820571

theorem tailTrace_4135572 : CollatzResearch.WordTrace tailWord_4135572 prefixEnd_4135572 1415690811517199192820571 := by
  unfold tailWord_4135572
  simp only [CollatzResearch.WordTrace]
  refine ⟨75418351286768209155668485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100557801715690945540891313 75418351286768209155668485)
  ·
    refine ⟨14140940866269039216687841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75418351286768209155668485 14140940866269039216687841)
    ·
      refine ⟨10605705649701779412515881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14140940866269039216687841 10605705649701779412515881)
      ·
        refine ⟨7954279237276334559386911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10605705649701779412515881 7954279237276334559386911)
        ·
          refine ⟨11931418855914501839080367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7954279237276334559386911 11931418855914501839080367)
          ·
            refine ⟨17897128283871752758620551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11931418855914501839080367 17897128283871752758620551)
            ·
              refine ⟨26845692425807629137930827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17897128283871752758620551 26845692425807629137930827)
              ·
                refine ⟨40268538638711443706896241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26845692425807629137930827 40268538638711443706896241)
                ·
                  refine ⟨30201403979033582780172181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40268538638711443706896241 30201403979033582780172181)
                  ·
                    refine ⟨1415690811517199192820571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30201403979033582780172181 1415690811517199192820571)
                    ·
                      rfl

theorem cell22_4135572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_4135572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135572 prefixEnd_4135572 := by exact prefixLift 4135572
  have htrace : WordTrace (prefixWord ++ tailWord_4135572) baseStart_4135572 baseEnd_4135572 := by
    simpa [prefixWord, tailWord_4135572, baseEnd_4135572] using wordTrace_append hprefix tailTrace_4135572
  have hstable : (prefixWord ++ tailWord_4135572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135572).length < 2 ^ (prefixWord ++ tailWord_4135572).sum := by decide
  have hdescent : baseEnd_4135572 < baseStart_4135572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135591 : List Nat := [1, 1, 6, 3, 1, 1, 1, 2, 3, 3]
def baseStart_4135591 : Nat := 118140960795 + 4135591 * 2 ^ 59
def prefixEnd_4135591 : Nat := 4983230072969 + 3 ^ 40 * 4135591 * 2
def baseEnd_4135591 : Nat := 1415697315605489476595513

theorem tailTrace_4135591 : CollatzResearch.WordTrace tailWord_4135591 prefixEnd_4135591 1415697315605489476595513 := by
  unfold tailWord_4135591
  simp only [CollatzResearch.WordTrace]
  refine ⟨150837395560467584556278627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100558263706978389704185751 150837395560467584556278627)
  ·
    refine ⟨226256093340701376834417941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150837395560467584556278627 226256093340701376834417941)
    ·
      refine ⟨10605754375345377039113341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 226256093340701376834417941 10605754375345377039113341)
      ·
        refine ⟨3977157890754516389667503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10605754375345377039113341 3977157890754516389667503)
        ·
          refine ⟨5965736836131774584501255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3977157890754516389667503 5965736836131774584501255)
          ·
            refine ⟨8948605254197661876751883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5965736836131774584501255 8948605254197661876751883)
            ·
              refine ⟨13422907881296492815127825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8948605254197661876751883 13422907881296492815127825)
              ·
                refine ⟨10067180910972369611345869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13422907881296492815127825 10067180910972369611345869)
                ·
                  refine ⟨3775192841614638604254701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10067180910972369611345869 3775192841614638604254701)
                  ·
                    refine ⟨1415697315605489476595513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3775192841614638604254701 1415697315605489476595513)
                    ·
                      rfl

theorem cell22_4135591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_4135591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135591 prefixEnd_4135591 := by exact prefixLift 4135591
  have htrace : WordTrace (prefixWord ++ tailWord_4135591) baseStart_4135591 baseEnd_4135591 := by
    simpa [prefixWord, tailWord_4135591, baseEnd_4135591] using wordTrace_append hprefix tailTrace_4135591
  have hstable : (prefixWord ++ tailWord_4135591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135591).length < 2 ^ (prefixWord ++ tailWord_4135591).sum := by decide
  have hdescent : baseEnd_4135591 < baseStart_4135591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135647 : List Nat := [1, 1, 2, 3, 2, 3, 3, 1, 1, 5]
def baseStart_4135647 : Nat := 118140960795 + 4135647 * 2 ^ 59
def prefixEnd_4135647 : Nat := 4983230072969 + 3 ^ 40 * 4135647 * 2
def baseEnd_4135647 : Nat := 1415716485549923997195341

theorem tailTrace_4135647 : CollatzResearch.WordTrace tailWord_4135647 prefixEnd_4135647 1415716485549923997195341 := by
  unfold tailWord_4135647
  simp only [CollatzResearch.WordTrace]
  refine ⟨150839438048264706120317195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100559625365509804080211463 150839438048264706120317195)
  ·
    refine ⟨226259157072397059180475793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150839438048264706120317195 226259157072397059180475793)
    ·
      refine ⟨169694367804297794385356845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226259157072397059180475793 169694367804297794385356845)
      ·
        refine ⟨63635387926611672894508817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169694367804297794385356845 63635387926611672894508817)
        ·
          refine ⟨47726540944958754670881613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63635387926611672894508817 47726540944958754670881613)
          ·
            refine ⟨17897452854359533001580605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47726540944958754670881613 17897452854359533001580605)
            ·
              refine ⟨6711544820384824875592727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17897452854359533001580605 6711544820384824875592727)
              ·
                refine ⟨10067317230577237313389091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6711544820384824875592727 10067317230577237313389091)
                ·
                  refine ⟨15100975845865855970083637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10067317230577237313389091 15100975845865855970083637)
                  ·
                    refine ⟨1415716485549923997195341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15100975845865855970083637 1415716485549923997195341)
                    ·
                      rfl

theorem cell22_4135647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 5].length) (baseStart_4135647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135647 prefixEnd_4135647 := by exact prefixLift 4135647
  have htrace : WordTrace (prefixWord ++ tailWord_4135647) baseStart_4135647 baseEnd_4135647 := by
    simpa [prefixWord, tailWord_4135647, baseEnd_4135647] using wordTrace_append hprefix tailTrace_4135647
  have hstable : (prefixWord ++ tailWord_4135647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135647).length < 2 ^ (prefixWord ++ tailWord_4135647).sum := by decide
  have hdescent : baseEnd_4135647 < baseStart_4135647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135662 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_4135662 : Nat := 118140960795 + 4135662 * 2 ^ 59
def prefixEnd_4135662 : Nat := 4983230072969 + 3 ^ 40 * 4135662 * 2
def baseEnd_4135662 : Nat := 1415721620356468958070295

theorem tailTrace_4135662 : CollatzResearch.WordTrace tailWord_4135662 prefixEnd_4135662 1415721620356468958070295 := by
  unfold tailWord_4135662
  simp only [CollatzResearch.WordTrace]
  refine ⟨18854998142901295460264155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100559990095473575788075493 18854998142901295460264155)
  ·
    refine ⟨28282497214351943190396233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18854998142901295460264155 28282497214351943190396233)
    ·
      refine ⟨21211872910763957392797175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28282497214351943190396233 21211872910763957392797175)
      ·
        refine ⟨31817809366145936089195763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21211872910763957392797175 31817809366145936089195763)
        ·
          refine ⟨47726714049218904133793645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31817809366145936089195763 47726714049218904133793645)
          ·
            refine ⟨17897517768457089050172617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47726714049218904133793645 17897517768457089050172617)
            ·
              refine ⟨13423138326342816787629463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17897517768457089050172617 13423138326342816787629463)
              ·
                refine ⟨20134707489514225181444195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13423138326342816787629463 20134707489514225181444195)
                ·
                  refine ⟨30202061234271337772166293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20134707489514225181444195 30202061234271337772166293)
                  ·
                    refine ⟨1415721620356468958070295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30202061234271337772166293 1415721620356468958070295)
                    ·
                      rfl

theorem cell22_4135662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_4135662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135662 prefixEnd_4135662 := by exact prefixLift 4135662
  have htrace : WordTrace (prefixWord ++ tailWord_4135662) baseStart_4135662 baseEnd_4135662 := by
    simpa [prefixWord, tailWord_4135662, baseEnd_4135662] using wordTrace_append hprefix tailTrace_4135662
  have hstable : (prefixWord ++ tailWord_4135662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135662).length < 2 ^ (prefixWord ++ tailWord_4135662).sum := by decide
  have hdescent : baseEnd_4135662 < baseStart_4135662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135666 : List Nat := [3, 2, 1, 3, 1, 4, 1, 3, 4]
def baseStart_4135666 : Nat := 118140960795 + 4135666 * 2 ^ 59
def prefixEnd_4135666 : Nat := 4983230072969 + 3 ^ 40 * 4135666 * 2
def baseEnd_4135666 : Nat := 471907663212738093656761

theorem tailTrace_4135666 : CollatzResearch.WordTrace tailWord_4135666 prefixEnd_4135666 471907663212738093656761 := by
  unfold tailWord_4135666
  simp only [CollatzResearch.WordTrace]
  refine ⟨37710032758798968091314713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100560087356797248243505901 37710032758798968091314713)
  ·
    refine ⟨28282524569099226068486035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37710032758798968091314713 28282524569099226068486035)
    ·
      refine ⟨42423786853648839102729053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28282524569099226068486035 42423786853648839102729053)
      ·
        refine ⟨15908920070118314663523395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42423786853648839102729053 15908920070118314663523395)
        ·
          refine ⟨23863380105177471995285093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15908920070118314663523395 23863380105177471995285093)
          ·
            refine ⟨4474383769720775999115955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23863380105177471995285093 4474383769720775999115955)
            ·
              refine ⟨6711575654581163998673933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4474383769720775999115955 6711575654581163998673933)
              ·
                refine ⟨2516840870467936499502725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6711575654581163998673933 2516840870467936499502725)
                ·
                  refine ⟨471907663212738093656761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2516840870467936499502725 471907663212738093656761)
                  ·
                    rfl

theorem cell22_4135666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_4135666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135666 prefixEnd_4135666 := by exact prefixLift 4135666
  have htrace : WordTrace (prefixWord ++ tailWord_4135666) baseStart_4135666 baseEnd_4135666 := by
    simpa [prefixWord, tailWord_4135666, baseEnd_4135666] using wordTrace_append hprefix tailTrace_4135666
  have hstable : (prefixWord ++ tailWord_4135666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135666).length < 2 ^ (prefixWord ++ tailWord_4135666).sum := by decide
  have hdescent : baseEnd_4135666 < baseStart_4135666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135698 : List Nat := [3, 2, 4, 1, 2, 1, 1, 3, 2, 3]
def baseStart_4135698 : Nat := 118140960795 + 4135698 * 2 ^ 59
def prefixEnd_4135698 : Nat := 4983230072969 + 3 ^ 40 * 4135698 * 2
def baseEnd_4135698 : Nat := 1415733943892176864170185

theorem tailTrace_4135698 : CollatzResearch.WordTrace tailWord_4135698 prefixEnd_4135698 1415733943892176864170185 := by
  unfold tailWord_4135698
  simp only [CollatzResearch.WordTrace]
  refine ⟨37710324542769985457605937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100560865447386627886949165 37710324542769985457605937)
  ·
    refine ⟨28282743407077489093204453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37710324542769985457605937 28282743407077489093204453)
    ·
      refine ⟨5303014388827029204975835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28282743407077489093204453 5303014388827029204975835)
      ·
        refine ⟨7954521583240543807463753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5303014388827029204975835 7954521583240543807463753)
        ·
          refine ⟨5965891187430407855597815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7954521583240543807463753 5965891187430407855597815)
          ·
            refine ⟨8948836781145611783396723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5965891187430407855597815 8948836781145611783396723)
            ·
              refine ⟨13423255171718417675095085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8948836781145611783396723 13423255171718417675095085)
              ·
                refine ⟨5033720689394406628160657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13423255171718417675095085 5033720689394406628160657)
                ·
                  refine ⟨3775290517045804971120493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5033720689394406628160657 3775290517045804971120493)
                  ·
                    refine ⟨1415733943892176864170185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3775290517045804971120493 1415733943892176864170185)
                    ·
                      rfl

theorem cell22_4135698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_4135698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135698 prefixEnd_4135698 := by exact prefixLift 4135698
  have htrace : WordTrace (prefixWord ++ tailWord_4135698) baseStart_4135698 baseEnd_4135698 := by
    simpa [prefixWord, tailWord_4135698, baseEnd_4135698] using wordTrace_append hprefix tailTrace_4135698
  have hstable : (prefixWord ++ tailWord_4135698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135698).length < 2 ^ (prefixWord ++ tailWord_4135698).sum := by decide
  have hdescent : baseEnd_4135698 < baseStart_4135698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135705 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 9]
def baseStart_4135705 : Nat := 118140960795 + 4135705 * 2 ^ 59
def prefixEnd_4135705 : Nat := 4983230072969 + 3 ^ 40 * 4135705 * 2
def baseEnd_4135705 : Nat := 471912113378410393081721

theorem tailTrace_4135705 : CollatzResearch.WordTrace tailWord_4135705 prefixEnd_4135705 471912113378410393081721 := by
  unfold tailWord_4135705
  simp only [CollatzResearch.WordTrace]
  refine ⟨150841553482054582025928569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100561035654703054683952379 150841553482054582025928569)
  ·
    refine ⟨113131165111540936519446427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150841553482054582025928569 113131165111540936519446427)
    ·
      refine ⟨169696747667311404779169641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113131165111540936519446427 169696747667311404779169641)
      ·
        refine ⟨127272560750483553584377231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169696747667311404779169641 127272560750483553584377231)
        ·
          refine ⟨190908841125725330376565847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127272560750483553584377231 190908841125725330376565847)
          ·
            refine ⟨286363261688587995564848771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190908841125725330376565847 286363261688587995564848771)
            ·
              refine ⟨429544892532881993347273157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286363261688587995564848771 429544892532881993347273157)
              ·
                refine ⟨80539667349915373752613717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 429544892532881993347273157 80539667349915373752613717)
                ·
                  refine ⟨471912113378410393081721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80539667349915373752613717 471912113378410393081721)
                  ·
                    rfl

theorem cell22_4135705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 9].length) (baseStart_4135705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135705 prefixEnd_4135705 := by exact prefixLift 4135705
  have htrace : WordTrace (prefixWord ++ tailWord_4135705) baseStart_4135705 baseEnd_4135705 := by
    simpa [prefixWord, tailWord_4135705, baseEnd_4135705] using wordTrace_append hprefix tailTrace_4135705
  have hstable : (prefixWord ++ tailWord_4135705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135705).length < 2 ^ (prefixWord ++ tailWord_4135705).sum := by decide
  have hdescent : baseEnd_4135705 < baseStart_4135705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135743 : List Nat := [1, 1, 2, 2, 5, 1, 4, 2, 1, 3]
def baseStart_4135743 : Nat := 118140960795 + 4135743 * 2 ^ 59
def prefixEnd_4135743 : Nat := 4983230072969 + 3 ^ 40 * 4135743 * 2
def baseEnd_4135743 : Nat := 1415749348311811746795047

theorem tailTrace_4135743 : CollatzResearch.WordTrace tailWord_4135743 prefixEnd_4135743 1415749348311811746795047 := by
  unfold tailWord_4135743
  simp only [CollatzResearch.WordTrace]
  refine ⟨150842939455916914515811883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100561959637277943010541255 150842939455916914515811883)
  ·
    refine ⟨226264409183875371773717825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150842939455916914515811883 226264409183875371773717825)
    ·
      refine ⟨169698306887906528830288369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226264409183875371773717825 169698306887906528830288369)
      ·
        refine ⟨127273730165929896622716277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169698306887906528830288369 127273730165929896622716277)
        ·
          refine ⟨11931912203055927808379651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127273730165929896622716277 11931912203055927808379651)
          ·
            refine ⟨17897868304583891712569477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11931912203055927808379651 17897868304583891712569477)
            ·
              refine ⟨3355850307109479696106777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17897868304583891712569477 3355850307109479696106777)
              ·
                refine ⟨2516887730332109772080083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3355850307109479696106777 2516887730332109772080083)
                ·
                  refine ⟨3775331595498164658120125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2516887730332109772080083 3775331595498164658120125)
                  ·
                    refine ⟨1415749348311811746795047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3775331595498164658120125 1415749348311811746795047)
                    ·
                      rfl

theorem cell22_4135743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 1, 3].length) (baseStart_4135743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135743 prefixEnd_4135743 := by exact prefixLift 4135743
  have htrace : WordTrace (prefixWord ++ tailWord_4135743) baseStart_4135743 baseEnd_4135743 := by
    simpa [prefixWord, tailWord_4135743, baseEnd_4135743] using wordTrace_append hprefix tailTrace_4135743
  have hstable : (prefixWord ++ tailWord_4135743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135743).length < 2 ^ (prefixWord ++ tailWord_4135743).sum := by decide
  have hdescent : baseEnd_4135743 < baseStart_4135743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135752 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 5, 4]
def baseStart_4135752 : Nat := 118140960795 + 4135752 * 2 ^ 59
def prefixEnd_4135752 : Nat := 4983230072969 + 3 ^ 40 * 4135752 * 2
def baseEnd_4135752 : Nat := 1415752429195738723320019

theorem tailTrace_4135752 : CollatzResearch.WordTrace tailWord_4135752 prefixEnd_4135752 1415752429195738723320019 := by
  unfold tailWord_4135752
  simp only [CollatzResearch.WordTrace]
  refine ⟨75421633856442154526444755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100562178475256206035259673 75421633856442154526444755)
  ·
    refine ⟨113132450784663231789667133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75421633856442154526444755 113132450784663231789667133)
    ·
      refine ⟨42424669044248711921125175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113132450784663231789667133 42424669044248711921125175)
      ·
        refine ⟨63637003566373067881687763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42424669044248711921125175 63637003566373067881687763)
        ·
          refine ⟨95455505349559601822531645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63637003566373067881687763 95455505349559601822531645)
          ·
            refine ⟨35795814506084850683449367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95455505349559601822531645 35795814506084850683449367)
            ·
              refine ⟨53693721759127276025174051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35795814506084850683449367 53693721759127276025174051)
              ·
                refine ⟨80540582638690914037761077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53693721759127276025174051 80540582638690914037761077)
                ·
                  refine ⟨7550679622377273191040101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80540582638690914037761077 7550679622377273191040101)
                  ·
                    refine ⟨1415752429195738723320019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7550679622377273191040101 1415752429195738723320019)
                    ·
                      rfl

theorem cell22_4135752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_4135752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135752 prefixEnd_4135752 := by exact prefixLift 4135752
  have htrace : WordTrace (prefixWord ++ tailWord_4135752) baseStart_4135752 baseEnd_4135752 := by
    simpa [prefixWord, tailWord_4135752, baseEnd_4135752] using wordTrace_append hprefix tailTrace_4135752
  have hstable : (prefixWord ++ tailWord_4135752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135752).length < 2 ^ (prefixWord ++ tailWord_4135752).sum := by decide
  have hdescent : baseEnd_4135752 < baseStart_4135752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135767 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 8]
def baseStart_4135767 : Nat := 118140960795 + 4135767 * 2 ^ 59
def prefixEnd_4135767 : Nat := 4983230072969 + 3 ^ 40 * 4135767 * 2
def baseEnd_4135767 : Nat := 471919188000761228064991

theorem tailTrace_4135767 : CollatzResearch.WordTrace tailWord_4135767 prefixEnd_4135767 471919188000761228064991 := by
  unfold tailWord_4135767
  simp only [CollatzResearch.WordTrace]
  refine ⟨150843814807829966614685555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100562543205219977743123703 150843814807829966614685555)
  ·
    refine ⟨226265722211744949922028333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150843814807829966614685555 226265722211744949922028333)
    ·
      refine ⟨84849645829404356220760625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226265722211744949922028333 84849645829404356220760625)
      ·
        refine ⟨63637234372053267165570469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84849645829404356220760625 63637234372053267165570469)
        ·
          refine ⟨11931981444759987593544463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63637234372053267165570469 11931981444759987593544463)
          ·
            refine ⟨17897972167139981390316695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11931981444759987593544463 17897972167139981390316695)
            ·
              refine ⟨26846958250709972085475043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17897972167139981390316695 26846958250709972085475043)
              ·
                refine ⟨40270437376064958128212565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26846958250709972085475043 40270437376064958128212565)
                ·
                  refine ⟨471919188000761228064991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40270437376064958128212565 471919188000761228064991)
                  ·
                    rfl

theorem cell22_4135767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 8].length) (baseStart_4135767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135767 prefixEnd_4135767 := by exact prefixLift 4135767
  have htrace : WordTrace (prefixWord ++ tailWord_4135767) baseStart_4135767 baseEnd_4135767 := by
    simpa [prefixWord, tailWord_4135767, baseEnd_4135767] using wordTrace_append hprefix tailTrace_4135767
  have hstable : (prefixWord ++ tailWord_4135767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135767).length < 2 ^ (prefixWord ++ tailWord_4135767).sum := by decide
  have hdescent : baseEnd_4135767 < baseStart_4135767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135812 : List Nat := [2, 3, 2, 1, 1, 1, 1, 11]
def baseStart_4135812 : Nat := 118140960795 + 4135812 * 2 ^ 59
def prefixEnd_4135812 : Nat := 4983230072969 + 3 ^ 40 * 4135812 * 2
def baseEnd_4135812 : Nat := 157308107602435396313315

theorem tailTrace_4135812 : CollatzResearch.WordTrace tailWord_4135812 prefixEnd_4135812 157308107602435396313315 := by
  unfold tailWord_4135812
  simp only [CollatzResearch.WordTrace]
  refine ⟨75422728046333469650036845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100563637395111292866715793 75422728046333469650036845)
  ·
    refine ⟨28283523017375051118763817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75422728046333469650036845 28283523017375051118763817)
    ·
      refine ⟨21212642263031288339072863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28283523017375051118763817 21212642263031288339072863)
      ·
        refine ⟨31818963394546932508609295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21212642263031288339072863 31818963394546932508609295)
        ·
          refine ⟨47728445091820398762913943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31818963394546932508609295 47728445091820398762913943)
          ·
            refine ⟨71592667637730598144370915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47728445091820398762913943 71592667637730598144370915)
            ·
              refine ⟨107389001456595897216556373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71592667637730598144370915 107389001456595897216556373)
              ·
                refine ⟨157308107602435396313315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 107389001456595897216556373 157308107602435396313315)
                ·
                  rfl

theorem cell22_4135812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 11].length) (baseStart_4135812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135812 prefixEnd_4135812 := by exact prefixLift 4135812
  have htrace : WordTrace (prefixWord ++ tailWord_4135812) baseStart_4135812 baseEnd_4135812 := by
    simpa [prefixWord, tailWord_4135812, baseEnd_4135812] using wordTrace_append hprefix tailTrace_4135812
  have hstable : (prefixWord ++ tailWord_4135812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135812).length < 2 ^ (prefixWord ++ tailWord_4135812).sum := by decide
  have hdescent : baseEnd_4135812 < baseStart_4135812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135816 : List Nat := [2, 1, 3, 3, 2, 3, 1, 1, 1, 5]
def baseStart_4135816 : Nat := 118140960795 + 4135816 * 2 ^ 59
def prefixEnd_4135816 : Nat := 4983230072969 + 3 ^ 40 * 4135816 * 2
def baseEnd_4135816 : Nat := 1415774337703663889719823

theorem tailTrace_4135816 : CollatzResearch.WordTrace tailWord_4135816 prefixEnd_4135816 1415774337703663889719823 := by
  unfold tailWord_4135816
  simp only [CollatzResearch.WordTrace]
  refine ⟨75422800992326223991609651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100563734656434965322146201 75422800992326223991609651)
  ·
    refine ⟨113134201488489335987414477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75422800992326223991609651 113134201488489335987414477)
    ·
      refine ⟨42425325558183500995280429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113134201488489335987414477 42425325558183500995280429)
      ·
        refine ⟨15909497084318812873230161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42425325558183500995280429 15909497084318812873230161)
        ·
          refine ⟨11932122813239109654922621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15909497084318812873230161 11932122813239109654922621)
          ·
            refine ⟨4474546054964666120595983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11932122813239109654922621 4474546054964666120595983)
            ·
              refine ⟨6711819082446999180893975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4474546054964666120595983 6711819082446999180893975)
              ·
                refine ⟨10067728623670498771340963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6711819082446999180893975 10067728623670498771340963)
                ·
                  refine ⟨15101592935505748157011445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10067728623670498771340963 15101592935505748157011445)
                  ·
                    refine ⟨1415774337703663889719823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15101592935505748157011445 1415774337703663889719823)
                    ·
                      rfl

theorem cell22_4135816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_4135816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135816 prefixEnd_4135816 := by exact prefixLift 4135816
  have htrace : WordTrace (prefixWord ++ tailWord_4135816) baseStart_4135816 baseEnd_4135816 := by
    simpa [prefixWord, tailWord_4135816, baseEnd_4135816] using wordTrace_append hprefix tailTrace_4135816
  have hstable : (prefixWord ++ tailWord_4135816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135816).length < 2 ^ (prefixWord ++ tailWord_4135816).sum := by decide
  have hdescent : baseEnd_4135816 < baseStart_4135816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135829 : List Nat := [1, 3, 2, 1, 1, 4, 4, 6]
def baseStart_4135829 : Nat := 118140960795 + 4135829 * 2 ^ 59
def prefixEnd_4135829 : Nat := 4983230072969 + 3 ^ 40 * 4135829 * 2
def baseEnd_4135829 : Nat := 157308754207704021016087

theorem tailTrace_4135829 : CollatzResearch.WordTrace tailWord_4135829 prefixEnd_4135829 157308754207704021016087 := by
  unfold tailWord_4135829
  simp only [CollatzResearch.WordTrace]
  refine ⟨150846076133605351203442541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100564050755736900802295027 150846076133605351203442541)
  ·
    refine ⟨56567278550102006701290953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150846076133605351203442541 56567278550102006701290953)
    ·
      refine ⟨42425458912576505025968215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56567278550102006701290953 42425458912576505025968215)
      ·
        refine ⟨63638188368864757538952323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42425458912576505025968215 63638188368864757538952323)
        ·
          refine ⟨95457282553297136308428485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63638188368864757538952323 95457282553297136308428485)
          ·
            refine ⟨17898240478743213057830341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95457282553297136308428485 17898240478743213057830341)
            ·
              refine ⟨3355920089764352448343189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17898240478743213057830341 3355920089764352448343189)
              ·
                refine ⟨157308754207704021016087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3355920089764352448343189 157308754207704021016087)
                ·
                  rfl

theorem cell22_4135829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 6].length) (baseStart_4135829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135829 prefixEnd_4135829 := by exact prefixLift 4135829
  have htrace : WordTrace (prefixWord ++ tailWord_4135829) baseStart_4135829 baseEnd_4135829 := by
    simpa [prefixWord, tailWord_4135829, baseEnd_4135829] using wordTrace_append hprefix tailTrace_4135829
  have hstable : (prefixWord ++ tailWord_4135829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135829).length < 2 ^ (prefixWord ++ tailWord_4135829).sum := by decide
  have hdescent : baseEnd_4135829 < baseStart_4135829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135994 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 2, 6]
def baseStart_4135994 : Nat := 118140960795 + 4135994 * 2 ^ 59
def prefixEnd_4135994 : Nat := 4983230072969 + 3 ^ 40 * 4135994 * 2
def baseEnd_4135994 : Nat := 1415835270741330758769277

theorem tailTrace_4135994 : CollatzResearch.WordTrace tailWord_4135994 prefixEnd_4135994 1415835270741330758769277 := by
  unfold tailWord_4135994
  simp only [CollatzResearch.WordTrace]
  refine ⟨37713023544501896095799759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100568062785338389588799357 37713023544501896095799759)
  ·
    refine ⟨56569535316752844143699639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37713023544501896095799759 56569535316752844143699639)
    ·
      refine ⟨84854302975129266215549459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56569535316752844143699639 84854302975129266215549459)
      ·
        refine ⟨127281454462693899323324189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84854302975129266215549459 127281454462693899323324189)
        ·
          refine ⟨47730545423510212246246571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127281454462693899323324189 47730545423510212246246571)
          ·
            refine ⟨71595818135265318369369857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47730545423510212246246571 71595818135265318369369857)
            ·
              refine ⟨53696863601448988777027393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71595818135265318369369857 53696863601448988777027393)
              ·
                refine ⟨40272647701086741582770545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53696863601448988777027393 40272647701086741582770545)
                ·
                  refine ⟨30204485775815056187077909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40272647701086741582770545 30204485775815056187077909)
                  ·
                    refine ⟨1415835270741330758769277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30204485775815056187077909 1415835270741330758769277)
                    ·
                      rfl

theorem cell22_4135994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_4135994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135994 prefixEnd_4135994 := by exact prefixLift 4135994
  have htrace : WordTrace (prefixWord ++ tailWord_4135994) baseStart_4135994 baseEnd_4135994 := by
    simpa [prefixWord, tailWord_4135994, baseEnd_4135994] using wordTrace_append hprefix tailTrace_4135994
  have hstable : (prefixWord ++ tailWord_4135994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135994).length < 2 ^ (prefixWord ++ tailWord_4135994).sum := by decide
  have hdescent : baseEnd_4135994 < baseStart_4135994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4135998 : List Nat := [4, 2, 1, 3, 1, 1, 4, 6]
def baseStart_4135998 : Nat := 118140960795 + 4135998 * 2 ^ 59
def prefixEnd_4135998 : Nat := 4983230072969 + 3 ^ 40 * 4135998 * 2
def baseEnd_4135998 : Nat := 157315182224786231296585

theorem tailTrace_4135998 : CollatzResearch.WordTrace tailWord_4135998 prefixEnd_4135998 157315182224786231296585 := by
  unfold tailWord_4135998
  simp only [CollatzResearch.WordTrace]
  refine ⟨18856530008749136633293081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100568160046662062044229765 18856530008749136633293081)
  ·
    refine ⟨14142397506561852474969811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18856530008749136633293081 14142397506561852474969811)
    ·
      refine ⟨21213596259842778712454717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14142397506561852474969811 21213596259842778712454717)
      ·
        refine ⟨7955098597441042017170519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21213596259842778712454717 7955098597441042017170519)
        ·
          refine ⟨11932647896161563025755779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7955098597441042017170519 11932647896161563025755779)
          ·
            refine ⟨17898971844242344538633669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11932647896161563025755779 17898971844242344538633669)
            ·
              refine ⟨3356057220795439600993813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17898971844242344538633669 3356057220795439600993813)
              ·
                refine ⟨157315182224786231296585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3356057220795439600993813 157315182224786231296585)
                ·
                  rfl

theorem cell22_4135998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_4135998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4135998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4135998 prefixEnd_4135998 := by exact prefixLift 4135998
  have htrace : WordTrace (prefixWord ++ tailWord_4135998) baseStart_4135998 baseEnd_4135998 := by
    simpa [prefixWord, tailWord_4135998, baseEnd_4135998] using wordTrace_append hprefix tailTrace_4135998
  have hstable : (prefixWord ++ tailWord_4135998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4135998).length < 2 ^ (prefixWord ++ tailWord_4135998).sum := by decide
  have hdescent : baseEnd_4135998 < baseStart_4135998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4135998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136103 : List Nat := [1, 1, 6, 2, 1, 1, 1, 3, 1, 5]
def baseStart_4136103 : Nat := 118140960795 + 4136103 * 2 ^ 59
def prefixEnd_4136103 : Nat := 4983230072969 + 3 ^ 40 * 4136103 * 2
def baseEnd_4136103 : Nat := 1415872583668890807793943

theorem tailTrace_4136103 : CollatzResearch.WordTrace tailWord_4136103 prefixEnd_4136103 1415872583668890807793943 := by
  unfold tailWord_4136103
  simp only [CollatzResearch.WordTrace]
  refine ⟨150856069734612695998916963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100570713156408463999277975 150856069734612695998916963)
  ·
    refine ⟨226284104601919043998375445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150856069734612695998916963 226284104601919043998375445)
    ·
      refine ⟨10607067403214955187423849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 226284104601919043998375445 10607067403214955187423849)
      ·
        refine ⟨7955300552411216390567887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10607067403214955187423849 7955300552411216390567887)
        ·
          refine ⟨11932950828616824585851831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7955300552411216390567887 11932950828616824585851831)
          ·
            refine ⟨17899426242925236878777747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11932950828616824585851831 17899426242925236878777747)
            ·
              refine ⟨26849139364387855318166621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17899426242925236878777747 26849139364387855318166621)
              ·
                refine ⟨10068427261645445744312483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26849139364387855318166621 10068427261645445744312483)
                ·
                  refine ⟨15102640892468168616468725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10068427261645445744312483 15102640892468168616468725)
                  ·
                    refine ⟨1415872583668890807793943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15102640892468168616468725 1415872583668890807793943)
                    ·
                      rfl

theorem cell22_4136103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_4136103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4136103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4136103 prefixEnd_4136103 := by exact prefixLift 4136103
  have htrace : WordTrace (prefixWord ++ tailWord_4136103) baseStart_4136103 baseEnd_4136103 := by
    simpa [prefixWord, tailWord_4136103, baseEnd_4136103] using wordTrace_append hprefix tailTrace_4136103
  have hstable : (prefixWord ++ tailWord_4136103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136103).length < 2 ^ (prefixWord ++ tailWord_4136103).sum := by decide
  have hdescent : baseEnd_4136103 < baseStart_4136103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136167 : List Nat := [1, 1, 5, 3, 3, 1, 2, 6]
def baseStart_4136167 : Nat := 118140960795 + 4136167 * 2 ^ 59
def prefixEnd_4136167 : Nat := 4983230072969 + 3 ^ 40 * 4136167 * 2
def baseEnd_4136167 : Nat := 157321610241868441577083

theorem tailTrace_4136167 : CollatzResearch.WordTrace tailWord_4136167 prefixEnd_4136167 157321610241868441577083 := by
  unfold tailWord_4136167
  simp only [CollatzResearch.WordTrace]
  refine ⟨150858404006380834929246755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100572269337587223286164503 150858404006380834929246755)
  ·
    refine ⟨226287606009571252393870133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150858404006380834929246755 226287606009571252393870133)
    ·
      refine ⟨21214463063397304911925325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226287606009571252393870133 21214463063397304911925325)
      ·
        refine ⟨7955423648773989341971997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21214463063397304911925325 7955423648773989341971997)
        ·
          refine ⟨2983283868290246003239499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7955423648773989341971997 2983283868290246003239499)
          ·
            refine ⟨4474925802435369004859249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2983283868290246003239499 4474925802435369004859249)
            ·
              refine ⟨3356194351826526753644437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4474925802435369004859249 3356194351826526753644437)
              ·
                refine ⟨157321610241868441577083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3356194351826526753644437 157321610241868441577083)
                ·
                  rfl

theorem cell22_4136167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 6].length) (baseStart_4136167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4136167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4136167 prefixEnd_4136167 := by exact prefixLift 4136167
  have htrace : WordTrace (prefixWord ++ tailWord_4136167) baseStart_4136167 baseEnd_4136167 := by
    simpa [prefixWord, tailWord_4136167, baseEnd_4136167] using wordTrace_append hprefix tailTrace_4136167
  have hstable : (prefixWord ++ tailWord_4136167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136167).length < 2 ^ (prefixWord ++ tailWord_4136167).sum := by decide
  have hdescent : baseEnd_4136167 < baseStart_4136167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136242 : List Nat := [3, 2, 1, 1, 4, 2, 3, 1, 1, 4]
def baseStart_4136242 : Nat := 118140960795 + 4136242 * 2 ^ 59
def prefixEnd_4136242 : Nat := 4983230072969 + 3 ^ 40 * 4136242 * 2
def baseEnd_4136242 : Nat := 1415920166209540778568517

theorem tailTrace_4136242 : CollatzResearch.WordTrace tailWord_4136242 prefixEnd_4136242 1415920166209540778568517 := by
  unfold tailWord_4136242
  simp only [CollatzResearch.WordTrace]
  refine ⟨37715284870277280684556745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100574092987406081825484653 37715284870277280684556745)
  ·
    refine ⟨28286463652707960513417559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37715284870277280684556745 28286463652707960513417559)
    ·
      refine ⟨42429695479061940770126339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28286463652707960513417559 42429695479061940770126339)
      ·
        refine ⟨63644543218592911155189509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42429695479061940770126339 63644543218592911155189509)
        ·
          refine ⟨11933351853486170841598033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63644543218592911155189509 11933351853486170841598033)
          ·
            refine ⟨8950013890114628131198525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11933351853486170841598033 8950013890114628131198525)
            ·
              refine ⟨3356255208792985549199447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8950013890114628131198525 3356255208792985549199447)
              ·
                refine ⟨5034382813189478323799171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3356255208792985549199447 5034382813189478323799171)
                ·
                  refine ⟨7551574219784217485698757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5034382813189478323799171 7551574219784217485698757)
                  ·
                    refine ⟨1415920166209540778568517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7551574219784217485698757 1415920166209540778568517)
                    ·
                      rfl

theorem cell22_4136242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_4136242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4136242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4136242 prefixEnd_4136242 := by exact prefixLift 4136242
  have htrace : WordTrace (prefixWord ++ tailWord_4136242) baseStart_4136242 baseEnd_4136242 := by
    simpa [prefixWord, tailWord_4136242, baseEnd_4136242] using wordTrace_append hprefix tailTrace_4136242
  have hstable : (prefixWord ++ tailWord_4136242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136242).length < 2 ^ (prefixWord ++ tailWord_4136242).sum := by decide
  have hdescent : baseEnd_4136242 < baseStart_4136242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136255 : List Nat := [1, 1, 2, 2, 4, 2, 1, 4, 2, 3]
def baseStart_4136255 : Nat := 118140960795 + 4136255 * 2 ^ 59
def prefixEnd_4136255 : Nat := 4983230072969 + 3 ^ 40 * 4136255 * 2
def baseEnd_4136255 : Nat := 1415924616375213077993477

theorem tailTrace_4136255 : CollatzResearch.WordTrace tailWord_4136255 prefixEnd_4136255 1415924616375213077993477 := by
  unfold tailWord_4136255
  simp only [CollatzResearch.WordTrace]
  refine ⟨150861613630062025958450219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100574409086708017305633479 150861613630062025958450219)
  ·
    refine ⟨226292420445093038937675329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150861613630062025958450219 226292420445093038937675329)
    ·
      refine ⟨169719315333819779203256497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226292420445093038937675329 169719315333819779203256497)
      ·
        refine ⟨127289486500364834402442373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169719315333819779203256497 127289486500364834402442373)
        ·
          refine ⟨23866778718818406450457945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127289486500364834402442373 23866778718818406450457945)
          ·
            refine ⟨17900084039113804837843459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23866778718818406450457945 17900084039113804837843459)
            ·
              refine ⟨26850126058670707256765189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17900084039113804837843459 26850126058670707256765189)
              ·
                refine ⟨5034398636000757610643473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26850126058670707256765189 5034398636000757610643473)
                ·
                  refine ⟨3775798977000568207982605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5034398636000757610643473 3775798977000568207982605)
                  ·
                    refine ⟨1415924616375213077993477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3775798977000568207982605 1415924616375213077993477)
                    ·
                      rfl

theorem cell22_4136255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 3].length) (baseStart_4136255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4136255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4136255 prefixEnd_4136255 := by exact prefixLift 4136255
  have htrace : WordTrace (prefixWord ++ tailWord_4136255) baseStart_4136255 baseEnd_4136255 := by
    simpa [prefixWord, tailWord_4136255, baseEnd_4136255] using wordTrace_append hprefix tailTrace_4136255
  have hstable : (prefixWord ++ tailWord_4136255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136255).length < 2 ^ (prefixWord ++ tailWord_4136255).sum := by decide
  have hdescent : baseEnd_4136255 < baseStart_4136255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136257 : List Nat := [1, 2, 5, 2, 1, 2, 1, 4, 4]
def baseStart_4136257 : Nat := 118140960795 + 4136257 * 2 ^ 59
def prefixEnd_4136257 : Nat := 4983230072969 + 3 ^ 40 * 4136257 * 2
def baseEnd_4136257 : Nat := 471975100338695246481157

theorem tailTrace_4136257 : CollatzResearch.WordTrace tailWord_4136257 prefixEnd_4136257 471975100338695246481157 := by
  unfold tailWord_4136257
  simp only [CollatzResearch.WordTrace]
  refine ⟨150861686576054780300023025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100574457717369853533348683 150861686576054780300023025)
  ·
    refine ⟨113146264932041085225017269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150861686576054780300023025 113146264932041085225017269)
    ·
      refine ⟨10607462337378851739845369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113146264932041085225017269 10607462337378851739845369)
      ·
        refine ⟨7955596753034138804884027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10607462337378851739845369 7955596753034138804884027)
        ·
          refine ⟨11933395129551208207326041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7955596753034138804884027 11933395129551208207326041)
          ·
            refine ⟨8950046347163406155494531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11933395129551208207326041 8950046347163406155494531)
            ·
              refine ⟨13425069520745109233241797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8950046347163406155494531 13425069520745109233241797)
              ·
                refine ⟨2517200535139707981232837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13425069520745109233241797 2517200535139707981232837)
                ·
                  refine ⟨471975100338695246481157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2517200535139707981232837 471975100338695246481157)
                  ·
                    rfl

theorem cell22_4136257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 4].length) (baseStart_4136257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4136257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4136257 prefixEnd_4136257 := by exact prefixLift 4136257
  have htrace : WordTrace (prefixWord ++ tailWord_4136257) baseStart_4136257 baseEnd_4136257 := by
    simpa [prefixWord, tailWord_4136257, baseEnd_4136257] using wordTrace_append hprefix tailTrace_4136257
  have hstable : (prefixWord ++ tailWord_4136257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136257).length < 2 ^ (prefixWord ++ tailWord_4136257).sum := by decide
  have hdescent : baseEnd_4136257 < baseStart_4136257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136268 : List Nat := [2, 2, 1, 3, 2, 2, 3, 7]
def baseStart_4136268 : Nat := 118140960795 + 4136268 * 2 ^ 59
def prefixEnd_4136268 : Nat := 4983230072969 + 3 ^ 40 * 4136268 * 2
def baseEnd_4136268 : Nat := 157325451837876153046493

theorem tailTrace_4136268 : CollatzResearch.WordTrace tailWord_4136268 prefixEnd_4136268 157325451837876153046493 := by
  unfold tailWord_4136268
  simp only [CollatzResearch.WordTrace]
  refine ⟨75431043889507464589336729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100574725186009952785782305 75431043889507464589336729)
  ·
    refine ⟨56573282917130598442002547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75431043889507464589336729 56573282917130598442002547)
    ·
      refine ⟨84859924375695897663003821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56573282917130598442002547 84859924375695897663003821)
      ·
        refine ⟨31822471640885961623626433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84859924375695897663003821 31822471640885961623626433)
        ·
          refine ⟨23866853730664471217719825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31822471640885961623626433 23866853730664471217719825)
          ·
            refine ⟨17900140297998353413289869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23866853730664471217719825 17900140297998353413289869)
            ·
              refine ⟨6712552611749382529983701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17900140297998353413289869 6712552611749382529983701)
              ·
                refine ⟨157325451837876153046493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6712552611749382529983701 157325451837876153046493)
                ·
                  rfl

theorem cell22_4136268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 7].length) (baseStart_4136268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4136268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4136268 prefixEnd_4136268 := by exact prefixLift 4136268
  have htrace : WordTrace (prefixWord ++ tailWord_4136268) baseStart_4136268 baseEnd_4136268 := by
    simpa [prefixWord, tailWord_4136268, baseEnd_4136268] using wordTrace_append hprefix tailTrace_4136268
  have hstable : (prefixWord ++ tailWord_4136268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136268).length < 2 ^ (prefixWord ++ tailWord_4136268).sum := by decide
  have hdescent : baseEnd_4136268 < baseStart_4136268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136317 : List Nat := [1, 4, 1, 1, 2, 2, 1, 6, 1, 3]
def baseStart_4136317 : Nat := 118140960795 + 4136317 * 2 ^ 59
def prefixEnd_4136317 : Nat := 4983230072969 + 3 ^ 40 * 4136317 * 2
def baseEnd_4136317 : Nat := 1415945840242265582943287

theorem tailTrace_4136317 : CollatzResearch.WordTrace tailWord_4136317 prefixEnd_4136317 1415945840242265582943287 := by
  unfold tailWord_4136317
  simp only [CollatzResearch.WordTrace]
  refine ⟨150863874955837410547207205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100575916637224940364804803 150863874955837410547207205)
  ·
    refine ⟨28286976554219514477601351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150863874955837410547207205 28286976554219514477601351)
    ·
      refine ⟨42430464831329271716402027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28286976554219514477601351 42430464831329271716402027)
      ·
        refine ⟨63645697246993907574603041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42430464831329271716402027 63645697246993907574603041)
        ·
          refine ⟨47734272935245430680952281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63645697246993907574603041 47734272935245430680952281)
          ·
            refine ⟨35800704701434073010714211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47734272935245430680952281 35800704701434073010714211)
            ·
              refine ⟨53701057052151109516071317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35800704701434073010714211 53701057052151109516071317)
              ·
                refine ⟨2517237049319583258565843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53701057052151109516071317 2517237049319583258565843)
                ·
                  refine ⟨3775855573979374887848765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2517237049319583258565843 3775855573979374887848765)
                  ·
                    refine ⟨1415945840242265582943287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3775855573979374887848765 1415945840242265582943287)
                    ·
                      rfl

theorem cell22_4136317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_4136317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4136317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4136317 prefixEnd_4136317 := by exact prefixLift 4136317
  have htrace : WordTrace (prefixWord ++ tailWord_4136317) baseStart_4136317 baseEnd_4136317 := by
    simpa [prefixWord, tailWord_4136317, baseEnd_4136317] using wordTrace_append hprefix tailTrace_4136317
  have hstable : (prefixWord ++ tailWord_4136317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136317).length < 2 ^ (prefixWord ++ tailWord_4136317).sum := by decide
  have hdescent : baseEnd_4136317 < baseStart_4136317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136426 : List Nat := [3, 1, 3, 1, 4, 2, 2, 2, 4]
def baseStart_4136426 : Nat := 118140960795 + 4136426 * 2 ^ 59
def prefixEnd_4136426 : Nat := 4983230072969 + 3 ^ 40 * 4136426 * 2
def baseEnd_4136426 : Nat := 471994384389941877322651

theorem tailTrace_4136426 : CollatzResearch.WordTrace tailWord_4136426 prefixEnd_4136426 471994384389941877322651 := by
  unfold tailWord_4136426
  simp only [CollatzResearch.WordTrace]
  refine ⟨37716962628110630540731283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100578567008295014775283421 37716962628110630540731283)
  ·
    refine ⟨56575443942165945811096925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37716962628110630540731283 56575443942165945811096925)
    ·
      refine ⟨21215791478312229679161347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56575443942165945811096925 21215791478312229679161347)
      ·
        refine ⟨31823687217468344518742021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21215791478312229679161347 31823687217468344518742021)
        ·
          refine ⟨5966941353275314597264129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31823687217468344518742021 5966941353275314597264129)
          ·
            refine ⟨4475206014956485947948097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5966941353275314597264129 4475206014956485947948097)
            ·
              refine ⟨3356404511217364460961073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4475206014956485947948097 3356404511217364460961073)
              ·
                refine ⟨2517303383413023345720805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3356404511217364460961073 2517303383413023345720805)
                ·
                  refine ⟨471994384389941877322651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2517303383413023345720805 471994384389941877322651)
                  ·
                    rfl

theorem cell22_4136426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_4136426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4136426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4136426 prefixEnd_4136426 := by exact prefixLift 4136426
  have htrace : WordTrace (prefixWord ++ tailWord_4136426) baseStart_4136426 baseEnd_4136426 := by
    simpa [prefixWord, tailWord_4136426, baseEnd_4136426] using wordTrace_append hprefix tailTrace_4136426
  have hstable : (prefixWord ++ tailWord_4136426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136426).length < 2 ^ (prefixWord ++ tailWord_4136426).sum := by decide
  have hdescent : baseEnd_4136426 < baseStart_4136426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136437 : List Nat := [1, 3, 5, 1, 1, 1, 3, 7]
def baseStart_4136437 : Nat := 118140960795 + 4136437 * 2 ^ 59
def prefixEnd_4136437 : Nat := 4983230072969 + 3 ^ 40 * 4136437 * 2
def baseEnd_4136437 : Nat := 157331879854958363326991

theorem tailTrace_4136437 : CollatzResearch.WordTrace tailWord_4136437 prefixEnd_4136437 157331879854958363326991 := by
  unfold tailWord_4136437
  simp only [CollatzResearch.WordTrace]
  refine ⟨150868251715402671041575565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100578834476935114027717043 150868251715402671041575565)
  ·
    refine ⟨56575594393276001640590837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150868251715402671041575565 56575594393276001640590837)
    ·
      refine ⟨5303961974369625153805391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56575594393276001640590837 5303961974369625153805391)
      ·
        refine ⟨7955942961554437730708087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5303961974369625153805391 7955942961554437730708087)
        ·
          refine ⟨11933914442331656596062131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7955942961554437730708087 11933914442331656596062131)
          ·
            refine ⟨17900871663497484894093197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11933914442331656596062131 17900871663497484894093197)
            ·
              refine ⟨6712826873811556835284949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17900871663497484894093197 6712826873811556835284949)
              ·
                refine ⟨157331879854958363326991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6712826873811556835284949 157331879854958363326991)
                ·
                  rfl

theorem cell22_4136437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 7].length) (baseStart_4136437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4136437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4136437 prefixEnd_4136437 := by exact prefixLift 4136437
  have htrace : WordTrace (prefixWord ++ tailWord_4136437) baseStart_4136437 baseEnd_4136437 := by
    simpa [prefixWord, tailWord_4136437, baseEnd_4136437] using wordTrace_append hprefix tailTrace_4136437
  have hstable : (prefixWord ++ tailWord_4136437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136437).length < 2 ^ (prefixWord ++ tailWord_4136437).sum := by decide
  have hdescent : baseEnd_4136437 < baseStart_4136437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136469 : List Nat := [1, 3, 2, 1, 3, 2, 1, 5, 1, 3]
def baseStart_4136469 : Nat := 118140960795 + 4136469 * 2 ^ 59
def prefixEnd_4136469 : Nat := 4983230072969 + 3 ^ 40 * 4136469 * 2
def baseEnd_4136469 : Nat := 1415997872948587853142821

theorem tailTrace_4136469 : CollatzResearch.WordTrace tailWord_4136469 prefixEnd_4136469 1415997872948587853142821 := by
  unfold tailWord_4136469
  simp only [CollatzResearch.WordTrace]
  refine ⟨150869418851286740506740461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100579612567524493671160307 150869418851286740506740461)
  ·
    refine ⟨56576032069232527690027673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150869418851286740506740461 56576032069232527690027673)
    ·
      refine ⟨42432024051924395767520755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56576032069232527690027673 42432024051924395767520755)
      ·
        refine ⟨63648036077886593651281133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42432024051924395767520755 63648036077886593651281133)
        ·
          refine ⟨23868013529207472619230425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63648036077886593651281133 23868013529207472619230425)
          ·
            refine ⟨17901010146905604464422819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23868013529207472619230425 17901010146905604464422819)
            ·
              refine ⟨26851515220358406696634229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17901010146905604464422819 26851515220358406696634229)
              ·
                refine ⟨2517329551908600627809459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26851515220358406696634229 2517329551908600627809459)
                ·
                  refine ⟨3775994327862900941714189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2517329551908600627809459 3775994327862900941714189)
                  ·
                    refine ⟨1415997872948587853142821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3775994327862900941714189 1415997872948587853142821)
                    ·
                      rfl

theorem cell22_4136469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_4136469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4136469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4136469 prefixEnd_4136469 := by exact prefixLift 4136469
  have htrace : WordTrace (prefixWord ++ tailWord_4136469) baseStart_4136469 baseEnd_4136469 := by
    simpa [prefixWord, tailWord_4136469, baseEnd_4136469] using wordTrace_append hprefix tailTrace_4136469
  have hstable : (prefixWord ++ tailWord_4136469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136469).length < 2 ^ (prefixWord ++ tailWord_4136469).sum := by decide
  have hdescent : baseEnd_4136469 < baseStart_4136469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136482 : List Nat := [3, 3, 1, 1, 1, 1, 5, 2, 5]
def baseStart_4136482 : Nat := 118140960795 + 4136482 * 2 ^ 59
def prefixEnd_4136482 : Nat := 4983230072969 + 3 ^ 40 * 4136482 * 2
def baseEnd_4136482 : Nat := 472000774371420050855927

theorem tailTrace_4136482 : CollatzResearch.WordTrace tailWord_4136482 prefixEnd_4136482 472000774371420050855927 := by
  unfold tailWord_4136482
  simp only [CollatzResearch.WordTrace]
  refine ⟨37717473250059910931740925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100579928666826429151309133 37717473250059910931740925)
  ·
    refine ⟨14144052468772466599402847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37717473250059910931740925 14144052468772466599402847)
    ·
      refine ⟨21216078703158699899104271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14144052468772466599402847 21216078703158699899104271)
      ·
        refine ⟨31824118054738049848656407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21216078703158699899104271 31824118054738049848656407)
        ·
          refine ⟨47736177082107074772984611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31824118054738049848656407 47736177082107074772984611)
          ·
            refine ⟨71604265623160612159476917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47736177082107074772984611 71604265623160612159476917)
            ·
              refine ⟨6712899902171307389950961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71604265623160612159476917 6712899902171307389950961)
              ·
                refine ⟨5034674926628480542463221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6712899902171307389950961 5034674926628480542463221)
                ·
                  refine ⟨472000774371420050855927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5034674926628480542463221 472000774371420050855927)
                  ·
                    rfl

theorem cell22_4136482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_4136482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4136482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4136482 prefixEnd_4136482 := by exact prefixLift 4136482
  have htrace : WordTrace (prefixWord ++ tailWord_4136482) baseStart_4136482 baseEnd_4136482 := by
    simpa [prefixWord, tailWord_4136482, baseEnd_4136482] using wordTrace_append hprefix tailTrace_4136482
  have hstable : (prefixWord ++ tailWord_4136482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136482).length < 2 ^ (prefixWord ++ tailWord_4136482).sum := by decide
  have hdescent : baseEnd_4136482 < baseStart_4136482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136638 : List Nat := [4, 2, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_4136638 : Nat := 118140960795 + 4136638 * 2 ^ 59
def prefixEnd_4136638 : Nat := 4983230072969 + 3 ^ 40 * 4136638 * 2
def baseEnd_4136638 : Nat := 1416055725102327745667303

theorem tailTrace_4136638 : CollatzResearch.WordTrace tailWord_4136638 prefixEnd_4136638 1416055725102327745667303 := by
  unfold tailWord_4136638
  simp only [CollatzResearch.WordTrace]
  refine ⟨18859447848459310296205321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100583721858449654913095045 18859447848459310296205321)
  ·
    refine ⟨14144585886344482722153991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18859447848459310296205321 14144585886344482722153991)
    ·
      refine ⟨21216878829516724083230987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14144585886344482722153991 21216878829516724083230987)
      ·
        refine ⟨31825318244275086124846481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21216878829516724083230987 31825318244275086124846481)
        ·
          refine ⟨23868988683206314593634861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31825318244275086124846481 23868988683206314593634861)
          ·
            refine ⟨8950870756202367972613073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23868988683206314593634861 8950870756202367972613073)
            ·
              refine ⟨6713153067151775979459805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8950870756202367972613073 6713153067151775979459805)
              ·
                refine ⟨2517432400181915992297427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6713153067151775979459805 2517432400181915992297427)
                ·
                  refine ⟨3776148600272873988446141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2517432400181915992297427 3776148600272873988446141)
                  ·
                    refine ⟨1416055725102327745667303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3776148600272873988446141 1416055725102327745667303)
                    ·
                      rfl

theorem cell22_4136638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_4136638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4136638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4136638 prefixEnd_4136638 := by exact prefixLift 4136638
  have htrace : WordTrace (prefixWord ++ tailWord_4136638) baseStart_4136638 baseEnd_4136638 := by
    simpa [prefixWord, tailWord_4136638, baseEnd_4136638] using wordTrace_append hprefix tailTrace_4136638
  have hstable : (prefixWord ++ tailWord_4136638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136638).length < 2 ^ (prefixWord ++ tailWord_4136638).sum := by decide
  have hdescent : baseEnd_4136638 < baseStart_4136638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136668 : List Nat := [2, 2, 5, 1, 2, 1, 3, 1, 5]
def baseStart_4136668 : Nat := 118140960795 + 4136668 * 2 ^ 59
def prefixEnd_4136668 : Nat := 4983230072969 + 3 ^ 40 * 4136668 * 2
def baseEnd_4136668 : Nat := 472021998238472555805737

theorem tailTrace_4136668 : CollatzResearch.WordTrace tailWord_4136668 prefixEnd_4136668 472021998238472555805737 := by
  unfold tailWord_4136668
  simp only [CollatzResearch.WordTrace]
  refine ⟨75438338488782898746617329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100584451318377198328823105 75438338488782898746617329)
  ·
    refine ⟨56578753866587174059962997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75438338488782898746617329 56578753866587174059962997)
    ·
      refine ⟨5304258174992547568121531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56578753866587174059962997 5304258174992547568121531)
      ·
        refine ⟨7956387262488821352182297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5304258174992547568121531 7956387262488821352182297)
        ·
          refine ⟨5967290446866616014136723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7956387262488821352182297 5967290446866616014136723)
          ·
            refine ⟨8950935670299924021205085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5967290446866616014136723 8950935670299924021205085)
            ·
              refine ⟨3356600876362471507951907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8950935670299924021205085 3356600876362471507951907)
              ·
                refine ⟨5034901314543707261927861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3356600876362471507951907 5034901314543707261927861)
                ·
                  refine ⟨472021998238472555805737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5034901314543707261927861 472021998238472555805737)
                  ·
                    rfl

theorem cell22_4136668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_4136668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4136668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4136668 prefixEnd_4136668 := by exact prefixLift 4136668
  have htrace : WordTrace (prefixWord ++ tailWord_4136668) baseStart_4136668 baseEnd_4136668 := by
    simpa [prefixWord, tailWord_4136668, baseEnd_4136668] using wordTrace_append hprefix tailTrace_4136668
  have hstable : (prefixWord ++ tailWord_4136668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136668).length < 2 ^ (prefixWord ++ tailWord_4136668).sum := by decide
  have hdescent : baseEnd_4136668 < baseStart_4136668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136739 : List Nat := [1, 1, 1, 4, 2, 1, 2, 4, 3, 3]
def baseStart_4136739 : Nat := 118140960795 + 4136739 * 2 ^ 59
def prefixEnd_4136739 : Nat := 4983230072969 + 3 ^ 40 * 4136739 * 2
def baseEnd_4136739 : Nat := 1416090299466397148891993

theorem tailTrace_4136739 : CollatzResearch.WordTrace tailWord_4136739 prefixEnd_4136739 1416090299466397148891993 := by
  unfold tailWord_4136739
  simp only [CollatzResearch.WordTrace]
  refine ⟨150879266560308576619069271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100586177706872384412712847 150879266560308576619069271)
  ·
    refine ⟨226318899840462864928603907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150879266560308576619069271 226318899840462864928603907)
    ·
      refine ⟨339478349760694297392905861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226318899840462864928603907 339478349760694297392905861)
      ·
        refine ⟨63652190580130180761169849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339478349760694297392905861 63652190580130180761169849)
        ·
          refine ⟨47739142935097635570877387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63652190580130180761169849 47739142935097635570877387)
          ·
            refine ⟨71608714402646453356316081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47739142935097635570877387 71608714402646453356316081)
            ·
              refine ⟨53706535801984840017237061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71608714402646453356316081 53706535801984840017237061)
              ·
                refine ⟨10069975462872157503231949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53706535801984840017237061 10069975462872157503231949)
                ·
                  refine ⟨3776240798577059063711981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10069975462872157503231949 3776240798577059063711981)
                  ·
                    refine ⟨1416090299466397148891993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3776240798577059063711981 1416090299466397148891993)
                    ·
                      rfl

theorem cell22_4136739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 3].length) (baseStart_4136739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4136739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4136739 prefixEnd_4136739 := by exact prefixLift 4136739
  have htrace : WordTrace (prefixWord ++ tailWord_4136739) baseStart_4136739 baseEnd_4136739 := by
    simpa [prefixWord, tailWord_4136739, baseEnd_4136739] using wordTrace_append hprefix tailTrace_4136739
  have hstable : (prefixWord ++ tailWord_4136739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136739).length < 2 ^ (prefixWord ++ tailWord_4136739).sum := by decide
  have hdescent : baseEnd_4136739 < baseStart_4136739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136799 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 3, 4]
def baseStart_4136799 : Nat := 118140960795 + 4136799 * 2 ^ 59
def prefixEnd_4136799 : Nat := 4983230072969 + 3 ^ 40 * 4136799 * 2
def baseEnd_4136799 : Nat := 1416110838692576992391809

theorem tailTrace_4136799 : CollatzResearch.WordTrace tailWord_4136799 prefixEnd_4136799 1416110838692576992391809 := by
  unfold tailWord_4136799
  simp only [CollatzResearch.WordTrace]
  refine ⟨150881454940091206866253451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100587636626727471244168967 150881454940091206866253451)
  ·
    refine ⟨226322182410136810299380177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150881454940091206866253451 226322182410136810299380177)
    ·
      refine ⟨169741636807602607724535133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226322182410136810299380177 169741636807602607724535133)
      ·
        refine ⟨63653113802850977896700675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169741636807602607724535133 63653113802850977896700675)
        ·
          refine ⟨95479670704276466845051013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63653113802850977896700675 95479670704276466845051013)
          ·
            refine ⟨17902438257051837533447065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95479670704276466845051013 17902438257051837533447065)
            ·
              refine ⟨13426828692788878150085299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17902438257051837533447065 13426828692788878150085299)
              ·
                refine ⟨20140243039183317225127949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13426828692788878150085299 20140243039183317225127949)
                ·
                  refine ⟨7552591139693743959422981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20140243039183317225127949 7552591139693743959422981)
                  ·
                    refine ⟨1416110838692576992391809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7552591139693743959422981 1416110838692576992391809)
                    ·
                      rfl

theorem cell22_4136799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_4136799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4136799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4136799 prefixEnd_4136799 := by exact prefixLift 4136799
  have htrace : WordTrace (prefixWord ++ tailWord_4136799) baseStart_4136799 baseEnd_4136799 := by
    simpa [prefixWord, tailWord_4136799, baseEnd_4136799] using wordTrace_append hprefix tailTrace_4136799
  have hstable : (prefixWord ++ tailWord_4136799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136799).length < 2 ^ (prefixWord ++ tailWord_4136799).sum := by decide
  have hdescent : baseEnd_4136799 < baseStart_4136799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136865 : List Nat := [1, 2, 3, 4, 2, 2, 1, 3, 4]
def baseStart_4136865 : Nat := 118140960795 + 4136865 * 2 ^ 59
def prefixEnd_4136865 : Nat := 4983230072969 + 3 ^ 40 * 4136865 * 2
def baseEnd_4136865 : Nat := 472044477280458273413869

theorem tailTrace_4136865 : CollatzResearch.WordTrace tailWord_4136865 prefixEnd_4136865 472044477280458273413869 := by
  unfold tailWord_4136865
  simp only [CollatzResearch.WordTrace]
  refine ⟨150883862157852100138156049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100589241438568066758770699 150883862157852100138156049)
  ·
    refine ⟨113162896618389075103617037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150883862157852100138156049 113162896618389075103617037)
    ·
      refine ⟨42436086231895903163856389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113162896618389075103617037 42436086231895903163856389)
      ·
        refine ⟨7956766168480481843223073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42436086231895903163856389 7956766168480481843223073)
        ·
          refine ⟨5967574626360361382417305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7956766168480481843223073 5967574626360361382417305)
          ·
            refine ⟨4475680969770271036812979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5967574626360361382417305 4475680969770271036812979)
            ·
              refine ⟨6713521454655406555219469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4475680969770271036812979 6713521454655406555219469)
              ·
                refine ⟨2517570545495777458207301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6713521454655406555219469 2517570545495777458207301)
                ·
                  refine ⟨472044477280458273413869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2517570545495777458207301 472044477280458273413869)
                  ·
                    rfl

theorem cell22_4136865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 4].length) (baseStart_4136865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4136865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4136865 prefixEnd_4136865 := by exact prefixLift 4136865
  have htrace : WordTrace (prefixWord ++ tailWord_4136865) baseStart_4136865 baseEnd_4136865 := by
    simpa [prefixWord, tailWord_4136865, baseEnd_4136865] using wordTrace_append hprefix tailTrace_4136865
  have hstable : (prefixWord ++ tailWord_4136865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136865).length < 2 ^ (prefixWord ++ tailWord_4136865).sum := by decide
  have hdescent : baseEnd_4136865 < baseStart_4136865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136889 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 2, 6]
def baseStart_4136889 : Nat := 118140960795 + 4136889 * 2 ^ 59
def prefixEnd_4136889 : Nat := 4983230072969 + 3 ^ 40 * 4136889 * 2
def baseEnd_4136889 : Nat := 1416141647531846757641533

theorem tailTrace_4136889 : CollatzResearch.WordTrace tailWord_4136889 prefixEnd_4136889 1416141647531846757641533 := by
  unfold tailWord_4136889
  simp only [CollatzResearch.WordTrace]
  refine ⟨150884737509765152237029721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100589825006510101491353147 150884737509765152237029721)
  ·
    refine ⟨113163553132323864177772291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150884737509765152237029721 113163553132323864177772291)
    ·
      refine ⟨169745329698485796266658437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113163553132323864177772291 169745329698485796266658437)
      ·
        refine ⟨31827249318466086799998457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169745329698485796266658437 31827249318466086799998457)
        ·
          refine ⟨23870436988849565099998843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31827249318466086799998457 23870436988849565099998843)
          ·
            refine ⟨35805655483274347649998265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23870436988849565099998843 35805655483274347649998265)
            ·
              refine ⟨26854241612455760737498699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35805655483274347649998265 26854241612455760737498699)
              ·
                refine ⟨40281362418683641106248049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26854241612455760737498699 40281362418683641106248049)
                ·
                  refine ⟨30211021814012730829686037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40281362418683641106248049 30211021814012730829686037)
                  ·
                    refine ⟨1416141647531846757641533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30211021814012730829686037 1416141647531846757641533)
                    ·
                      rfl

theorem cell22_4136889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_4136889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4136889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4136889 prefixEnd_4136889 := by exact prefixLift 4136889
  have htrace : WordTrace (prefixWord ++ tailWord_4136889) baseStart_4136889 baseEnd_4136889 := by
    simpa [prefixWord, tailWord_4136889, baseEnd_4136889] using wordTrace_append hprefix tailTrace_4136889
  have hstable : (prefixWord ++ tailWord_4136889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136889).length < 2 ^ (prefixWord ++ tailWord_4136889).sum := by decide
  have hdescent : baseEnd_4136889 < baseStart_4136889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4136942 : List Nat := [4, 1, 2, 1, 3, 1, 4, 2, 1, 3]
def baseStart_4136942 : Nat := 118140960795 + 4136942 * 2 ^ 59
def prefixEnd_4136942 : Nat := 4983230072969 + 3 ^ 40 * 4136942 * 2
def baseEnd_4136942 : Nat := 1416159790514972286066371

theorem tailTrace_4136942 : CollatzResearch.WordTrace tailWord_4136942 prefixEnd_4136942 1416159790514972286066371 := by
  unfold tailWord_4136942
  simp only [CollatzResearch.WordTrace]
  refine ⟨18860833822321642786088635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100591113719048761525806053 18860833822321642786088635)
  ·
    refine ⟨28291250733482464179132953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18860833822321642786088635 28291250733482464179132953)
    ·
      refine ⟨21218438050111848134349715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28291250733482464179132953 21218438050111848134349715)
      ·
        refine ⟨31827657075167772201524573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21218438050111848134349715 31827657075167772201524573)
        ·
          refine ⟨11935371403187914575571715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31827657075167772201524573 11935371403187914575571715)
          ·
            refine ⟨17903057104781871863357573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11935371403187914575571715 17903057104781871863357573)
            ·
              refine ⟨3356823207146600974379545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17903057104781871863357573 3356823207146600974379545)
              ·
                refine ⟨2517617405359950730784659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3356823207146600974379545 2517617405359950730784659)
                ·
                  refine ⟨3776426108039926096176989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2517617405359950730784659 3776426108039926096176989)
                  ·
                    refine ⟨1416159790514972286066371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3776426108039926096176989 1416159790514972286066371)
                    ·
                      rfl

theorem cell22_4136942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_4136942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4136942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4136942 prefixEnd_4136942 := by exact prefixLift 4136942
  have htrace : WordTrace (prefixWord ++ tailWord_4136942) baseStart_4136942 baseEnd_4136942 := by
    simpa [prefixWord, tailWord_4136942, baseEnd_4136942] using wordTrace_append hprefix tailTrace_4136942
  have hstable : (prefixWord ++ tailWord_4136942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4136942).length < 2 ^ (prefixWord ++ tailWord_4136942).sum := by decide
  have hdescent : baseEnd_4136942 < baseStart_4136942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4136942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
