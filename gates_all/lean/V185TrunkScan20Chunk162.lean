import V185TrunkScan20Chunk161

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_986073 : List Nat := [1, 2, 1, 2, 5, 2, 1, 4, 2]
def baseStart_986073 : Nat := 118140960795 + 986073 * 2 ^ 59
def prefixEnd_986073 : Nat := 4983230072969 + 3 ^ 40 * 986073 * 2
def baseEnd_986073 : Nat := 450070586152022860935679

theorem tailTrace_986073 : CollatzResearch.WordTrace tailWord_986073 prefixEnd_986073 450070586152022860935679 := by
  unfold tailWord_986073
  simp only [CollatzResearch.WordTrace]
  refine ⟨35965036956633403705874873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23976691304422269137249915 35965036956633403705874873)
  ·
    refine ⟨26973777717475052779406155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35965036956633403705874873 26973777717475052779406155)
    ·
      refine ⟨40460666576212579169109233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26973777717475052779406155 40460666576212579169109233)
      ·
        refine ⟨30345499932159434376831925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40460666576212579169109233 30345499932159434376831925)
        ·
          refine ⟨2844890618639946972827993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30345499932159434376831925 2844890618639946972827993)
          ·
            refine ⟨2133667963979960229620995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2844890618639946972827993 2133667963979960229620995)
            ·
              refine ⟨3200501945969940344431493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2133667963979960229620995 3200501945969940344431493)
              ·
                refine ⟨600094114869363814580905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3200501945969940344431493 600094114869363814580905)
                ·
                  refine ⟨450070586152022860935679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600094114869363814580905 450070586152022860935679)
                  ·
                    rfl

theorem cell20_986073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 2].length) (baseStart_986073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986073 prefixEnd_986073 := by exact prefixLift 986073
  have htrace : WordTrace (prefixWord ++ tailWord_986073) baseStart_986073 baseEnd_986073 := by
    simpa [prefixWord, tailWord_986073, baseEnd_986073] using wordTrace_append hprefix tailTrace_986073
  have hstable : (prefixWord ++ tailWord_986073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986073).length < 2 ^ (prefixWord ++ tailWord_986073).sum := by decide
  have hdescent : baseEnd_986073 < baseStart_986073 := by decide
  rcases family_descends (prefixWord ++ tailWord_986073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986084 : List Nat := [2, 3, 1, 1, 1, 1, 2, 9]
def baseStart_986084 : Nat := 118140960795 + 986084 * 2 ^ 59
def prefixEnd_986084 : Nat := 4983230072969 + 3 ^ 40 * 986084 * 2
def baseEnd_986084 : Nat := 150025202283918570522989

theorem tailTrace_986084 : CollatzResearch.WordTrace tailWord_986084 prefixEnd_986084 150025202283918570522989 := by
  unfold tailWord_986084
  simp only [CollatzResearch.WordTrace]
  refine ⟨17982719079796776292262653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23976958773062368389683537 17982719079796776292262653)
  ·
    refine ⟨6743519654923791109598495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17982719079796776292262653 6743519654923791109598495)
    ·
      refine ⟨10115279482385686664397743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6743519654923791109598495 10115279482385686664397743)
      ·
        refine ⟨15172919223578529996596615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10115279482385686664397743 15172919223578529996596615)
        ·
          refine ⟨22759378835367794994894923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15172919223578529996596615 22759378835367794994894923)
          ·
            refine ⟨34139068253051692492342385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22759378835367794994894923 34139068253051692492342385)
            ·
              refine ⟨25604301189788769369256789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34139068253051692492342385 25604301189788769369256789)
              ·
                refine ⟨150025202283918570522989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25604301189788769369256789 150025202283918570522989)
                ·
                  rfl

theorem cell20_986084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_986084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986084 prefixEnd_986084 := by exact prefixLift 986084
  have htrace : WordTrace (prefixWord ++ tailWord_986084) baseStart_986084 baseEnd_986084 := by
    simpa [prefixWord, tailWord_986084, baseEnd_986084] using wordTrace_append hprefix tailTrace_986084
  have hstable : (prefixWord ++ tailWord_986084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986084).length < 2 ^ (prefixWord ++ tailWord_986084).sum := by decide
  have hdescent : baseEnd_986084 < baseStart_986084 := by decide
  rcases family_descends (prefixWord ++ tailWord_986084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986087 : List Nat := [1, 1, 5, 2, 2, 1, 2, 3, 3]
def baseStart_986087 : Nat := 118140960795 + 986087 * 2 ^ 59
def prefixEnd_986087 : Nat := 4983230072969 + 3 ^ 40 * 986087 * 2
def baseEnd_986087 : Nat := 450076976133501034468955

theorem tailTrace_986087 : CollatzResearch.WordTrace tailWord_986087 prefixEnd_986087 450076976133501034468955 := by
  unfold tailWord_986087
  simp only [CollatzResearch.WordTrace]
  refine ⟨35965547578582684096884515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23977031719055122731256343 35965547578582684096884515)
  ·
    refine ⟨53948321367874026145326773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35965547578582684096884515 53948321367874026145326773)
    ·
      refine ⟨5057655128238189951124385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53948321367874026145326773 5057655128238189951124385)
      ·
        refine ⟨3793241346178642463343289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5057655128238189951124385 3793241346178642463343289)
        ·
          refine ⟨2844931009633981847507467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3793241346178642463343289 2844931009633981847507467)
          ·
            refine ⟨4267396514450972771261201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2844931009633981847507467 4267396514450972771261201)
            ·
              refine ⟨3200547385838229578445901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4267396514450972771261201 3200547385838229578445901)
              ·
                refine ⟨1200205269689336091917213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3200547385838229578445901 1200205269689336091917213)
                ·
                  refine ⟨450076976133501034468955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1200205269689336091917213 450076976133501034468955)
                  ·
                    rfl

theorem cell20_986087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 3].length) (baseStart_986087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986087 prefixEnd_986087 := by exact prefixLift 986087
  have htrace : WordTrace (prefixWord ++ tailWord_986087) baseStart_986087 baseEnd_986087 := by
    simpa [prefixWord, tailWord_986087, baseEnd_986087] using wordTrace_append hprefix tailTrace_986087
  have hstable : (prefixWord ++ tailWord_986087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986087).length < 2 ^ (prefixWord ++ tailWord_986087).sum := by decide
  have hdescent : baseEnd_986087 < baseStart_986087 := by decide
  rcases family_descends (prefixWord ++ tailWord_986087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986091 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 9]
def baseStart_986091 : Nat := 118140960795 + 986091 * 2 ^ 59
def prefixEnd_986091 : Nat := 4983230072969 + 3 ^ 40 * 986091 * 2
def baseEnd_986091 : Nat := 450078801842494798335605

theorem tailTrace_986091 : CollatzResearch.WordTrace tailWord_986091 prefixEnd_986091 450078801842494798335605 := by
  unfold tailWord_986091
  simp only [CollatzResearch.WordTrace]
  refine ⟨35965693470568192780030127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23977128980378795186686751 35965693470568192780030127)
  ·
    refine ⟨53948540205852289170045191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35965693470568192780030127 53948540205852289170045191)
    ·
      refine ⟨80922810308778433755067787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53948540205852289170045191 80922810308778433755067787)
      ·
        refine ⟨121384215463167650632601681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80922810308778433755067787 121384215463167650632601681)
        ·
          refine ⟨91038161597375737974451261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121384215463167650632601681 91038161597375737974451261)
          ·
            refine ⟨34139310599015901740419223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91038161597375737974451261 34139310599015901740419223)
            ·
              refine ⟨51208965898523852610628835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34139310599015901740419223 51208965898523852610628835)
              ·
                refine ⟨76813448847785778915943253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51208965898523852610628835 76813448847785778915943253)
                ·
                  refine ⟨450078801842494798335605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76813448847785778915943253 450078801842494798335605)
                  ·
                    rfl

theorem cell20_986091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_986091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986091 prefixEnd_986091 := by exact prefixLift 986091
  have htrace : WordTrace (prefixWord ++ tailWord_986091) baseStart_986091 baseEnd_986091 := by
    simpa [prefixWord, tailWord_986091, baseEnd_986091] using wordTrace_append hprefix tailTrace_986091
  have hstable : (prefixWord ++ tailWord_986091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986091).length < 2 ^ (prefixWord ++ tailWord_986091).sum := by decide
  have hdescent : baseEnd_986091 < baseStart_986091 := by decide
  rcases family_descends (prefixWord ++ tailWord_986091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986160 : List Nat := [2, 1, 1, 1, 2, 4, 3, 6]
def baseStart_986160 : Nat := 118140960795 + 986160 * 2 ^ 59
def prefixEnd_986160 : Nat := 4983230072969 + 3 ^ 40 * 986160 * 2
def baseEnd_986160 : Nat := 150036765107545741678441

theorem tailTrace_986160 : CollatzResearch.WordTrace tailWord_986160 prefixEnd_986160 150036765107545741678441 := by
  unfold tailWord_986160
  simp only [CollatzResearch.WordTrace]
  refine ⟨17984105053659108782145967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23978806738212145042861289 17984105053659108782145967)
  ·
    refine ⟨26976157580488663173218951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17984105053659108782145967 26976157580488663173218951)
    ·
      refine ⟨40464236370732994759828427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26976157580488663173218951 40464236370732994759828427)
      ·
        refine ⟨60696354556099492139742641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40464236370732994759828427 60696354556099492139742641)
        ·
          refine ⟨45522265917074619104806981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60696354556099492139742641 45522265917074619104806981)
          ·
            refine ⟨8535424859451491082151309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45522265917074619104806981 8535424859451491082151309)
            ·
              refine ⟨3200784322294309155806741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8535424859451491082151309 3200784322294309155806741)
              ·
                refine ⟨150036765107545741678441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3200784322294309155806741 150036765107545741678441)
                ·
                  rfl

theorem cell20_986160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_986160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986160 prefixEnd_986160 := by exact prefixLift 986160
  have htrace : WordTrace (prefixWord ++ tailWord_986160) baseStart_986160 baseEnd_986160 := by
    simpa [prefixWord, tailWord_986160, baseEnd_986160] using wordTrace_append hprefix tailTrace_986160
  have hstable : (prefixWord ++ tailWord_986160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986160).length < 2 ^ (prefixWord ++ tailWord_986160).sum := by decide
  have hdescent : baseEnd_986160 < baseStart_986160 := by decide
  rcases family_descends (prefixWord ++ tailWord_986160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986166 : List Nat := [5, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_986166 : Nat := 118140960795 + 986166 * 2 ^ 59
def prefixEnd_986166 : Nat := 4983230072969 + 3 ^ 40 * 986166 * 2
def baseEnd_986166 : Nat := 450113033886127870835299

theorem tailTrace_986166 : CollatzResearch.WordTrace tailWord_986166 prefixEnd_986166 450113033886127870835299 := by
  unfold tailWord_986166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2248026809081030036813147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23978952630197653726006901 2248026809081030036813147)
  ·
    refine ⟨3372040213621545055219721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2248026809081030036813147 3372040213621545055219721)
    ·
      refine ⟨2529030160216158791414791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3372040213621545055219721 2529030160216158791414791)
      ·
        refine ⟨3793545240324238187122187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2529030160216158791414791 3793545240324238187122187)
        ·
          refine ⟨5690317860486357280683281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3793545240324238187122187 5690317860486357280683281)
          ·
            refine ⟨4267738395364767960512461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5690317860486357280683281 4267738395364767960512461)
            ·
              refine ⟨1600401898261787985192173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4267738395364767960512461 1600401898261787985192173)
              ·
                refine ⟨600150711848170494447065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1600401898261787985192173 600150711848170494447065)
                ·
                  refine ⟨450113033886127870835299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600150711848170494447065 450113033886127870835299)
                  ·
                    rfl

theorem cell20_986166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_986166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986166 prefixEnd_986166 := by exact prefixLift 986166
  have htrace : WordTrace (prefixWord ++ tailWord_986166) baseStart_986166 baseEnd_986166 := by
    simpa [prefixWord, tailWord_986166, baseEnd_986166] using wordTrace_append hprefix tailTrace_986166
  have hstable : (prefixWord ++ tailWord_986166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986166).length < 2 ^ (prefixWord ++ tailWord_986166).sum := by decide
  have hdescent : baseEnd_986166 < baseStart_986166 := by decide
  rcases family_descends (prefixWord ++ tailWord_986166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986184 : List Nat := [2, 1, 3, 1, 1, 1, 4, 4, 3]
def baseStart_986184 : Nat := 118140960795 + 986184 * 2 ^ 59
def prefixEnd_986184 : Nat := 4983230072969 + 3 ^ 40 * 986184 * 2
def baseEnd_986184 : Nat := 450121249576599808235225

theorem tailTrace_986184 : CollatzResearch.WordTrace tailWord_986184 prefixEnd_986184 450121249576599808235225 := by
  unfold tailWord_986184
  simp only [CollatzResearch.WordTrace]
  refine ⟨17984542729615634831582803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23979390306154179775443737 17984542729615634831582803)
  ·
    refine ⟨26976814094423452247374205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17984542729615634831582803 26976814094423452247374205)
    ·
      refine ⟨10116305285408794592765327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26976814094423452247374205 10116305285408794592765327)
      ·
        refine ⟨15174457928113191889147991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10116305285408794592765327 15174457928113191889147991)
        ·
          refine ⟨22761686892169787833721987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15174457928113191889147991 22761686892169787833721987)
          ·
            refine ⟨34142530338254681750582981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22761686892169787833721987 34142530338254681750582981)
            ·
              refine ⟨6401724438422752828234309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34142530338254681750582981 6401724438422752828234309)
              ·
                refine ⟨1200323332204266155293933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6401724438422752828234309 1200323332204266155293933)
                ·
                  refine ⟨450121249576599808235225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1200323332204266155293933 450121249576599808235225)
                  ·
                    rfl

theorem cell20_986184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_986184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986184 prefixEnd_986184 := by exact prefixLift 986184
  have htrace : WordTrace (prefixWord ++ tailWord_986184) baseStart_986184 baseEnd_986184 := by
    simpa [prefixWord, tailWord_986184, baseEnd_986184] using wordTrace_append hprefix tailTrace_986184
  have hstable : (prefixWord ++ tailWord_986184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986184).length < 2 ^ (prefixWord ++ tailWord_986184).sum := by decide
  have hdescent : baseEnd_986184 < baseStart_986184 := by decide
  rcases family_descends (prefixWord ++ tailWord_986184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986238 : List Nat := [4, 2, 4, 1, 1, 1, 1, 4, 2]
def baseStart_986238 : Nat := 118140960795 + 986238 * 2 ^ 59
def prefixEnd_986238 : Nat := 4983230072969 + 3 ^ 40 * 986238 * 2
def baseEnd_986238 : Nat := 450145896648015620435005

theorem tailTrace_986238 : CollatzResearch.WordTrace tailWord_986238 prefixEnd_986238 450145896648015620435005 := by
  unfold tailWord_986238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4496381875129454610703921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23980703334023757923754245 4496381875129454610703921)
  ·
    refine ⟨3372286406347090958027941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4496381875129454610703921 3372286406347090958027941)
    ·
      refine ⟨632303701190079554630239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3372286406347090958027941 632303701190079554630239)
      ·
        refine ⟨948455551785119331945359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632303701190079554630239 948455551785119331945359)
        ·
          refine ⟨1422683327677678997918039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948455551785119331945359 1422683327677678997918039)
          ·
            refine ⟨2134024991516518496877059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422683327677678997918039 2134024991516518496877059)
            ·
              refine ⟨3201037487274777745315589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134024991516518496877059 3201037487274777745315589)
              ·
                refine ⟨600194528864020827246673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3201037487274777745315589 600194528864020827246673)
                ·
                  refine ⟨450145896648015620435005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600194528864020827246673 450145896648015620435005)
                  ·
                    rfl

theorem cell20_986238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_986238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986238 prefixEnd_986238 := by exact prefixLift 986238
  have htrace : WordTrace (prefixWord ++ tailWord_986238) baseStart_986238 baseEnd_986238 := by
    simpa [prefixWord, tailWord_986238, baseEnd_986238] using wordTrace_append hprefix tailTrace_986238
  have hstable : (prefixWord ++ tailWord_986238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986238).length < 2 ^ (prefixWord ++ tailWord_986238).sum := by decide
  have hdescent : baseEnd_986238 < baseStart_986238 := by decide
  rcases family_descends (prefixWord ++ tailWord_986238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986350 : List Nat := [4, 1, 2, 1, 1, 1, 10]
def baseStart_986350 : Nat := 118140960795 + 986350 * 2 ^ 59
def prefixEnd_986350 : Nat := 4983230072969 + 3 ^ 40 * 986350 * 2
def baseEnd_986350 : Nat := 50021890722204556522357

theorem tailTrace_986350 : CollatzResearch.WordTrace tailWord_986350 prefixEnd_986350 50021890722204556522357 := by
  unfold tailWord_986350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4496892497078735001713563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23983426651086586675805669 4496892497078735001713563)
  ·
    refine ⟨6745338745618102502570345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4496892497078735001713563 6745338745618102502570345)
    ·
      refine ⟨5059004059213576876927759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6745338745618102502570345 5059004059213576876927759)
      ·
        refine ⟨7588506088820365315391639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5059004059213576876927759 7588506088820365315391639)
        ·
          refine ⟨11382759133230547973087459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7588506088820365315391639 11382759133230547973087459)
          ·
            refine ⟨17074138699845821959631189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11382759133230547973087459 17074138699845821959631189)
            ·
              refine ⟨50021890722204556522357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17074138699845821959631189 50021890722204556522357)
              ·
                rfl

theorem cell20_986350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 10].length) (baseStart_986350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986350 prefixEnd_986350 := by exact prefixLift 986350
  have htrace : WordTrace (prefixWord ++ tailWord_986350) baseStart_986350 baseEnd_986350 := by
    simpa [prefixWord, tailWord_986350, baseEnd_986350] using wordTrace_append hprefix tailTrace_986350
  have hstable : (prefixWord ++ tailWord_986350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986350).length < 2 ^ (prefixWord ++ tailWord_986350).sum := by decide
  have hdescent : baseEnd_986350 < baseStart_986350 := by decide
  rcases family_descends (prefixWord ++ tailWord_986350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986370 : List Nat := [3, 4, 1, 1, 3, 1, 1, 3, 3]
def baseStart_986370 : Nat := 118140960795 + 986370 * 2 ^ 59
def prefixEnd_986370 : Nat := 4983230072969 + 3 ^ 40 * 986370 * 2
def baseEnd_986370 : Nat := 450206145044809828034465

theorem tailTrace_986370 : CollatzResearch.WordTrace tailWord_986370 prefixEnd_986370 450206145044809828034465 := by
  unfold tailWord_986370
  simp only [CollatzResearch.WordTrace]
  refine ⟨8993967359139355857359141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23983912957704948952957709 8993967359139355857359141)
  ·
    refine ⟨1686368879838629223254839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8993967359139355857359141 1686368879838629223254839)
    ·
      refine ⟨2529553319757943834882259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1686368879838629223254839 2529553319757943834882259)
      ·
        refine ⟨3794329979636915752323389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2529553319757943834882259 3794329979636915752323389)
        ·
          refine ⟨1422873742363843407121271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3794329979636915752323389 1422873742363843407121271)
          ·
            refine ⟨2134310613545765110681907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422873742363843407121271 2134310613545765110681907)
            ·
              refine ⟨3201465920318647666022861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134310613545765110681907 3201465920318647666022861)
              ·
                refine ⟨1200549720119492874758573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3201465920318647666022861 1200549720119492874758573)
                ·
                  refine ⟨450206145044809828034465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1200549720119492874758573 450206145044809828034465)
                  ·
                    rfl

theorem cell20_986370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_986370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986370 prefixEnd_986370 := by exact prefixLift 986370
  have htrace : WordTrace (prefixWord ++ tailWord_986370) baseStart_986370 baseEnd_986370 := by
    simpa [prefixWord, tailWord_986370, baseEnd_986370] using wordTrace_append hprefix tailTrace_986370
  have hstable : (prefixWord ++ tailWord_986370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986370).length < 2 ^ (prefixWord ++ tailWord_986370).sum := by decide
  have hdescent : baseEnd_986370 < baseStart_986370 := by decide
  rcases family_descends (prefixWord ++ tailWord_986370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986436 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 6]
def baseStart_986436 : Nat := 118140960795 + 986436 * 2 ^ 59
def prefixEnd_986436 : Nat := 4983230072969 + 3 ^ 40 * 986436 * 2
def baseEnd_986436 : Nat := 450236269243206931834195

theorem tailTrace_986436 : CollatzResearch.WordTrace tailWord_986436 prefixEnd_986436 450236269243206931834195 := by
  unfold tailWord_986436
  simp only [CollatzResearch.WordTrace]
  refine ⟨17989138327159158350669581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23985517769545544467559441 17989138327159158350669581)
  ·
    refine ⟨6745926872684684381501093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17989138327159158350669581 6745926872684684381501093)
    ·
      refine ⟨1264861288628378321531455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6745926872684684381501093 1264861288628378321531455)
      ·
        refine ⟨1897291932942567482297183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1264861288628378321531455 1897291932942567482297183)
        ·
          refine ⟨2845937899413851223445775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897291932942567482297183 2845937899413851223445775)
          ·
            refine ⟨4268906849120776835168663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2845937899413851223445775 4268906849120776835168663)
            ·
              refine ⟨6403360273681165252752995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4268906849120776835168663 6403360273681165252752995)
              ·
                refine ⟨9605040410521747879129493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6403360273681165252752995 9605040410521747879129493)
                ·
                  refine ⟨450236269243206931834195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9605040410521747879129493 450236269243206931834195)
                  ·
                    rfl

theorem cell20_986436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_986436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986436 prefixEnd_986436 := by exact prefixLift 986436
  have htrace : WordTrace (prefixWord ++ tailWord_986436) baseStart_986436 baseEnd_986436 := by
    simpa [prefixWord, tailWord_986436, baseEnd_986436] using wordTrace_append hprefix tailTrace_986436
  have hstable : (prefixWord ++ tailWord_986436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986436).length < 2 ^ (prefixWord ++ tailWord_986436).sum := by decide
  have hdescent : baseEnd_986436 < baseStart_986436 := by decide
  rcases family_descends (prefixWord ++ tailWord_986436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986453 : List Nat := [1, 3, 2, 2, 3, 2, 2, 3, 2]
def baseStart_986453 : Nat := 118140960795 + 986453 * 2 ^ 59
def prefixEnd_986453 : Nat := 4983230072969 + 3 ^ 40 * 986453 * 2
def baseEnd_986453 : Nat := 450244028506430428267459

theorem tailTrace_986453 : CollatzResearch.WordTrace tailWord_986453 prefixEnd_986453 450244028506430428267459 := by
  unfold tailWord_986453
  simp only [CollatzResearch.WordTrace]
  refine ⟨35978896695256728604708013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23985931130171152403138675 35978896695256728604708013)
  ·
    refine ⟨13492086260721273226765505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35978896695256728604708013 13492086260721273226765505)
    ·
      refine ⟨10119064695540954920074129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13492086260721273226765505 10119064695540954920074129)
      ·
        refine ⟨7589298521655716190055597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10119064695540954920074129 7589298521655716190055597)
        ·
          refine ⟨2845986945620893571270849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7589298521655716190055597 2845986945620893571270849)
          ·
            refine ⟨2134490209215670178453137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2845986945620893571270849 2134490209215670178453137)
            ·
              refine ⟨1600867656911752633839853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2134490209215670178453137 1600867656911752633839853)
              ·
                refine ⟨600325371341907237689945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1600867656911752633839853 600325371341907237689945)
                ·
                  refine ⟨450244028506430428267459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600325371341907237689945 450244028506430428267459)
                  ·
                    rfl

theorem cell20_986453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_986453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986453 prefixEnd_986453 := by exact prefixLift 986453
  have htrace : WordTrace (prefixWord ++ tailWord_986453) baseStart_986453 baseEnd_986453 := by
    simpa [prefixWord, tailWord_986453, baseEnd_986453] using wordTrace_append hprefix tailTrace_986453
  have hstable : (prefixWord ++ tailWord_986453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986453).length < 2 ^ (prefixWord ++ tailWord_986453).sum := by decide
  have hdescent : baseEnd_986453 < baseStart_986453 := by decide
  rcases family_descends (prefixWord ++ tailWord_986453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986464 : List Nat := [2, 1, 1, 3, 4, 2, 7]
def baseStart_986464 : Nat := 118140960795 + 986464 * 2 ^ 59
def prefixEnd_986464 : Nat := 4983230072969 + 3 ^ 40 * 986464 * 2
def baseEnd_986464 : Nat := 50027672134018142100083

theorem tailTrace_986464 : CollatzResearch.WordTrace tailWord_986464 prefixEnd_986464 50027672134018142100083 := by
  unfold tailWord_986464
  simp only [CollatzResearch.WordTrace]
  refine ⟨17989648949108438741679223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23986198598811251655572297 17989648949108438741679223)
  ·
    refine ⟨26984473423662658112518835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17989648949108438741679223 26984473423662658112518835)
    ·
      refine ⟨40476710135493987168778253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26984473423662658112518835 40476710135493987168778253)
      ·
        refine ⟨15178766300810245188291845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40476710135493987168778253 15178766300810245188291845)
        ·
          refine ⟨2846018681401920972804721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15178766300810245188291845 2846018681401920972804721)
          ·
            refine ⟨2134514011051440729603541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2846018681401920972804721 2134514011051440729603541)
            ·
              refine ⟨50027672134018142100083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2134514011051440729603541 50027672134018142100083)
              ·
                rfl

theorem cell20_986464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 7].length) (baseStart_986464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986464 prefixEnd_986464 := by exact prefixLift 986464
  have htrace : WordTrace (prefixWord ++ tailWord_986464) baseStart_986464 baseEnd_986464 := by
    simpa [prefixWord, tailWord_986464, baseEnd_986464] using wordTrace_append hprefix tailTrace_986464
  have hstable : (prefixWord ++ tailWord_986464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986464).length < 2 ^ (prefixWord ++ tailWord_986464).sum := by decide
  have hdescent : baseEnd_986464 < baseStart_986464 := by decide
  rcases family_descends (prefixWord ++ tailWord_986464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986467 : List Nat := [1, 1, 1, 5, 2, 4, 1, 2, 3]
def baseStart_986467 : Nat := 118140960795 + 986467 * 2 ^ 59
def prefixEnd_986467 : Nat := 4983230072969 + 3 ^ 40 * 986467 * 2
def baseEnd_986467 : Nat := 450250418487908601800735

theorem tailTrace_986467 : CollatzResearch.WordTrace tailWord_986467 prefixEnd_986467 450250418487908601800735 := by
  unfold tailWord_986467
  simp only [CollatzResearch.WordTrace]
  refine ⟨35979407317206008995717655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23986271544804005997145103 35979407317206008995717655)
  ·
    refine ⟨53969110975809013493576483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35979407317206008995717655 53969110975809013493576483)
    ·
      refine ⟨80953666463713520240364725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53969110975809013493576483 80953666463713520240364725)
      ·
        refine ⟨7589406230973142522534193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80953666463713520240364725 7589406230973142522534193)
        ·
          refine ⟨5692054673229856891900645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7589406230973142522534193 5692054673229856891900645)
          ·
            refine ⟨1067260251230598167231371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5692054673229856891900645 1067260251230598167231371)
            ·
              refine ⟨1600890376845897250847057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067260251230598167231371 1600890376845897250847057)
              ·
                refine ⟨1200667782634422938135293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1600890376845897250847057 1200667782634422938135293)
                ·
                  refine ⟨450250418487908601800735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1200667782634422938135293 450250418487908601800735)
                  ·
                    rfl

theorem cell20_986467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 3].length) (baseStart_986467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986467 prefixEnd_986467 := by exact prefixLift 986467
  have htrace : WordTrace (prefixWord ++ tailWord_986467) baseStart_986467 baseEnd_986467 := by
    simpa [prefixWord, tailWord_986467, baseEnd_986467] using wordTrace_append hprefix tailTrace_986467
  have hstable : (prefixWord ++ tailWord_986467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986467).length < 2 ^ (prefixWord ++ tailWord_986467).sum := by decide
  have hdescent : baseEnd_986467 < baseStart_986467 := by decide
  rcases family_descends (prefixWord ++ tailWord_986467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986494 : List Nat := [4, 2, 3, 2, 1, 2, 2, 4]
def baseStart_986494 : Nat := 118140960795 + 986494 * 2 ^ 59
def prefixEnd_986494 : Nat := 4983230072969 + 3 ^ 40 * 986494 * 2
def baseEnd_986494 : Nat := 150087580674538835966875

theorem tailTrace_986494 : CollatzResearch.WordTrace tailWord_986494 prefixEnd_986494 150087580674538835966875 := by
  unfold tailWord_986494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4497549011013524075868817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23986928058738795071300357 4497549011013524075868817)
  ·
    refine ⟨3373161758260143056901613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4497549011013524075868817 3373161758260143056901613)
    ·
      refine ⟨1264935659347553646338105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3373161758260143056901613 1264935659347553646338105)
      ·
        refine ⟨948701744510665234753579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1264935659347553646338105 948701744510665234753579)
        ·
          refine ⟨1423052616765997852130369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948701744510665234753579 1423052616765997852130369)
          ·
            refine ⟨1067289462574498389097777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1423052616765997852130369 1067289462574498389097777)
            ·
              refine ⟨800467096930873791823333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1067289462574498389097777 800467096930873791823333)
              ·
                refine ⟨150087580674538835966875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 800467096930873791823333 150087580674538835966875)
                ·
                  rfl

theorem cell20_986494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_986494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986494 prefixEnd_986494 := by exact prefixLift 986494
  have htrace : WordTrace (prefixWord ++ tailWord_986494) baseStart_986494 baseEnd_986494 := by
    simpa [prefixWord, tailWord_986494, baseEnd_986494] using wordTrace_append hprefix tailTrace_986494
  have hstable : (prefixWord ++ tailWord_986494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986494).length < 2 ^ (prefixWord ++ tailWord_986494).sum := by decide
  have hdescent : baseEnd_986494 < baseStart_986494 := by decide
  rcases family_descends (prefixWord ++ tailWord_986494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986498 : List Nat := [3, 4, 2, 1, 1, 2, 1, 6]
def baseStart_986498 : Nat := 118140960795 + 986498 * 2 ^ 59
def prefixEnd_986498 : Nat := 4983230072969 + 3 ^ 40 * 986498 * 2
def baseEnd_986498 : Nat := 150088189244203423922425

theorem tailTrace_986498 : CollatzResearch.WordTrace tailWord_986498 prefixEnd_986498 150088189244203423922425 := by
  unfold tailWord_986498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8995134495023425322524037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23987025320062467526730765 8995134495023425322524037)
  ·
    refine ⟨1686587717816892247973257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8995134495023425322524037 1686587717816892247973257)
    ·
      refine ⟨1264940788362669185979943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1686587717816892247973257 1264940788362669185979943)
      ·
        refine ⟨1897411182544003778969915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1264940788362669185979943 1897411182544003778969915)
        ·
          refine ⟨2846116773816005668454873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897411182544003778969915 2846116773816005668454873)
          ·
            refine ⟨2134587580362004251341155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2846116773816005668454873 2134587580362004251341155)
            ·
              refine ⟨3201881370543006377011733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134587580362004251341155 3201881370543006377011733)
              ·
                refine ⟨150088189244203423922425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3201881370543006377011733 150088189244203423922425)
                ·
                  rfl

theorem cell20_986498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_986498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986498 prefixEnd_986498 := by exact prefixLift 986498
  have htrace : WordTrace (prefixWord ++ tailWord_986498) baseStart_986498 baseEnd_986498 := by
    simpa [prefixWord, tailWord_986498, baseEnd_986498] using wordTrace_append hprefix tailTrace_986498
  have hstable : (prefixWord ++ tailWord_986498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986498).length < 2 ^ (prefixWord ++ tailWord_986498).sum := by decide
  have hdescent : baseEnd_986498 < baseStart_986498 := by decide
  rcases family_descends (prefixWord ++ tailWord_986498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986536 : List Nat := [2, 1, 6, 1, 2, 1, 2, 5]
def baseStart_986536 : Nat := 118140960795 + 986536 * 2 ^ 59
def prefixEnd_986536 : Nat := 4983230072969 + 3 ^ 40 * 986536 * 2
def baseEnd_986536 : Nat := 150093970656017009500151

theorem tailTrace_986536 : CollatzResearch.WordTrace tailWord_986536 prefixEnd_986536 150093970656017009500151 := by
  unfold tailWord_986536
  simp only [CollatzResearch.WordTrace]
  refine ⟨17990961976978016889989731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23987949302637355853319641 17990961976978016889989731)
  ·
    refine ⟨26986442965467025334984597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17990961976978016889989731 26986442965467025334984597)
    ·
      refine ⟨1264989514006266812577403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26986442965467025334984597 1264989514006266812577403)
      ·
        refine ⟨1897484271009400218866105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1264989514006266812577403 1897484271009400218866105)
        ·
          refine ⟨1423113203257050164149579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1897484271009400218866105 1423113203257050164149579)
          ·
            refine ⟨2134669804885575246224369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423113203257050164149579 2134669804885575246224369)
            ·
              refine ⟨1601002353664181434668277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2134669804885575246224369 1601002353664181434668277)
              ·
                refine ⟨150093970656017009500151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1601002353664181434668277 150093970656017009500151)
                ·
                  rfl

theorem cell20_986536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_986536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986536 prefixEnd_986536 := by exact prefixLift 986536
  have htrace : WordTrace (prefixWord ++ tailWord_986536) baseStart_986536 baseEnd_986536 := by
    simpa [prefixWord, tailWord_986536, baseEnd_986536] using wordTrace_append hprefix tailTrace_986536
  have hstable : (prefixWord ++ tailWord_986536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986536).length < 2 ^ (prefixWord ++ tailWord_986536).sum := by decide
  have hdescent : baseEnd_986536 < baseStart_986536 := by decide
  rcases family_descends (prefixWord ++ tailWord_986536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986595 : List Nat := [1, 1, 1, 6, 2, 3, 1, 5]
def baseStart_986595 : Nat := 118140960795 + 986595 * 2 ^ 59
def prefixEnd_986595 : Nat := 4983230072969 + 3 ^ 40 * 986595 * 2
def baseEnd_986595 : Nat := 150102947058569681844515

theorem tailTrace_986595 : CollatzResearch.WordTrace tailWord_986595 prefixEnd_986595 150102947058569681844515 := by
  unfold tailWord_986595
  simp only [CollatzResearch.WordTrace]
  refine ⟨35984075860742286856377239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23989383907161524570918159 35984075860742286856377239)
  ·
    refine ⟨53976113791113430284565859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35984075860742286856377239 53976113791113430284565859)
    ·
      refine ⟨80964170686670145426848789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53976113791113430284565859 80964170686670145426848789)
      ·
        refine ⟨3795195500937663066883537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 80964170686670145426848789 3795195500937663066883537)
        ·
          refine ⟨2846396625703247300162653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3795195500937663066883537 2846396625703247300162653)
          ·
            refine ⟨1067398734638717737560995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2846396625703247300162653 1067398734638717737560995)
            ·
              refine ⟨1601098101958076606341493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067398734638717737560995 1601098101958076606341493)
              ·
                refine ⟨150102947058569681844515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1601098101958076606341493 150102947058569681844515)
                ·
                  rfl

theorem cell20_986595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 5].length) (baseStart_986595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986595 prefixEnd_986595 := by exact prefixLift 986595
  have htrace : WordTrace (prefixWord ++ tailWord_986595) baseStart_986595 baseEnd_986595 := by
    simpa [prefixWord, tailWord_986595, baseEnd_986595] using wordTrace_append hprefix tailTrace_986595
  have hstable : (prefixWord ++ tailWord_986595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986595).length < 2 ^ (prefixWord ++ tailWord_986595).sum := by decide
  have hdescent : baseEnd_986595 < baseStart_986595 := by decide
  rcases family_descends (prefixWord ++ tailWord_986595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986609 : List Nat := [1, 2, 2, 2, 3, 3, 1, 2, 4]
def baseStart_986609 : Nat := 118140960795 + 986609 * 2 ^ 59
def prefixEnd_986609 : Nat := 4983230072969 + 3 ^ 40 * 986609 * 2
def baseEnd_986609 : Nat := 450315231157187219066821

theorem tailTrace_986609 : CollatzResearch.WordTrace tailWord_986609 prefixEnd_986609 450315231157187219066821 := by
  unfold tailWord_986609
  simp only [CollatzResearch.WordTrace]
  refine ⟨35984586482691567247386881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23989724321794378164924587 35984586482691567247386881)
  ·
    refine ⟨26988439862018675435540161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35984586482691567247386881 26988439862018675435540161)
    ·
      refine ⟨20241329896514006576655121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26988439862018675435540161 20241329896514006576655121)
      ·
        refine ⟨15180997422385504932491341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20241329896514006576655121 15180997422385504932491341)
        ·
          refine ⟨5692874033394564349684253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15180997422385504932491341 5692874033394564349684253)
          ·
            refine ⟨2134827762522961631131595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5692874033394564349684253 2134827762522961631131595)
            ·
              refine ⟨3202241643784442446697393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134827762522961631131595 3202241643784442446697393)
              ·
                refine ⟨2401681232838331835023045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3202241643784442446697393 2401681232838331835023045)
                ·
                  refine ⟨450315231157187219066821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2401681232838331835023045 450315231157187219066821)
                  ·
                    rfl

theorem cell20_986609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_986609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986609 prefixEnd_986609 := by exact prefixLift 986609
  have htrace : WordTrace (prefixWord ++ tailWord_986609) baseStart_986609 baseEnd_986609 := by
    simpa [prefixWord, tailWord_986609, baseEnd_986609] using wordTrace_append hprefix tailTrace_986609
  have hstable : (prefixWord ++ tailWord_986609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986609).length < 2 ^ (prefixWord ++ tailWord_986609).sum := by decide
  have hdescent : baseEnd_986609 < baseStart_986609 := by decide
  rcases family_descends (prefixWord ++ tailWord_986609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986636 : List Nat := [2, 2, 1, 2, 6, 1, 1, 2, 3]
def baseStart_986636 : Nat := 118140960795 + 986636 * 2 ^ 59
def prefixEnd_986636 : Nat := 4983230072969 + 3 ^ 40 * 986636 * 2
def baseEnd_986636 : Nat := 450327554692895125166711

theorem tailTrace_986636 : CollatzResearch.WordTrace tailWord_986636 prefixEnd_986636 450327554692895125166711 := by
  unfold tailWord_986636
  simp only [CollatzResearch.WordTrace]
  refine ⟨17992785626796875429309881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23990380835729167239079841 17992785626796875429309881)
  ·
    refine ⟨13494589220097656571982411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17992785626796875429309881 13494589220097656571982411)
    ·
      refine ⟨20241883830146484857973617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13494589220097656571982411 20241883830146484857973617)
      ·
        refine ⟨15181412872609863643480213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20241883830146484857973617 15181412872609863643480213)
        ·
          refine ⟨711628728403587358288135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15181412872609863643480213 711628728403587358288135)
          ·
            refine ⟨1067443092605381037432203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711628728403587358288135 1067443092605381037432203)
            ·
              refine ⟨1601164638908071556148305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067443092605381037432203 1601164638908071556148305)
              ·
                refine ⟨1200873479181053667111229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1601164638908071556148305 1200873479181053667111229)
                ·
                  refine ⟨450327554692895125166711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1200873479181053667111229 450327554692895125166711)
                  ·
                    rfl

theorem cell20_986636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_986636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986636 prefixEnd_986636 := by exact prefixLift 986636
  have htrace : WordTrace (prefixWord ++ tailWord_986636) baseStart_986636 baseEnd_986636 := by
    simpa [prefixWord, tailWord_986636, baseEnd_986636] using wordTrace_append hprefix tailTrace_986636
  have hstable : (prefixWord ++ tailWord_986636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986636).length < 2 ^ (prefixWord ++ tailWord_986636).sum := by decide
  have hdescent : baseEnd_986636 < baseStart_986636 := by decide
  rcases family_descends (prefixWord ++ tailWord_986636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986657 : List Nat := [1, 2, 3, 2, 2, 3, 3, 1, 3]
def baseStart_986657 : Nat := 118140960795 + 986657 * 2 ^ 59
def prefixEnd_986657 : Nat := 4983230072969 + 3 ^ 40 * 986657 * 2
def baseEnd_986657 : Nat := 450337139665112385466625

theorem tailTrace_986657 : CollatzResearch.WordTrace tailWord_986657 prefixEnd_986657 450337139665112385466625 := by
  unfold tailWord_986657
  simp only [CollatzResearch.WordTrace]
  refine ⟨35986337186517671445134225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23990891457678447630089483 35986337186517671445134225)
  ·
    refine ⟨26989752889888253583850669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35986337186517671445134225 26989752889888253583850669)
    ·
      refine ⟨10121157333708095093944001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26989752889888253583850669 10121157333708095093944001)
      ·
        refine ⟨7590868000281071320458001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10121157333708095093944001 7590868000281071320458001)
        ·
          refine ⟨5693151000210803490343501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7590868000281071320458001 5693151000210803490343501)
          ·
            refine ⟨2134931625079051308878813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5693151000210803490343501 2134931625079051308878813)
            ·
              refine ⟨800599359404644240829555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2134931625079051308878813 800599359404644240829555)
              ·
                refine ⟨1200899039106966361244333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 800599359404644240829555 1200899039106966361244333)
                ·
                  refine ⟨450337139665112385466625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1200899039106966361244333 450337139665112385466625)
                  ·
                    rfl

theorem cell20_986657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 3].length) (baseStart_986657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986657 prefixEnd_986657 := by exact prefixLift 986657
  have htrace : WordTrace (prefixWord ++ tailWord_986657) baseStart_986657 baseEnd_986657 := by
    simpa [prefixWord, tailWord_986657, baseEnd_986657] using wordTrace_append hprefix tailTrace_986657
  have hstable : (prefixWord ++ tailWord_986657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986657).length < 2 ^ (prefixWord ++ tailWord_986657).sum := by decide
  have hdescent : baseEnd_986657 < baseStart_986657 := by decide
  rcases family_descends (prefixWord ++ tailWord_986657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986681 : List Nat := [1, 2, 1, 5, 1, 4, 1, 3, 2]
def baseStart_986681 : Nat := 118140960795 + 986681 * 2 ^ 59
def prefixEnd_986681 : Nat := 4983230072969 + 3 ^ 40 * 986681 * 2
def baseEnd_986681 : Nat := 450348093919074968666527

theorem tailTrace_986681 : CollatzResearch.WordTrace tailWord_986681 prefixEnd_986681 450348093919074968666527 := by
  unfold tailWord_986681
  simp only [CollatzResearch.WordTrace]
  refine ⟨35987212538430723544007897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23991475025620482362671931 35987212538430723544007897)
  ·
    refine ⟨26990409403823042658005923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35987212538430723544007897 26990409403823042658005923)
    ·
      refine ⟨40485614105734563987008885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26990409403823042658005923 40485614105734563987008885)
      ·
        refine ⟨3795526322412615373782083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40485614105734563987008885 3795526322412615373782083)
        ·
          refine ⟨5693289483618923060673125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3795526322412615373782083 5693289483618923060673125)
          ·
            refine ⟨1067491778178548073876211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5693289483618923060673125 1067491778178548073876211)
            ·
              refine ⟨1601237667267822110814317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067491778178548073876211 1601237667267822110814317)
              ·
                refine ⟨600464125225433291555369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1601237667267822110814317 600464125225433291555369)
                ·
                  refine ⟨450348093919074968666527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600464125225433291555369 450348093919074968666527)
                  ·
                    rfl

theorem cell20_986681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 2].length) (baseStart_986681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986681 prefixEnd_986681 := by exact prefixLift 986681
  have htrace : WordTrace (prefixWord ++ tailWord_986681) baseStart_986681 baseEnd_986681 := by
    simpa [prefixWord, tailWord_986681, baseEnd_986681] using wordTrace_append hprefix tailTrace_986681
  have hstable : (prefixWord ++ tailWord_986681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986681).length < 2 ^ (prefixWord ++ tailWord_986681).sum := by decide
  have hdescent : baseEnd_986681 < baseStart_986681 := by decide
  rcases family_descends (prefixWord ++ tailWord_986681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986699 : List Nat := [1, 1, 1, 1, 3, 1, 3, 6, 3]
def baseStart_986699 : Nat := 118140960795 + 986699 * 2 ^ 59
def prefixEnd_986699 : Nat := 4983230072969 + 3 ^ 40 * 986699 * 2
def baseEnd_986699 : Nat := 450356309609546906066453

theorem tailTrace_986699 : CollatzResearch.WordTrace tailWord_986699 prefixEnd_986699 450356309609546906066453 := by
  unfold tailWord_986699
  simp only [CollatzResearch.WordTrace]
  refine ⟨35987869052365512618163151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23991912701577008412108767 35987869052365512618163151)
  ·
    refine ⟨53981803578548268927244727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35987869052365512618163151 53981803578548268927244727)
    ·
      refine ⟨80972705367822403390867091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53981803578548268927244727 80972705367822403390867091)
      ·
        refine ⟨121459058051733605086300637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80972705367822403390867091 121459058051733605086300637)
        ·
          refine ⟨45547146769400101907362739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121459058051733605086300637 45547146769400101907362739)
          ·
            refine ⟨68320720154100152861044109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45547146769400101907362739 68320720154100152861044109)
            ·
              refine ⟨25620270057787557322891541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68320720154100152861044109 25620270057787557322891541)
              ·
                refine ⟨1200950158958791749510541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25620270057787557322891541 1200950158958791749510541)
                ·
                  refine ⟨450356309609546906066453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1200950158958791749510541 450356309609546906066453)
                  ·
                    rfl

theorem cell20_986699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 3].length) (baseStart_986699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986699 prefixEnd_986699 := by exact prefixLift 986699
  have htrace : WordTrace (prefixWord ++ tailWord_986699) baseStart_986699 baseEnd_986699 := by
    simpa [prefixWord, tailWord_986699, baseEnd_986699] using wordTrace_append hprefix tailTrace_986699
  have hstable : (prefixWord ++ tailWord_986699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986699).length < 2 ^ (prefixWord ++ tailWord_986699).sum := by decide
  have hdescent : baseEnd_986699 < baseStart_986699 := by decide
  rcases family_descends (prefixWord ++ tailWord_986699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986730 : List Nat := [3, 1, 3, 2, 1, 2, 2, 6]
def baseStart_986730 : Nat := 118140960795 + 986730 * 2 ^ 59
def prefixEnd_986730 : Nat := 4983230072969 + 3 ^ 40 * 986730 * 2
def baseEnd_986730 : Nat := 150123486284749525344331

theorem tailTrace_986730 : CollatzResearch.WordTrace tailWord_986730 prefixEnd_986730 150123486284749525344331 := by
  unfold tailWord_986730
  simp only [CollatzResearch.WordTrace]
  refine ⟨8997249928813301228135411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23992666476835469941694429 8997249928813301228135411)
  ·
    refine ⟨13495874893219951842203117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8997249928813301228135411 13495874893219951842203117)
    ·
      refine ⟨5060953084957481940826169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13495874893219951842203117 5060953084957481940826169)
      ·
        refine ⟨3795714813718111455619627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5060953084957481940826169 3795714813718111455619627)
        ·
          refine ⟨5693572220577167183429441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3795714813718111455619627 5693572220577167183429441)
          ·
            refine ⟨4270179165432875387572081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5693572220577167183429441 4270179165432875387572081)
            ·
              refine ⟨3202634374074656540679061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4270179165432875387572081 3202634374074656540679061)
              ·
                refine ⟨150123486284749525344331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3202634374074656540679061 150123486284749525344331)
                ·
                  rfl

theorem cell20_986730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_986730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986730 prefixEnd_986730 := by exact prefixLift 986730
  have htrace : WordTrace (prefixWord ++ tailWord_986730) baseStart_986730 baseEnd_986730 := by
    simpa [prefixWord, tailWord_986730, baseEnd_986730] using wordTrace_append hprefix tailTrace_986730
  have hstable : (prefixWord ++ tailWord_986730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986730).length < 2 ^ (prefixWord ++ tailWord_986730).sum := by decide
  have hdescent : baseEnd_986730 < baseStart_986730 := by decide
  rcases family_descends (prefixWord ++ tailWord_986730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986785 : List Nat := [1, 2, 3, 3, 2, 2, 3, 4]
def baseStart_986785 : Nat := 118140960795 + 986785 * 2 ^ 59
def prefixEnd_986785 : Nat := 4983230072969 + 3 ^ 40 * 986785 * 2
def baseEnd_986785 : Nat := 150131854117637609733145

theorem tailTrace_986785 : CollatzResearch.WordTrace tailWord_986785 prefixEnd_986785 150131854117637609733145 := by
  unfold tailWord_986785
  simp only [CollatzResearch.WordTrace]
  refine ⟨35991005730053949305793809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23994003820035966203862539 35991005730053949305793809)
  ·
    refine ⟨26993254297540461979345357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35991005730053949305793809 26993254297540461979345357)
    ·
      refine ⟨10122470361577673242254509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26993254297540461979345357 10122470361577673242254509)
      ·
        refine ⟨3795926385591627465845441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10122470361577673242254509 3795926385591627465845441)
        ·
          refine ⟨2846944789193720599384081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3795926385591627465845441 2846944789193720599384081)
          ·
            refine ⟨2135208591895290449538061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2846944789193720599384081 2135208591895290449538061)
            ·
              refine ⟨800703221960733918576773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2135208591895290449538061 800703221960733918576773)
              ·
                refine ⟨150131854117637609733145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 800703221960733918576773 150131854117637609733145)
                ·
                  rfl

theorem cell20_986785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 4].length) (baseStart_986785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986785 prefixEnd_986785 := by exact prefixLift 986785
  have htrace : WordTrace (prefixWord ++ tailWord_986785) baseStart_986785 baseEnd_986785 := by
    simpa [prefixWord, tailWord_986785, baseEnd_986785] using wordTrace_append hprefix tailTrace_986785
  have hstable : (prefixWord ++ tailWord_986785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986785).length < 2 ^ (prefixWord ++ tailWord_986785).sum := by decide
  have hdescent : baseEnd_986785 < baseStart_986785 := by decide
  rcases family_descends (prefixWord ++ tailWord_986785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986789 : List Nat := [1, 3, 1, 2, 1, 2, 2, 8]
def baseStart_986789 : Nat := 118140960795 + 986789 * 2 ^ 59
def prefixEnd_986789 : Nat := 4983230072969 + 3 ^ 40 * 986789 * 2
def baseEnd_986789 : Nat := 150132462687302197688695

theorem tailTrace_986789 : CollatzResearch.WordTrace tailWord_986789 prefixEnd_986789 150132462687302197688695 := by
  unfold tailWord_986789
  simp only [CollatzResearch.WordTrace]
  refine ⟨35991151622039457988939421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23994101081359638659292947 35991151622039457988939421)
  ·
    refine ⟨13496681858264796745852283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35991151622039457988939421 13496681858264796745852283)
    ·
      refine ⟨20245022787397195118778425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13496681858264796745852283 20245022787397195118778425)
      ·
        refine ⟨15183767090547896339083819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20245022787397195118778425 15183767090547896339083819)
        ·
          refine ⟨22775650635821844508625729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15183767090547896339083819 22775650635821844508625729)
          ·
            refine ⟨17081737976866383381469297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22775650635821844508625729 17081737976866383381469297)
            ·
              refine ⟨12811303482649787536101973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17081737976866383381469297 12811303482649787536101973)
              ·
                refine ⟨150132462687302197688695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12811303482649787536101973 150132462687302197688695)
                ·
                  rfl

theorem cell20_986789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 8].length) (baseStart_986789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986789 prefixEnd_986789 := by exact prefixLift 986789
  have htrace : WordTrace (prefixWord ++ tailWord_986789) baseStart_986789 baseEnd_986789 := by
    simpa [prefixWord, tailWord_986789, baseEnd_986789] using wordTrace_append hprefix tailTrace_986789
  have hstable : (prefixWord ++ tailWord_986789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986789).length < 2 ^ (prefixWord ++ tailWord_986789).sum := by decide
  have hdescent : baseEnd_986789 < baseStart_986789 := by decide
  rcases family_descends (prefixWord ++ tailWord_986789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986813 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 5]
def baseStart_986813 : Nat := 118140960795 + 986813 * 2 ^ 59
def prefixEnd_986813 : Nat := 4983230072969 + 3 ^ 40 * 986813 * 2
def baseEnd_986813 : Nat := 450408342315869176265987

theorem tailTrace_986813 : CollatzResearch.WordTrace tailWord_986813 prefixEnd_986813 450408342315869176265987 := by
  unfold tailWord_986813
  simp only [CollatzResearch.WordTrace]
  refine ⟨35992026973952510087813093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23994684649301673391875395 35992026973952510087813093)
  ·
    refine ⟨6748505057616095641464955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35992026973952510087813093 6748505057616095641464955)
    ·
      refine ⟨10122757586424143462197433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6748505057616095641464955 10122757586424143462197433)
      ·
        refine ⟨7592068189818107596648075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10122757586424143462197433 7592068189818107596648075)
        ·
          refine ⟨11388102284727161394972113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7592068189818107596648075 11388102284727161394972113)
          ·
            refine ⟨8541076713545371046229085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11388102284727161394972113 8541076713545371046229085)
            ·
              refine ⟨3202903767579514142335907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8541076713545371046229085 3202903767579514142335907)
              ·
                refine ⟨4804355651369271213503861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202903767579514142335907 4804355651369271213503861)
                ·
                  refine ⟨450408342315869176265987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4804355651369271213503861 450408342315869176265987)
                  ·
                    rfl

theorem cell20_986813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_986813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986813 prefixEnd_986813 := by exact prefixLift 986813
  have htrace : WordTrace (prefixWord ++ tailWord_986813) baseStart_986813 baseEnd_986813 := by
    simpa [prefixWord, tailWord_986813, baseEnd_986813] using wordTrace_append hprefix tailTrace_986813
  have hstable : (prefixWord ++ tailWord_986813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986813).length < 2 ^ (prefixWord ++ tailWord_986813).sum := by decide
  have hdescent : baseEnd_986813 < baseStart_986813 := by decide
  rcases family_descends (prefixWord ++ tailWord_986813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986858 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_986858 : Nat := 118140960795 + 986858 * 2 ^ 59
def prefixEnd_986858 : Nat := 4983230072969 + 3 ^ 40 * 986858 * 2
def baseEnd_986858 : Nat := 450428881542049019765803

theorem tailTrace_986858 : CollatzResearch.WordTrace tailWord_986858 prefixEnd_986858 450428881542049019765803 := by
  unfold tailWord_986858
  simp only [CollatzResearch.WordTrace]
  refine ⟨8998417064697370693300307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23995778839192988515467485 8998417064697370693300307)
  ·
    refine ⟨13497625597046056039950461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8998417064697370693300307 13497625597046056039950461)
    ·
      refine ⟨5061609598892271014981423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13497625597046056039950461 5061609598892271014981423)
      ·
        refine ⟨7592414398338406522472135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5061609598892271014981423 7592414398338406522472135)
        ·
          refine ⟨11388621597507609783708203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7592414398338406522472135 11388621597507609783708203)
          ·
            refine ⟨17082932396261414675562305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11388621597507609783708203 17082932396261414675562305)
            ·
              refine ⟨12812199297196061006671729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17082932396261414675562305 12812199297196061006671729)
              ·
                refine ⟨9609149472897045755003797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12812199297196061006671729 9609149472897045755003797)
                ·
                  refine ⟨450428881542049019765803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9609149472897045755003797 450428881542049019765803)
                  ·
                    rfl

theorem cell20_986858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_986858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986858 prefixEnd_986858 := by exact prefixLift 986858
  have htrace : WordTrace (prefixWord ++ tailWord_986858) baseStart_986858 baseEnd_986858 := by
    simpa [prefixWord, tailWord_986858, baseEnd_986858] using wordTrace_append hprefix tailTrace_986858
  have hstable : (prefixWord ++ tailWord_986858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986858).length < 2 ^ (prefixWord ++ tailWord_986858).sum := by decide
  have hdescent : baseEnd_986858 < baseStart_986858 := by decide
  rcases family_descends (prefixWord ++ tailWord_986858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986865 : List Nat := [1, 2, 2, 2, 2, 3, 8]
def baseStart_986865 : Nat := 118140960795 + 986865 * 2 ^ 59
def prefixEnd_986865 : Nat := 4983230072969 + 3 ^ 40 * 986865 * 2
def baseEnd_986865 : Nat := 50048008503643122948049

theorem tailTrace_986865 : CollatzResearch.WordTrace tailWord_986865 prefixEnd_986865 50048008503643122948049 := by
  unfold tailWord_986865
  simp only [CollatzResearch.WordTrace]
  refine ⟨35993923569764122968706049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23995949046509415312470699 35993923569764122968706049)
  ·
    refine ⟨26995442677323092226529537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35993923569764122968706049 26995442677323092226529537)
    ·
      refine ⟨20246582007992319169897153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26995442677323092226529537 20246582007992319169897153)
      ·
        refine ⟨15184936505994239377422865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20246582007992319169897153 15184936505994239377422865)
        ·
          refine ⟨11388702379495679533067149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15184936505994239377422865 11388702379495679533067149)
          ·
            refine ⟨4270763392310879824900181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11388702379495679533067149 4270763392310879824900181)
            ·
              refine ⟨50048008503643122948049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4270763392310879824900181 50048008503643122948049)
              ·
                rfl

theorem cell20_986865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 8].length) (baseStart_986865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986865 prefixEnd_986865 := by exact prefixLift 986865
  have htrace : WordTrace (prefixWord ++ tailWord_986865) baseStart_986865 baseEnd_986865 := by
    simpa [prefixWord, tailWord_986865, baseEnd_986865] using wordTrace_append hprefix tailTrace_986865
  have hstable : (prefixWord ++ tailWord_986865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986865).length < 2 ^ (prefixWord ++ tailWord_986865).sum := by decide
  have hdescent : baseEnd_986865 < baseStart_986865 := by decide
  rcases family_descends (prefixWord ++ tailWord_986865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986930 : List Nat := [3, 2, 1, 1, 3, 3, 1, 4, 2]
def baseStart_986930 : Nat := 118140960795 + 986930 * 2 ^ 59
def prefixEnd_986930 : Nat := 4983230072969 + 3 ^ 40 * 986930 * 2
def baseEnd_986930 : Nat := 450461744303936769365509

theorem tailTrace_986930 : CollatzResearch.WordTrace tailWord_986930 prefixEnd_986930 450461744303936769365509 := by
  unfold tailWord_986930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8999073578632159767455561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23997529543019092713214829 8999073578632159767455561)
  ·
    refine ⟨6749305183974119825591671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8999073578632159767455561 6749305183974119825591671)
    ·
      refine ⟨10123957775961179738387507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6749305183974119825591671 10123957775961179738387507)
      ·
        refine ⟨15185936663941769607581261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10123957775961179738387507 15185936663941769607581261)
        ·
          refine ⟨5694726248978163602842973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15185936663941769607581261 5694726248978163602842973)
          ·
            refine ⟨2135522343366811351066115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5694726248978163602842973 2135522343366811351066115)
            ·
              refine ⟨3203283515050217026599173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135522343366811351066115 3203283515050217026599173)
              ·
                refine ⟨600615659071915692487345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3203283515050217026599173 600615659071915692487345)
                ·
                  refine ⟨450461744303936769365509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600615659071915692487345 450461744303936769365509)
                  ·
                    rfl

theorem cell20_986930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_986930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_986930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_986930 prefixEnd_986930 := by exact prefixLift 986930
  have htrace : WordTrace (prefixWord ++ tailWord_986930) baseStart_986930 baseEnd_986930 := by
    simpa [prefixWord, tailWord_986930, baseEnd_986930] using wordTrace_append hprefix tailTrace_986930
  have hstable : (prefixWord ++ tailWord_986930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986930).length < 2 ^ (prefixWord ++ tailWord_986930).sum := by decide
  have hdescent : baseEnd_986930 < baseStart_986930 := by decide
  rcases family_descends (prefixWord ++ tailWord_986930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987006 : List Nat := [4, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_987006 : Nat := 118140960795 + 987006 * 2 ^ 59
def prefixEnd_987006 : Nat := 4983230072969 + 3 ^ 40 * 987006 * 2
def baseEnd_987006 : Nat := 450496432774818282831865

theorem tailTrace_987006 : CollatzResearch.WordTrace tailWord_987006 prefixEnd_987006 450496432774818282831865 := by
  unfold tailWord_987006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4499883282781663006198609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23999377508168869366392581 4499883282781663006198609)
  ·
    refine ⟨3374912462086247254648957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4499883282781663006198609 3374912462086247254648957)
    ·
      refine ⟨1265592173282342720493359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3374912462086247254648957 1265592173282342720493359)
      ·
        refine ⟨1898388259923514080740039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1265592173282342720493359 1898388259923514080740039)
        ·
          refine ⟨2847582389885271121110059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1898388259923514080740039 2847582389885271121110059)
          ·
            refine ⟨4271373584827906681665089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2847582389885271121110059 4271373584827906681665089)
            ·
              refine ⟨3203530188620930011248817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4271373584827906681665089 3203530188620930011248817)
              ·
                refine ⟨2402647641465697508436613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3203530188620930011248817 2402647641465697508436613)
                ·
                  refine ⟨450496432774818282831865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2402647641465697508436613 450496432774818282831865)
                  ·
                    rfl

theorem cell20_987006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_987006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987006 prefixEnd_987006 := by exact prefixLift 987006
  have htrace : WordTrace (prefixWord ++ tailWord_987006) baseStart_987006 baseEnd_987006 := by
    simpa [prefixWord, tailWord_987006, baseEnd_987006] using wordTrace_append hprefix tailTrace_987006
  have hstable : (prefixWord ++ tailWord_987006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987006).length < 2 ^ (prefixWord ++ tailWord_987006).sum := by decide
  have hdescent : baseEnd_987006 < baseStart_987006 := by decide
  rcases family_descends (prefixWord ++ tailWord_987006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987009 : List Nat := [1, 2, 4, 4, 2, 1, 2, 4]
def baseStart_987009 : Nat := 118140960795 + 987009 * 2 ^ 59
def prefixEnd_987009 : Nat := 4983230072969 + 3 ^ 40 * 987009 * 2
def baseEnd_987009 : Nat := 150165934018854535243951

theorem tailTrace_987009 : CollatzResearch.WordTrace tailWord_987009 prefixEnd_987009 150165934018854535243951 := by
  unfold tailWord_987009
  simp only [CollatzResearch.WordTrace]
  refine ⟨35999175681242435561948081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23999450454161623707965387 35999175681242435561948081)
  ·
    refine ⟨26999381760931826671461061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35999175681242435561948081 26999381760931826671461061)
    ·
      refine ⟨5062384080174717500898949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26999381760931826671461061 5062384080174717500898949)
      ·
        refine ⟨949197015032759531418553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5062384080174717500898949 949197015032759531418553)
        ·
          refine ⟨711897761274569648563915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 949197015032759531418553 711897761274569648563915)
          ·
            refine ⟨1067846641911854472845873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711897761274569648563915 1067846641911854472845873)
            ·
              refine ⟨800884981433890854634405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1067846641911854472845873 800884981433890854634405)
              ·
                refine ⟨150165934018854535243951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 800884981433890854634405 150165934018854535243951)
                ·
                  rfl

theorem cell20_987009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 4].length) (baseStart_987009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987009 prefixEnd_987009 := by exact prefixLift 987009
  have htrace : WordTrace (prefixWord ++ tailWord_987009) baseStart_987009 baseEnd_987009 := by
    simpa [prefixWord, tailWord_987009, baseEnd_987009] using wordTrace_append hprefix tailTrace_987009
  have hstable : (prefixWord ++ tailWord_987009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987009).length < 2 ^ (prefixWord ++ tailWord_987009).sum := by decide
  have hdescent : baseEnd_987009 < baseStart_987009 := by decide
  rcases family_descends (prefixWord ++ tailWord_987009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987017 : List Nat := [1, 2, 1, 1, 5, 1, 3, 6]
def baseStart_987017 : Nat := 118140960795 + 987017 * 2 ^ 59
def prefixEnd_987017 : Nat := 4983230072969 + 3 ^ 40 * 987017 * 2
def baseEnd_987017 : Nat := 150167151158183711155051

theorem tailTrace_987017 : CollatzResearch.WordTrace tailWord_987017 prefixEnd_987017 150167151158183711155051 := by
  unfold tailWord_987017
  simp only [CollatzResearch.WordTrace]
  refine ⟨35999467465213452928239305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23999644976808968618826203 35999467465213452928239305)
  ·
    refine ⟨26999600598910089696179479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35999467465213452928239305 26999600598910089696179479)
    ·
      refine ⟨40499400898365134544269219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26999600598910089696179479 40499400898365134544269219)
      ·
        refine ⟨60749101347547701816403829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40499400898365134544269219 60749101347547701816403829)
        ·
          refine ⟨5695228251332597045287859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60749101347547701816403829 5695228251332597045287859)
          ·
            refine ⟨8542842376998895567931789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5695228251332597045287859 8542842376998895567931789)
            ·
              refine ⟨3203565891374585837974421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8542842376998895567931789 3203565891374585837974421)
              ·
                refine ⟨150167151158183711155051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3203565891374585837974421 150167151158183711155051)
                ·
                  rfl

theorem cell20_987017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 6].length) (baseStart_987017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987017 prefixEnd_987017 := by exact prefixLift 987017
  have htrace : WordTrace (prefixWord ++ tailWord_987017) baseStart_987017 baseEnd_987017 := by
    simpa [prefixWord, tailWord_987017, baseEnd_987017] using wordTrace_append hprefix tailTrace_987017
  have hstable : (prefixWord ++ tailWord_987017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987017).length < 2 ^ (prefixWord ++ tailWord_987017).sum := by decide
  have hdescent : baseEnd_987017 < baseStart_987017 := by decide
  rcases family_descends (prefixWord ++ tailWord_987017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987024 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 5]
def baseStart_987024 : Nat := 118140960795 + 987024 * 2 ^ 59
def prefixEnd_987024 : Nat := 4983230072969 + 3 ^ 40 * 987024 * 2
def baseEnd_987024 : Nat := 450504648465290220231791

theorem tailTrace_987024 : CollatzResearch.WordTrace tailWord_987024 prefixEnd_987024 450504648465290220231791 := by
  unfold tailWord_987024
  simp only [CollatzResearch.WordTrace]
  refine ⟨17999861388094046561872063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23999815184125395415829417 17999861388094046561872063)
  ·
    refine ⟨26999792082141069842808095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17999861388094046561872063 26999792082141069842808095)
    ·
      refine ⟨40499688123211604764212143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26999792082141069842808095 40499688123211604764212143)
      ·
        refine ⟨60749532184817407146318215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40499688123211604764212143 60749532184817407146318215)
        ·
          refine ⟨91124298277226110719477323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60749532184817407146318215 91124298277226110719477323)
          ·
            refine ⟨136686447415839166079215985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91124298277226110719477323 136686447415839166079215985)
            ·
              refine ⟨102514835561879374559411989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136686447415839166079215985 102514835561879374559411989)
              ·
                refine ⟨4805382916963095682472437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102514835561879374559411989 4805382916963095682472437)
                ·
                  refine ⟨450504648465290220231791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4805382916963095682472437 450504648465290220231791)
                  ·
                    rfl

theorem cell20_987024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_987024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987024 prefixEnd_987024 := by exact prefixLift 987024
  have htrace : WordTrace (prefixWord ++ tailWord_987024) baseStart_987024 baseEnd_987024 := by
    simpa [prefixWord, tailWord_987024, baseEnd_987024] using wordTrace_append hprefix tailTrace_987024
  have hstable : (prefixWord ++ tailWord_987024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987024).length < 2 ^ (prefixWord ++ tailWord_987024).sum := by decide
  have hdescent : baseEnd_987024 < baseStart_987024 := by decide
  rcases family_descends (prefixWord ++ tailWord_987024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987034 : List Nat := [3, 1, 1, 4, 2, 3, 6]
def baseStart_987034 : Nat := 118140960795 + 987034 * 2 ^ 59
def prefixEnd_987034 : Nat := 4983230072969 + 3 ^ 40 * 987034 * 2
def baseEnd_987034 : Nat := 50056579193086069988713

theorem tailTrace_987034 : CollatzResearch.WordTrace tailWord_987034 prefixEnd_987034 50056579193086069988713 := by
  unfold tailWord_987034
  simp only [CollatzResearch.WordTrace]
  refine ⟨9000021876537966207902039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24000058337434576554405437 9000021876537966207902039)
  ·
    refine ⟨13500032814806949311853059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9000021876537966207902039 13500032814806949311853059)
    ·
      refine ⟨20250049222210423967779589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13500032814806949311853059 20250049222210423967779589)
      ·
        refine ⟨3796884229164454493958673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20250049222210423967779589 3796884229164454493958673)
        ·
          refine ⟨2847663171873340870469005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3796884229164454493958673 2847663171873340870469005)
          ·
            refine ⟨1067873689452502826425877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2847663171873340870469005 1067873689452502826425877)
            ·
              refine ⟨50056579193086069988713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1067873689452502826425877 50056579193086069988713)
              ·
                rfl

theorem cell20_987034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 6].length) (baseStart_987034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987034 prefixEnd_987034 := by exact prefixLift 987034
  have htrace : WordTrace (prefixWord ++ tailWord_987034) baseStart_987034 baseEnd_987034 := by
    simpa [prefixWord, tailWord_987034, baseEnd_987034] using wordTrace_append hprefix tailTrace_987034
  have hstable : (prefixWord ++ tailWord_987034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987034).length < 2 ^ (prefixWord ++ tailWord_987034).sum := by decide
  have hdescent : baseEnd_987034 < baseStart_987034 := by decide
  rcases family_descends (prefixWord ++ tailWord_987034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987055 : List Nat := [1, 1, 2, 1, 2, 2, 6, 5]
def baseStart_987055 : Nat := 118140960795 + 987055 * 2 ^ 59
def prefixEnd_987055 : Nat := 4983230072969 + 3 ^ 40 * 987055 * 2
def baseEnd_987055 : Nat := 150172932569997296732777

theorem tailTrace_987055 : CollatzResearch.WordTrace tailWord_987055 prefixEnd_987055 150172932569997296732777 := by
  unfold tailWord_987055
  simp only [CollatzResearch.WordTrace]
  refine ⟨36000853439075785418122619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24000568959383856945415079 36000853439075785418122619)
  ·
    refine ⟨54001280158613678127183929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36000853439075785418122619 54001280158613678127183929)
    ·
      refine ⟨40500960118960258595387947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54001280158613678127183929 40500960118960258595387947)
      ·
        refine ⟨60751440178440387893081921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40500960118960258595387947 60751440178440387893081921)
        ·
          refine ⟨45563580133830290919811441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60751440178440387893081921 45563580133830290919811441)
          ·
            refine ⟨34172685100372718189858581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45563580133830290919811441 34172685100372718189858581)
            ·
              refine ⟨1601844614079971165149621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34172685100372718189858581 1601844614079971165149621)
              ·
                refine ⟨150172932569997296732777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1601844614079971165149621 150172932569997296732777)
                ·
                  rfl

theorem cell20_987055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 5].length) (baseStart_987055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987055 prefixEnd_987055 := by exact prefixLift 987055
  have htrace : WordTrace (prefixWord ++ tailWord_987055) baseStart_987055 baseEnd_987055 := by
    simpa [prefixWord, tailWord_987055, baseEnd_987055] using wordTrace_append hprefix tailTrace_987055
  have hstable : (prefixWord ++ tailWord_987055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987055).length < 2 ^ (prefixWord ++ tailWord_987055).sum := by decide
  have hdescent : baseEnd_987055 < baseStart_987055 := by decide
  rcases family_descends (prefixWord ++ tailWord_987055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987093 : List Nat := [1, 3, 2, 3, 2, 9]
def baseStart_987093 : Nat := 118140960795 + 987093 * 2 ^ 59
def prefixEnd_987093 : Nat := 4983230072969 + 3 ^ 40 * 987093 * 2
def baseEnd_987093 : Nat := 16686523775756764701167

theorem tailTrace_987093 : CollatzResearch.WordTrace tailWord_987093 prefixEnd_987093 16686523775756764701167 := by
  unfold tailWord_987093
  simp only [CollatzResearch.WordTrace]
  refine ⟨36002239412938117908005933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24001492941958745272003955 36002239412938117908005933)
  ·
    refine ⟨13500839779851794215502225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36002239412938117908005933 13500839779851794215502225)
    ·
      refine ⟨10125629834888845661626669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13500839779851794215502225 10125629834888845661626669)
      ·
        refine ⟨3797111188083317123110001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10125629834888845661626669 3797111188083317123110001)
        ·
          refine ⟨2847833391062487842332501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3797111188083317123110001 2847833391062487842332501)
          ·
            refine ⟨16686523775756764701167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2847833391062487842332501 16686523775756764701167)
            ·
              rfl

theorem cell20_987093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 9].length) (baseStart_987093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987093 prefixEnd_987093 := by exact prefixLift 987093
  have htrace : WordTrace (prefixWord ++ tailWord_987093) baseStart_987093 baseEnd_987093 := by
    simpa [prefixWord, tailWord_987093, baseEnd_987093] using wordTrace_append hprefix tailTrace_987093
  have hstable : (prefixWord ++ tailWord_987093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987093).length < 2 ^ (prefixWord ++ tailWord_987093).sum := by decide
  have hdescent : baseEnd_987093 < baseStart_987093 := by decide
  rcases family_descends (prefixWord ++ tailWord_987093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987106 : List Nat := [3, 3, 3, 1, 2, 2, 1, 5]
def baseStart_987106 : Nat := 118140960795 + 987106 * 2 ^ 59
def prefixEnd_987106 : Nat := 4983230072969 + 3 ^ 40 * 987106 * 2
def baseEnd_987106 : Nat := 150180691833220793166041

theorem tailTrace_987106 : CollatzResearch.WordTrace tailWord_987106 prefixEnd_987106 150180691833220793166041 := by
  unfold tailWord_987106
  simp only [CollatzResearch.WordTrace]
  refine ⟨9000678390472755282057293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24001809041260680752152781 9000678390472755282057293)
  ·
    refine ⟨3375254396427283230771485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9000678390472755282057293 3375254396427283230771485)
    ·
      refine ⟨1265720398660231211539307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3375254396427283230771485 1265720398660231211539307)
      ·
        refine ⟨1898580597990346817308961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1265720398660231211539307 1898580597990346817308961)
        ·
          refine ⟨1423935448492760112981721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1898580597990346817308961 1423935448492760112981721)
          ·
            refine ⟨1067951586369570084736291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1423935448492760112981721 1067951586369570084736291)
            ·
              refine ⟨1601927379554355127104437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067951586369570084736291 1601927379554355127104437)
              ·
                refine ⟨150180691833220793166041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1601927379554355127104437 150180691833220793166041)
                ·
                  rfl

theorem cell20_987106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_987106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987106 prefixEnd_987106 := by exact prefixLift 987106
  have htrace : WordTrace (prefixWord ++ tailWord_987106) baseStart_987106 baseEnd_987106 := by
    simpa [prefixWord, tailWord_987106, baseEnd_987106] using wordTrace_append hprefix tailTrace_987106
  have hstable : (prefixWord ++ tailWord_987106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987106).length < 2 ^ (prefixWord ++ tailWord_987106).sum := by decide
  have hdescent : baseEnd_987106 < baseStart_987106 := by decide
  rcases family_descends (prefixWord ++ tailWord_987106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987141 : List Nat := [1, 3, 1, 1, 2, 4, 1, 5, 2]
def baseStart_987141 : Nat := 118140960795 + 987141 * 2 ^ 59
def prefixEnd_987141 : Nat := 4983230072969 + 3 ^ 40 * 987141 * 2
def baseEnd_987141 : Nat := 450558050453357813331313

theorem tailTrace_987141 : CollatzResearch.WordTrace tailWord_987141 prefixEnd_987141 450558050453357813331313 := by
  unfold tailWord_987141
  simp only [CollatzResearch.WordTrace]
  refine ⟨36003990116764222105753277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24002660077842814737168851 36003990116764222105753277)
  ·
    refine ⟨13501496293786583289657479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36003990116764222105753277 13501496293786583289657479)
    ·
      refine ⟨20252244440679874934486219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13501496293786583289657479 20252244440679874934486219)
      ·
        refine ⟨30378366661019812401729329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20252244440679874934486219 30378366661019812401729329)
        ·
          refine ⟨22783774995764859301296997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30378366661019812401729329 22783774995764859301296997)
          ·
            refine ⟨4271957811705911118993187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22783774995764859301296997 4271957811705911118993187)
            ·
              refine ⟨6407936717558866678489781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4271957811705911118993187 6407936717558866678489781)
              ·
                refine ⟨600744067271143751108417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6407936717558866678489781 600744067271143751108417)
                ·
                  refine ⟨450558050453357813331313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600744067271143751108417 450558050453357813331313)
                  ·
                    rfl

theorem cell20_987141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_987141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987141 prefixEnd_987141 := by exact prefixLift 987141
  have htrace : WordTrace (prefixWord ++ tailWord_987141) baseStart_987141 baseEnd_987141 := by
    simpa [prefixWord, tailWord_987141, baseEnd_987141] using wordTrace_append hprefix tailTrace_987141
  have hstable : (prefixWord ++ tailWord_987141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987141).length < 2 ^ (prefixWord ++ tailWord_987141).sum := by decide
  have hdescent : baseEnd_987141 < baseStart_987141 := by decide
  rcases family_descends (prefixWord ++ tailWord_987141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987155 : List Nat := [1, 1, 1, 2, 1, 4, 5, 2, 3]
def baseStart_987155 : Nat := 118140960795 + 987155 * 2 ^ 59
def prefixEnd_987155 : Nat := 4983230072969 + 3 ^ 40 * 987155 * 2
def baseEnd_987155 : Nat := 450564440434835986864589

theorem tailTrace_987155 : CollatzResearch.WordTrace tailWord_987155 prefixEnd_987155 450564440434835986864589 := by
  unfold tailWord_987155
  simp only [CollatzResearch.WordTrace]
  refine ⟨36004500738713502496762919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24003000492475668331175279 36004500738713502496762919)
  ·
    refine ⟨54006751108070253745144379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36004500738713502496762919 54006751108070253745144379)
    ·
      refine ⟨81010126662105380617716569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54006751108070253745144379 81010126662105380617716569)
      ·
        refine ⟨60757594996579035463287427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81010126662105380617716569 60757594996579035463287427)
        ·
          refine ⟨91136392494868553194931141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60757594996579035463287427 91136392494868553194931141)
          ·
            refine ⟨17088073592787853724049589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91136392494868553194931141 17088073592787853724049589)
            ·
              refine ⟨1602006899323861286629649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17088073592787853724049589 1602006899323861286629649)
              ·
                refine ⟨1201505174492895964972237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1602006899323861286629649 1201505174492895964972237)
                ·
                  refine ⟨450564440434835986864589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1201505174492895964972237 450564440434835986864589)
                  ·
                    rfl

theorem cell20_987155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 3].length) (baseStart_987155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987155 prefixEnd_987155 := by exact prefixLift 987155
  have htrace : WordTrace (prefixWord ++ tailWord_987155) baseStart_987155 baseEnd_987155 := by
    simpa [prefixWord, tailWord_987155, baseEnd_987155] using wordTrace_append hprefix tailTrace_987155
  have hstable : (prefixWord ++ tailWord_987155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987155).length < 2 ^ (prefixWord ++ tailWord_987155).sum := by decide
  have hdescent : baseEnd_987155 < baseStart_987155 := by decide
  rcases family_descends (prefixWord ++ tailWord_987155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987162 : List Nat := [3, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_987162 : Nat := 118140960795 + 987162 * 2 ^ 59
def prefixEnd_987162 : Nat := 4983230072969 + 3 ^ 40 * 987162 * 2
def baseEnd_987162 : Nat := 450567635425575073631227

theorem tailTrace_987162 : CollatzResearch.WordTrace tailWord_987162 prefixEnd_987162 450567635425575073631227 := by
  unfold tailWord_987162
  simp only [CollatzResearch.WordTrace]
  refine ⟨9001189012422035673066935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24003170699792095128178493 9001189012422035673066935)
  ·
    refine ⟨13501783518633053509600403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9001189012422035673066935 13501783518633053509600403)
    ·
      refine ⟨20252675277949580264400605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13501783518633053509600403 20252675277949580264400605)
      ·
        refine ⟨7594753229231092599150227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20252675277949580264400605 7594753229231092599150227)
        ·
          refine ⟨11392129843846638898725341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7594753229231092599150227 11392129843846638898725341)
          ·
            refine ⟨4272048691442489587022003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11392129843846638898725341 4272048691442489587022003)
            ·
              refine ⟨6408073037163734380533005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272048691442489587022003 6408073037163734380533005)
              ·
                refine ⟨2403027388936400392699877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6408073037163734380533005 2403027388936400392699877)
                ·
                  refine ⟨450567635425575073631227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2403027388936400392699877 450567635425575073631227)
                  ·
                    rfl

theorem cell20_987162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_987162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987162 prefixEnd_987162 := by exact prefixLift 987162
  have htrace : WordTrace (prefixWord ++ tailWord_987162) baseStart_987162 baseEnd_987162 := by
    simpa [prefixWord, tailWord_987162, baseEnd_987162] using wordTrace_append hprefix tailTrace_987162
  have hstable : (prefixWord ++ tailWord_987162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987162).length < 2 ^ (prefixWord ++ tailWord_987162).sum := by decide
  have hdescent : baseEnd_987162 < baseStart_987162 := by decide
  rcases family_descends (prefixWord ++ tailWord_987162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987183 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 6]
def baseStart_987183 : Nat := 118140960795 + 987183 * 2 ^ 59
def prefixEnd_987183 : Nat := 4983230072969 + 3 ^ 40 * 987183 * 2
def baseEnd_987183 : Nat := 450577220397792333931141

theorem tailTrace_987183 : CollatzResearch.WordTrace tailWord_987183 prefixEnd_987183 450577220397792333931141 := by
  unfold tailWord_987183
  simp only [CollatzResearch.WordTrace]
  refine ⟨36005521982612063278782203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24003681321741375519188135 36005521982612063278782203)
  ·
    refine ⟨54008282973918094918173305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36005521982612063278782203 54008282973918094918173305)
    ·
      refine ⟨40506212230438571188629979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54008282973918094918173305 40506212230438571188629979)
      ·
        refine ⟨60759318345657856782944969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40506212230438571188629979 60759318345657856782944969)
        ·
          refine ⟨45569488759243392587208727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60759318345657856782944969 45569488759243392587208727)
          ·
            refine ⟨68354233138865088880813091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45569488759243392587208727 68354233138865088880813091)
            ·
              refine ⟨102531349708297633321219637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68354233138865088880813091 102531349708297633321219637)
              ·
                refine ⟨9612314035152903123864341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102531349708297633321219637 9612314035152903123864341)
                ·
                  refine ⟨450577220397792333931141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9612314035152903123864341 450577220397792333931141)
                  ·
                    rfl

theorem cell20_987183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_987183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987183 prefixEnd_987183 := by exact prefixLift 987183
  have htrace : WordTrace (prefixWord ++ tailWord_987183) baseStart_987183 baseEnd_987183 := by
    simpa [prefixWord, tailWord_987183, baseEnd_987183] using wordTrace_append hprefix tailTrace_987183
  have hstable : (prefixWord ++ tailWord_987183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987183).length < 2 ^ (prefixWord ++ tailWord_987183).sum := by decide
  have hdescent : baseEnd_987183 < baseStart_987183 := by decide
  rcases family_descends (prefixWord ++ tailWord_987183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987186 : List Nat := [3, 2, 1, 1, 2, 3, 4, 4]
def baseStart_987186 : Nat := 118140960795 + 987186 * 2 ^ 59
def prefixEnd_987186 : Nat := 4983230072969 + 3 ^ 40 * 987186 * 2
def baseEnd_987186 : Nat := 150192863226512552277043

theorem tailTrace_987186 : CollatzResearch.WordTrace tailWord_987186 prefixEnd_987186 150192863226512552277043 := by
  unfold tailWord_987186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9001407850400298697785353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24003754267734129860760941 9001407850400298697785353)
  ·
    refine ⟨6751055887800224023339015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9001407850400298697785353 6751055887800224023339015)
    ·
      refine ⟨10126583831700336035008523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6751055887800224023339015 10126583831700336035008523)
      ·
        refine ⟨15189875747550504052512785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10126583831700336035008523 15189875747550504052512785)
        ·
          refine ⟨11392406810662878039384589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15189875747550504052512785 11392406810662878039384589)
          ·
            refine ⟨4272152553998579264769221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11392406810662878039384589 4272152553998579264769221)
            ·
              refine ⟨801028603874733612144229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4272152553998579264769221 801028603874733612144229)
              ·
                refine ⟨150192863226512552277043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 801028603874733612144229 150192863226512552277043)
                ·
                  rfl

theorem cell20_987186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_987186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987186 prefixEnd_987186 := by exact prefixLift 987186
  have htrace : WordTrace (prefixWord ++ tailWord_987186) baseStart_987186 baseEnd_987186 := by
    simpa [prefixWord, tailWord_987186, baseEnd_987186] using wordTrace_append hprefix tailTrace_987186
  have hstable : (prefixWord ++ tailWord_987186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987186).length < 2 ^ (prefixWord ++ tailWord_987186).sum := by decide
  have hdescent : baseEnd_987186 < baseStart_987186 := by decide
  rcases family_descends (prefixWord ++ tailWord_987186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987213 : List Nat := [1, 6, 1, 1, 1, 1, 5, 2, 2]
def baseStart_987213 : Nat := 118140960795 + 987213 * 2 ^ 59
def prefixEnd_987213 : Nat := 4983230072969 + 3 ^ 40 * 987213 * 2
def baseEnd_987213 : Nat := 450590913215245562931019

theorem tailTrace_987213 : CollatzResearch.WordTrace tailWord_987213 prefixEnd_987213 450590913215245562931019 := by
  unfold tailWord_987213
  simp only [CollatzResearch.WordTrace]
  refine ⟨36006616172503378402374293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24004410781668918934916195 36006616172503378402374293)
  ·
    refine ⟨1687810133086095862611295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36006616172503378402374293 1687810133086095862611295)
    ·
      refine ⟨2531715199629143793916943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1687810133086095862611295 2531715199629143793916943)
      ·
        refine ⟨3797572799443715690875415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2531715199629143793916943 3797572799443715690875415)
        ·
          refine ⟨5696359199165573536313123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3797572799443715690875415 5696359199165573536313123)
          ·
            refine ⟨8544538798748360304469685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5696359199165573536313123 8544538798748360304469685)
            ·
              refine ⟨801050512382658778544033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8544538798748360304469685 801050512382658778544033)
              ·
                refine ⟨600787884286994083908025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 801050512382658778544033 600787884286994083908025)
                ·
                  refine ⟨450590913215245562931019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600787884286994083908025 450590913215245562931019)
                  ·
                    rfl

theorem cell20_987213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_987213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987213 prefixEnd_987213 := by exact prefixLift 987213
  have htrace : WordTrace (prefixWord ++ tailWord_987213) baseStart_987213 baseEnd_987213 := by
    simpa [prefixWord, tailWord_987213, baseEnd_987213] using wordTrace_append hprefix tailTrace_987213
  have hstable : (prefixWord ++ tailWord_987213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987213).length < 2 ^ (prefixWord ++ tailWord_987213).sum := by decide
  have hdescent : baseEnd_987213 < baseStart_987213 := by decide
  rcases family_descends (prefixWord ++ tailWord_987213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987245 : List Nat := [1, 5, 1, 1, 2, 1, 1, 8]
def baseStart_987245 : Nat := 118140960795 + 987245 * 2 ^ 59
def prefixEnd_987245 : Nat := 4983230072969 + 3 ^ 40 * 987245 * 2
def baseEnd_987245 : Nat := 150201839629065224621407

theorem tailTrace_987245 : CollatzResearch.WordTrace tailWord_987245 prefixEnd_987245 150201839629065224621407 := by
  unfold tailWord_987245
  simp only [CollatzResearch.WordTrace]
  refine ⟨36007783308387447867539189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24005188872258298578359459 36007783308387447867539189)
  ·
    refine ⟨3375729685161323237581799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36007783308387447867539189 3375729685161323237581799)
    ·
      refine ⟨5063594527741984856372699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3375729685161323237581799 5063594527741984856372699)
      ·
        refine ⟨7595391791612977284559049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5063594527741984856372699 7595391791612977284559049)
        ·
          refine ⟨5696543843709732963419287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7595391791612977284559049 5696543843709732963419287)
          ·
            refine ⟨8544815765564599445128931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5696543843709732963419287 8544815765564599445128931)
            ·
              refine ⟨12817223648346899167693397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8544815765564599445128931 12817223648346899167693397)
              ·
                refine ⟨150201839629065224621407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12817223648346899167693397 150201839629065224621407)
                ·
                  rfl

theorem cell20_987245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 8].length) (baseStart_987245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987245 prefixEnd_987245 := by exact prefixLift 987245
  have htrace : WordTrace (prefixWord ++ tailWord_987245) baseStart_987245 baseEnd_987245 := by
    simpa [prefixWord, tailWord_987245, baseEnd_987245] using wordTrace_append hprefix tailTrace_987245
  have hstable : (prefixWord ++ tailWord_987245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987245).length < 2 ^ (prefixWord ++ tailWord_987245).sum := by decide
  have hdescent : baseEnd_987245 < baseStart_987245 := by decide
  rcases family_descends (prefixWord ++ tailWord_987245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987262 : List Nat := [4, 2, 4, 10]
def baseStart_987262 : Nat := 118140960795 + 987262 * 2 ^ 59
def prefixEnd_987262 : Nat := 4983230072969 + 3 ^ 40 * 987262 * 2
def baseEnd_987262 : Nat := 1854375630248638560895

theorem tailTrace_987262 : CollatzResearch.WordTrace tailWord_987262 prefixEnd_987262 1854375630248638560895 := by
  unfold tailWord_987262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4501050418665732471363505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24005602232883906513938693 4501050418665732471363505)
  ·
    refine ⟨3375787813999299353522629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4501050418665732471363505 3375787813999299353522629)
    ·
      refine ⟨632960215124868628785493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3375787813999299353522629 632960215124868628785493)
      ·
        refine ⟨1854375630248638560895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 632960215124868628785493 1854375630248638560895)
        ·
          rfl

theorem cell20_987262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 10].length) (baseStart_987262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987262 prefixEnd_987262 := by exact prefixLift 987262
  have htrace : WordTrace (prefixWord ++ tailWord_987262) baseStart_987262 baseEnd_987262 := by
    simpa [prefixWord, tailWord_987262, baseEnd_987262] using wordTrace_append hprefix tailTrace_987262
  have hstable : (prefixWord ++ tailWord_987262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987262).length < 2 ^ (prefixWord ++ tailWord_987262).sum := by decide
  have hdescent : baseEnd_987262 < baseStart_987262 := by decide
  rcases family_descends (prefixWord ++ tailWord_987262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987269 : List Nat := [1, 3, 1, 1, 5, 1, 1, 4, 3]
def baseStart_987269 : Nat := 118140960795 + 987269 * 2 ^ 59
def prefixEnd_987269 : Nat := 4983230072969 + 3 ^ 40 * 987269 * 2
def baseEnd_987269 : Nat := 450616473141158257064123

theorem tailTrace_987269 : CollatzResearch.WordTrace tailWord_987269 prefixEnd_987269 450616473141158257064123 := by
  unfold tailWord_987269
  simp only [CollatzResearch.WordTrace]
  refine ⟨36008658660300499966412861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24005772440200333310941907 36008658660300499966412861)
  ·
    refine ⟨13503246997612687487404823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36008658660300499966412861 13503246997612687487404823)
    ·
      refine ⟨20254870496419031231107235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13503246997612687487404823 20254870496419031231107235)
      ·
        refine ⟨30382305744628546846660853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20254870496419031231107235 30382305744628546846660853)
        ·
          refine ⟨2848341163558926266874455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30382305744628546846660853 2848341163558926266874455)
          ·
            refine ⟨4272511745338389400311683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848341163558926266874455 4272511745338389400311683)
            ·
              refine ⟨6408767618007584100467525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4272511745338389400311683 6408767618007584100467525)
              ·
                refine ⟨1201643928376422018837661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6408767618007584100467525 1201643928376422018837661)
                ·
                  refine ⟨450616473141158257064123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1201643928376422018837661 450616473141158257064123)
                  ·
                    rfl

theorem cell20_987269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_987269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987269 prefixEnd_987269 := by exact prefixLift 987269
  have htrace : WordTrace (prefixWord ++ tailWord_987269) baseStart_987269 baseEnd_987269 := by
    simpa [prefixWord, tailWord_987269, baseEnd_987269] using wordTrace_append hprefix tailTrace_987269
  have hstable : (prefixWord ++ tailWord_987269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987269).length < 2 ^ (prefixWord ++ tailWord_987269).sum := by decide
  have hdescent : baseEnd_987269 < baseStart_987269 := by decide
  rcases family_descends (prefixWord ++ tailWord_987269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987272 : List Nat := [2, 1, 3, 4, 1, 2, 1, 4, 2]
def baseStart_987272 : Nat := 118140960795 + 987272 * 2 ^ 59
def prefixEnd_987272 : Nat := 4983230072969 + 3 ^ 40 * 987272 * 2
def baseEnd_987272 : Nat := 450617842422903579964111

theorem tailTrace_987272 : CollatzResearch.WordTrace tailWord_987272 prefixEnd_987272 450617842422903579964111 := by
  unfold tailWord_987272
  simp only [CollatzResearch.WordTrace]
  refine ⟨18004384039644815739386035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24005845386193087652514713 18004384039644815739386035)
  ·
    refine ⟨27006576059467223609079053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18004384039644815739386035 27006576059467223609079053)
    ·
      refine ⟨10127466022300208853404645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27006576059467223609079053 10127466022300208853404645)
      ·
        refine ⟨1898899879181289160013371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10127466022300208853404645 1898899879181289160013371)
        ·
          refine ⟨2848349818771933740020057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1898899879181289160013371 2848349818771933740020057)
          ·
            refine ⟨2136262364078950305015043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2848349818771933740020057 2136262364078950305015043)
            ·
              refine ⟨3204393546118425457522565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2136262364078950305015043 3204393546118425457522565)
              ·
                refine ⟨600823789897204773285481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3204393546118425457522565 600823789897204773285481)
                ·
                  refine ⟨450617842422903579964111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600823789897204773285481 450617842422903579964111)
                  ·
                    rfl

theorem cell20_987272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 2].length) (baseStart_987272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987272 prefixEnd_987272 := by exact prefixLift 987272
  have htrace : WordTrace (prefixWord ++ tailWord_987272) baseStart_987272 baseEnd_987272 := by
    simpa [prefixWord, tailWord_987272, baseEnd_987272] using wordTrace_append hprefix tailTrace_987272
  have hstable : (prefixWord ++ tailWord_987272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987272).length < 2 ^ (prefixWord ++ tailWord_987272).sum := by decide
  have hdescent : baseEnd_987272 < baseStart_987272 := by decide
  rcases family_descends (prefixWord ++ tailWord_987272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987316 : List Nat := [2, 5, 3, 1, 2, 1, 1, 2, 3]
def baseStart_987316 : Nat := 118140960795 + 987316 * 2 ^ 59
def prefixEnd_987316 : Nat := 4983230072969 + 3 ^ 40 * 987316 * 2
def baseEnd_987316 : Nat := 450637925221834982497265

theorem tailTrace_987316 : CollatzResearch.WordTrace tailWord_987316 prefixEnd_987316 450637925221834982497265 := by
  unfold tailWord_987316
  simp only [CollatzResearch.WordTrace]
  refine ⟨18005186445565113496686901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24006915260753484662249201 18005186445565113496686901)
  ·
    refine ⟨1687986229271729390314397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18005186445565113496686901 1687986229271729390314397)
    ·
      refine ⟨632994835976898521367899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1687986229271729390314397 632994835976898521367899)
      ·
        refine ⟨949492253965347782051849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632994835976898521367899 949492253965347782051849)
        ·
          refine ⟨712119190474010836538887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 949492253965347782051849 712119190474010836538887)
          ·
            refine ⟨1068178785711016254808331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712119190474010836538887 1068178785711016254808331)
            ·
              refine ⟨1602268178566524382212497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068178785711016254808331 1602268178566524382212497)
              ·
                refine ⟨1201701133924893286659373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1602268178566524382212497 1201701133924893286659373)
                ·
                  refine ⟨450637925221834982497265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1201701133924893286659373 450637925221834982497265)
                  ·
                    rfl

theorem cell20_987316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_987316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987316 prefixEnd_987316 := by exact prefixLift 987316
  have htrace : WordTrace (prefixWord ++ tailWord_987316) baseStart_987316 baseEnd_987316 := by
    simpa [prefixWord, tailWord_987316, baseEnd_987316] using wordTrace_append hprefix tailTrace_987316
  have hstable : (prefixWord ++ tailWord_987316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987316).length < 2 ^ (prefixWord ++ tailWord_987316).sum := by decide
  have hdescent : baseEnd_987316 < baseStart_987316 := by decide
  rcases family_descends (prefixWord ++ tailWord_987316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987352 : List Nat := [2, 1, 2, 2, 4, 1, 2, 2, 4]
def baseStart_987352 : Nat := 118140960795 + 987352 * 2 ^ 59
def prefixEnd_987352 : Nat := 4983230072969 + 3 ^ 40 * 987352 * 2
def baseEnd_987352 : Nat := 450654356602778857297117

theorem tailTrace_987352 : CollatzResearch.WordTrace tailWord_987352 prefixEnd_987352 450654356602778857297117 := by
  unfold tailWord_987352
  simp only [CollatzResearch.WordTrace]
  refine ⟨18005842959499902570842155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24007790612666536761122873 18005842959499902570842155)
  ·
    refine ⟨27008764439249853856263233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18005842959499902570842155 27008764439249853856263233)
    ·
      refine ⟨20256573329437390392197425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27008764439249853856263233 20256573329437390392197425)
      ·
        refine ⟨15192429997078042794148069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20256573329437390392197425 15192429997078042794148069)
        ·
          refine ⟨2848580624452133023902763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15192429997078042794148069 2848580624452133023902763)
          ·
            refine ⟨4272870936678199535854145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848580624452133023902763 4272870936678199535854145)
            ·
              refine ⟨3204653202508649651890609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4272870936678199535854145 3204653202508649651890609)
              ·
                refine ⟨2403489901881487238917957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3204653202508649651890609 2403489901881487238917957)
                ·
                  refine ⟨450654356602778857297117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2403489901881487238917957 450654356602778857297117)
                  ·
                    rfl

theorem cell20_987352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_987352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987352 prefixEnd_987352 := by exact prefixLift 987352
  have htrace : WordTrace (prefixWord ++ tailWord_987352) baseStart_987352 baseEnd_987352 := by
    simpa [prefixWord, tailWord_987352, baseEnd_987352] using wordTrace_append hprefix tailTrace_987352
  have hstable : (prefixWord ++ tailWord_987352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987352).length < 2 ^ (prefixWord ++ tailWord_987352).sum := by decide
  have hdescent : baseEnd_987352 < baseStart_987352 := by decide
  rcases family_descends (prefixWord ++ tailWord_987352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987386 : List Nat := [3, 1, 1, 1, 1, 6, 3, 2, 2]
def baseStart_987386 : Nat := 118140960795 + 987386 * 2 ^ 59
def prefixEnd_987386 : Nat := 4983230072969 + 3 ^ 40 * 987386 * 2
def baseEnd_987386 : Nat := 450669875129225850163645

theorem tailTrace_987386 : CollatzResearch.WordTrace tailWord_987386 prefixEnd_987386 450669875129225850163645 := by
  unfold tailWord_987386
  simp only [CollatzResearch.WordTrace]
  refine ⟨9003231500219157237105503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24008617333917752632281341 9003231500219157237105503)
  ·
    refine ⟨13504847250328735855658255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9003231500219157237105503 13504847250328735855658255)
    ·
      refine ⟨20257270875493103783487383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13504847250328735855658255 20257270875493103783487383)
      ·
        refine ⟨30385906313239655675231075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20257270875493103783487383 30385906313239655675231075)
        ·
          refine ⟨45578859469859483512846613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30385906313239655675231075 45578859469859483512846613)
          ·
            refine ⟨2136509037649663289664685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45578859469859483512846613 2136509037649663289664685)
            ·
              refine ⟨801190889118623733624257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2136509037649663289664685 801190889118623733624257)
              ·
                refine ⟨600893166838967800218193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 801190889118623733624257 600893166838967800218193)
                ·
                  refine ⟨450669875129225850163645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600893166838967800218193 450669875129225850163645)
                  ·
                    rfl

theorem cell20_987386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_987386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987386 prefixEnd_987386 := by exact prefixLift 987386
  have htrace : WordTrace (prefixWord ++ tailWord_987386) baseStart_987386 baseEnd_987386 := by
    simpa [prefixWord, tailWord_987386, baseEnd_987386] using wordTrace_append hprefix tailTrace_987386
  have hstable : (prefixWord ++ tailWord_987386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987386).length < 2 ^ (prefixWord ++ tailWord_987386).sum := by decide
  have hdescent : baseEnd_987386 < baseStart_987386 := by decide
  rcases family_descends (prefixWord ++ tailWord_987386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987396 : List Nat := [2, 3, 2, 2, 4, 1, 2, 1, 3]
def baseStart_987396 : Nat := 118140960795 + 987396 * 2 ^ 59
def prefixEnd_987396 : Nat := 4983230072969 + 3 ^ 40 * 987396 * 2
def baseEnd_987396 : Nat := 450674439401710259830271

theorem tailTrace_987396 : CollatzResearch.WordTrace tailWord_987396 prefixEnd_987396 450674439401710259830271 := by
  unfold tailWord_987396
  simp only [CollatzResearch.WordTrace]
  refine ⟨18006645365420200328143021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24008860487226933770857361 18006645365420200328143021)
  ·
    refine ⟨6752492012032575123053633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18006645365420200328143021 6752492012032575123053633)
    ·
      refine ⟨5064369009024431342290225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6752492012032575123053633 5064369009024431342290225)
      ·
        refine ⟨3798276756768323506717669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5064369009024431342290225 3798276756768323506717669)
        ·
          refine ⟨712176891894060657509563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3798276756768323506717669 712176891894060657509563)
          ·
            refine ⟨1068265337841090986264345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712176891894060657509563 1068265337841090986264345)
            ·
              refine ⟨801199003380818239698259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1068265337841090986264345 801199003380818239698259)
              ·
                refine ⟨1201798505071227359547389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801199003380818239698259 1201798505071227359547389)
                ·
                  refine ⟨450674439401710259830271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1201798505071227359547389 450674439401710259830271)
                  ·
                    rfl

theorem cell20_987396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_987396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987396 prefixEnd_987396 := by exact prefixLift 987396
  have htrace : WordTrace (prefixWord ++ tailWord_987396) baseStart_987396 baseEnd_987396 := by
    simpa [prefixWord, tailWord_987396, baseEnd_987396] using wordTrace_append hprefix tailTrace_987396
  have hstable : (prefixWord ++ tailWord_987396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987396).length < 2 ^ (prefixWord ++ tailWord_987396).sum := by decide
  have hdescent : baseEnd_987396 < baseStart_987396 := by decide
  rcases family_descends (prefixWord ++ tailWord_987396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987400 : List Nat := [2, 1, 3, 2, 3, 1, 4, 1, 3]
def baseStart_987400 : Nat := 118140960795 + 987400 * 2 ^ 59
def prefixEnd_987400 : Nat := 4983230072969 + 3 ^ 40 * 987400 * 2
def baseEnd_987400 : Nat := 450676265110704023696921

theorem tailTrace_987400 : CollatzResearch.WordTrace tailWord_987400 prefixEnd_987400 450676265110704023696921 := by
  unfold tailWord_987400
  simp only [CollatzResearch.WordTrace]
  refine ⟨18006718311412954669715827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24008957748550606226287769 18006718311412954669715827)
  ·
    refine ⟨27010077467119432004573741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18006718311412954669715827 27010077467119432004573741)
    ·
      refine ⟨10128779050169787001715153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27010077467119432004573741 10128779050169787001715153)
      ·
        refine ⟨7596584287627340251286365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10128779050169787001715153 7596584287627340251286365)
        ·
          refine ⟨2848719107860252594232387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7596584287627340251286365 2848719107860252594232387)
          ·
            refine ⟨4273078661790378891348581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848719107860252594232387 4273078661790378891348581)
            ·
              refine ⟨801202249085696042127859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4273078661790378891348581 801202249085696042127859)
              ·
                refine ⟨1201803373628544063191789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801202249085696042127859 1201803373628544063191789)
                ·
                  refine ⟨450676265110704023696921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1201803373628544063191789 450676265110704023696921)
                  ·
                    rfl

theorem cell20_987400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 3].length) (baseStart_987400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987400 prefixEnd_987400 := by exact prefixLift 987400
  have htrace : WordTrace (prefixWord ++ tailWord_987400) baseStart_987400 baseEnd_987400 := by
    simpa [prefixWord, tailWord_987400, baseEnd_987400] using wordTrace_append hprefix tailTrace_987400
  have hstable : (prefixWord ++ tailWord_987400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987400).length < 2 ^ (prefixWord ++ tailWord_987400).sum := by decide
  have hdescent : baseEnd_987400 < baseStart_987400 := by decide
  rcases family_descends (prefixWord ++ tailWord_987400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987411 : List Nat := [1, 1, 1, 2, 1, 3, 1, 6, 4]
def baseStart_987411 : Nat := 118140960795 + 987411 * 2 ^ 59
def prefixEnd_987411 : Nat := 4983230072969 + 3 ^ 40 * 987411 * 2
def baseEnd_987411 : Nat := 450681285810436874330209

theorem tailTrace_987411 : CollatzResearch.WordTrace tailWord_987411 prefixEnd_987411 450681285810436874330209 := by
  unfold tailWord_987411
  simp only [CollatzResearch.WordTrace]
  refine ⟨36013837825786058218082087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24009225217190705478721391 36013837825786058218082087)
  ·
    refine ⟨54020756738679087327123131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36013837825786058218082087 54020756738679087327123131)
    ·
      refine ⟨81031135108018630990684697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54020756738679087327123131 81031135108018630990684697)
      ·
        refine ⟨60773351331013973243013523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81031135108018630990684697 60773351331013973243013523)
        ·
          refine ⟨91160026996520959864520285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60773351331013973243013523 91160026996520959864520285)
          ·
            refine ⟨34185010123695359949195107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91160026996520959864520285 34185010123695359949195107)
            ·
              refine ⟨51277515185543039923792661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34185010123695359949195107 51277515185543039923792661)
              ·
                refine ⟨2403633524322329996427781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51277515185543039923792661 2403633524322329996427781)
                ·
                  refine ⟨450681285810436874330209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2403633524322329996427781 450681285810436874330209)
                  ·
                    rfl

theorem cell20_987411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_987411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987411 prefixEnd_987411 := by exact prefixLift 987411
  have htrace : WordTrace (prefixWord ++ tailWord_987411) baseStart_987411 baseEnd_987411 := by
    simpa [prefixWord, tailWord_987411, baseEnd_987411] using wordTrace_append hprefix tailTrace_987411
  have hstable : (prefixWord ++ tailWord_987411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987411).length < 2 ^ (prefixWord ++ tailWord_987411).sum := by decide
  have hdescent : baseEnd_987411 < baseStart_987411 := by decide
  rcases family_descends (prefixWord ++ tailWord_987411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987431 : List Nat := [1, 1, 8, 1, 1, 8]
def baseStart_987431 : Nat := 118140960795 + 987431 * 2 ^ 59
def prefixEnd_987431 : Nat := 4983230072969 + 3 ^ 40 * 987431 * 2
def baseEnd_987431 : Nat := 16692237568718729394943

theorem tailTrace_987431 : CollatzResearch.WordTrace tailWord_987431 prefixEnd_987431 16692237568718729394943 := by
  unfold tailWord_987431
  simp only [CollatzResearch.WordTrace]
  refine ⟨36014567285713601633810147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24009711523809067755873431 36014567285713601633810147)
  ·
    refine ⟨54021850928570402450715221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36014567285713601633810147 54021850928570402450715221)
    ·
      refine ⟨633068565569184403719319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 54021850928570402450715221 633068565569184403719319)
      ·
        refine ⟨949602848353776605578979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633068565569184403719319 949602848353776605578979)
        ·
          refine ⟨1424404272530664908368469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949602848353776605578979 1424404272530664908368469)
          ·
            refine ⟨16692237568718729394943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1424404272530664908368469 16692237568718729394943)
            ·
              rfl

theorem cell20_987431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 8].length) (baseStart_987431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987431 prefixEnd_987431 := by exact prefixLift 987431
  have htrace : WordTrace (prefixWord ++ tailWord_987431) baseStart_987431 baseEnd_987431 := by
    simpa [prefixWord, tailWord_987431, baseEnd_987431] using wordTrace_append hprefix tailTrace_987431
  have hstable : (prefixWord ++ tailWord_987431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987431).length < 2 ^ (prefixWord ++ tailWord_987431).sum := by decide
  have hdescent : baseEnd_987431 < baseStart_987431 := by decide
  rcases family_descends (prefixWord ++ tailWord_987431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987437 : List Nat := [1, 5, 3, 1, 3, 1, 2, 2, 2]
def baseStart_987437 : Nat := 118140960795 + 987437 * 2 ^ 59
def prefixEnd_987437 : Nat := 4983230072969 + 3 ^ 40 * 987437 * 2
def baseEnd_987437 : Nat := 450693152918896339463437

theorem tailTrace_987437 : CollatzResearch.WordTrace tailWord_987437 prefixEnd_987437 450693152918896339463437 := by
  unfold tailWord_987437
  simp only [CollatzResearch.WordTrace]
  refine ⟨36014786123691864658528565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24009857415794576439019043 36014786123691864658528565)
  ·
    refine ⟨3376386199096112311737053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36014786123691864658528565 3376386199096112311737053)
    ·
      refine ⟨1266144824661042116901395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3376386199096112311737053 1266144824661042116901395)
      ·
        refine ⟨1899217236991563175352093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1266144824661042116901395 1899217236991563175352093)
        ·
          refine ⟨712206463871836190757035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1899217236991563175352093 712206463871836190757035)
          ·
            refine ⟨1068309695807754286135553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712206463871836190757035 1068309695807754286135553)
            ·
              refine ⟨801232271855815714601665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1068309695807754286135553 801232271855815714601665)
              ·
                refine ⟨600924203891861785951249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 801232271855815714601665 600924203891861785951249)
                ·
                  refine ⟨450693152918896339463437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600924203891861785951249 450693152918896339463437)
                  ·
                    rfl

theorem cell20_987437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_987437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987437 prefixEnd_987437 := by exact prefixLift 987437
  have htrace : WordTrace (prefixWord ++ tailWord_987437) baseStart_987437 baseEnd_987437 := by
    simpa [prefixWord, tailWord_987437, baseEnd_987437] using wordTrace_append hprefix tailTrace_987437
  have hstable : (prefixWord ++ tailWord_987437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987437).length < 2 ^ (prefixWord ++ tailWord_987437).sum := by decide
  have hdescent : baseEnd_987437 < baseStart_987437 := by decide
  rcases family_descends (prefixWord ++ tailWord_987437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987441 : List Nat := [1, 2, 2, 3, 4, 2, 2, 2, 2]
def baseStart_987441 : Nat := 118140960795 + 987441 * 2 ^ 59
def prefixEnd_987441 : Nat := 4983230072969 + 3 ^ 40 * 987441 * 2
def baseEnd_987441 : Nat := 450694978627890103330087

theorem tailTrace_987441 : CollatzResearch.WordTrace tailWord_987441 prefixEnd_987441 450694978627890103330087 := by
  unfold tailWord_987441
  simp only [CollatzResearch.WordTrace]
  refine ⟨36014932015677373341674177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24009954677118248894449451 36014932015677373341674177)
  ·
    refine ⟨27011199011758030006255633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36014932015677373341674177 27011199011758030006255633)
    ·
      refine ⟨20258399258818522504691725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27011199011758030006255633 20258399258818522504691725)
      ·
        refine ⟨7596899722056945939259397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20258399258818522504691725 7596899722056945939259397)
        ·
          refine ⟨1424418697885677363611137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7596899722056945939259397 1424418697885677363611137)
          ·
            refine ⟨1068314023414258022708353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1424418697885677363611137 1068314023414258022708353)
            ·
              refine ⟨801235517560693517031265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1068314023414258022708353 801235517560693517031265)
              ·
                refine ⟨600926638170520137773449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 801235517560693517031265 600926638170520137773449)
                ·
                  refine ⟨450694978627890103330087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600926638170520137773449 450694978627890103330087)
                  ·
                    rfl

theorem cell20_987441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 2].length) (baseStart_987441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987441 prefixEnd_987441 := by exact prefixLift 987441
  have htrace : WordTrace (prefixWord ++ tailWord_987441) baseStart_987441 baseEnd_987441 := by
    simpa [prefixWord, tailWord_987441, baseEnd_987441] using wordTrace_append hprefix tailTrace_987441
  have hstable : (prefixWord ++ tailWord_987441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987441).length < 2 ^ (prefixWord ++ tailWord_987441).sum := by decide
  have hdescent : baseEnd_987441 < baseStart_987441 := by decide
  rcases family_descends (prefixWord ++ tailWord_987441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987445 : List Nat := [1, 3, 3, 1, 2, 1, 3, 4, 2]
def baseStart_987445 : Nat := 118140960795 + 987445 * 2 ^ 59
def prefixEnd_987445 : Nat := 4983230072969 + 3 ^ 40 * 987445 * 2
def baseEnd_987445 : Nat := 450696804336883867196737

theorem tailTrace_987445 : CollatzResearch.WordTrace tailWord_987445 prefixEnd_987445 450696804336883867196737 := by
  unfold tailWord_987445
  simp only [CollatzResearch.WordTrace]
  refine ⟨36015077907662882024819789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24010051938441921349879859 36015077907662882024819789)
  ·
    refine ⟨13505654215373580759307421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36015077907662882024819789 13505654215373580759307421)
    ·
      refine ⟨5064620330765092784740283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13505654215373580759307421 5064620330765092784740283)
      ·
        refine ⟨7596930496147639177110425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5064620330765092784740283 7596930496147639177110425)
        ·
          refine ⟨5697697872110729382832819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7596930496147639177110425 5697697872110729382832819)
          ·
            refine ⟨8546546808166094074249229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5697697872110729382832819 8546546808166094074249229)
            ·
              refine ⟨3204955053062285277843461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8546546808166094074249229 3204955053062285277843461)
              ·
                refine ⟨600929072449178489595649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3204955053062285277843461 600929072449178489595649)
                ·
                  refine ⟨450696804336883867196737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600929072449178489595649 450696804336883867196737)
                  ·
                    rfl

theorem cell20_987445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 2].length) (baseStart_987445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987445 prefixEnd_987445 := by exact prefixLift 987445
  have htrace : WordTrace (prefixWord ++ tailWord_987445) baseStart_987445 baseEnd_987445 := by
    simpa [prefixWord, tailWord_987445, baseEnd_987445] using wordTrace_append hprefix tailTrace_987445
  have hstable : (prefixWord ++ tailWord_987445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987445).length < 2 ^ (prefixWord ++ tailWord_987445).sum := by decide
  have hdescent : baseEnd_987445 < baseStart_987445 := by decide
  rcases family_descends (prefixWord ++ tailWord_987445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987456 : List Nat := [2, 1, 1, 2, 2, 1, 2, 9]
def baseStart_987456 : Nat := 118140960795 + 987456 * 2 ^ 59
def prefixEnd_987456 : Nat := 4983230072969 + 3 ^ 40 * 987456 * 2
def baseEnd_987456 : Nat := 150233941678872239276675

theorem tailTrace_987456 : CollatzResearch.WordTrace tailWord_987456 prefixEnd_987456 150233941678872239276675 := by
  unfold tailWord_987456
  simp only [CollatzResearch.WordTrace]
  refine ⟨18007739555311515451735111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24010319407082020602313481 18007739555311515451735111)
  ·
    refine ⟨27011609332967273177602667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18007739555311515451735111 27011609332967273177602667)
    ·
      refine ⟨40517413999450909766404001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27011609332967273177602667 40517413999450909766404001)
      ·
        refine ⟨30388060499588182324803001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40517413999450909766404001 30388060499588182324803001)
        ·
          refine ⟨22791045374691136743602251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30388060499588182324803001 22791045374691136743602251)
          ·
            refine ⟨34186568062036705115403377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22791045374691136743602251 34186568062036705115403377)
            ·
              refine ⟨25639926046527528836552533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34186568062036705115403377 25639926046527528836552533)
              ·
                refine ⟨150233941678872239276675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25639926046527528836552533 150233941678872239276675)
                ·
                  rfl

theorem cell20_987456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_987456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987456 prefixEnd_987456 := by exact prefixLift 987456
  have htrace : WordTrace (prefixWord ++ tailWord_987456) baseStart_987456 baseEnd_987456 := by
    simpa [prefixWord, tailWord_987456, baseEnd_987456] using wordTrace_append hprefix tailTrace_987456
  have hstable : (prefixWord ++ tailWord_987456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987456).length < 2 ^ (prefixWord ++ tailWord_987456).sum := by decide
  have hdescent : baseEnd_987456 < baseStart_987456 := by decide
  rcases family_descends (prefixWord ++ tailWord_987456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987504 : List Nat := [2, 1, 1, 1, 4, 4, 2, 1, 4]
def baseStart_987504 : Nat := 118140960795 + 987504 * 2 ^ 59
def prefixEnd_987504 : Nat := 4983230072969 + 3 ^ 40 * 987504 * 2
def baseEnd_987504 : Nat := 450723733544541884229829

theorem tailTrace_987504 : CollatzResearch.WordTrace tailWord_987504 prefixEnd_987504 450723733544541884229829 := by
  unfold tailWord_987504
  simp only [CollatzResearch.WordTrace]
  refine ⟨18008614907224567550608783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24011486542966090067478377 18008614907224567550608783)
  ·
    refine ⟨27012922360836851325913175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18008614907224567550608783 27012922360836851325913175)
    ·
      refine ⟨40519383541255276988869763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27012922360836851325913175 40519383541255276988869763)
      ·
        refine ⟨60779075311882915483304645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40519383541255276988869763 60779075311882915483304645)
        ·
          refine ⟨11396076620978046653119621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60779075311882915483304645 11396076620978046653119621)
          ·
            refine ⟨2136764366433383747459929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11396076620978046653119621 2136764366433383747459929)
            ·
              refine ⟨1602573274825037810594947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2136764366433383747459929 1602573274825037810594947)
              ·
                refine ⟨2403859912237556715892421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1602573274825037810594947 2403859912237556715892421)
                ·
                  refine ⟨450723733544541884229829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2403859912237556715892421 450723733544541884229829)
                  ·
                    rfl

theorem cell20_987504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_987504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987504 prefixEnd_987504 := by exact prefixLift 987504
  have htrace : WordTrace (prefixWord ++ tailWord_987504) baseStart_987504 baseEnd_987504 := by
    simpa [prefixWord, tailWord_987504, baseEnd_987504] using wordTrace_append hprefix tailTrace_987504
  have hstable : (prefixWord ++ tailWord_987504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987504).length < 2 ^ (prefixWord ++ tailWord_987504).sum := by decide
  have hdescent : baseEnd_987504 < baseStart_987504 := by decide
  rcases family_descends (prefixWord ++ tailWord_987504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987510 : List Nat := [5, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_987510 : Nat := 118140960795 + 987510 * 2 ^ 59
def prefixEnd_987510 : Nat := 4983230072969 + 3 ^ 40 * 987510 * 2
def baseEnd_987510 : Nat := 450726472108032530029805

theorem tailTrace_987510 : CollatzResearch.WordTrace tailWord_987510 prefixEnd_987510 450726472108032530029805 := by
  unfold tailWord_987510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2251090540776712382870999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24011632434951598750623989 2251090540776712382870999)
  ·
    refine ⟨3376635811165068574306499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2251090540776712382870999 3376635811165068574306499)
    ·
      refine ⟨5064953716747602861459749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3376635811165068574306499 5064953716747602861459749)
      ·
        refine ⟨949678821890175536523703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5064953716747602861459749 949678821890175536523703)
        ·
          refine ⟨1424518232835263304785555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949678821890175536523703 1424518232835263304785555)
          ·
            refine ⟨2136777349252894957178333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424518232835263304785555 2136777349252894957178333)
            ·
              refine ⟨801291505969835608941875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2136777349252894957178333 801291505969835608941875)
              ·
                refine ⟨1201937258954753413412813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801291505969835608941875 1201937258954753413412813)
                ·
                  refine ⟨450726472108032530029805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1201937258954753413412813 450726472108032530029805)
                  ·
                    rfl

theorem cell20_987510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_987510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987510 prefixEnd_987510 := by exact prefixLift 987510
  have htrace : WordTrace (prefixWord ++ tailWord_987510) baseStart_987510 baseEnd_987510 := by
    simpa [prefixWord, tailWord_987510, baseEnd_987510] using wordTrace_append hprefix tailTrace_987510
  have hstable : (prefixWord ++ tailWord_987510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987510).length < 2 ^ (prefixWord ++ tailWord_987510).sum := by decide
  have hdescent : baseEnd_987510 < baseStart_987510 := by decide
  rcases family_descends (prefixWord ++ tailWord_987510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987556 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 5]
def baseStart_987556 : Nat := 118140960795 + 987556 * 2 ^ 59
def prefixEnd_987556 : Nat := 4983230072969 + 3 ^ 40 * 987556 * 2
def baseEnd_987556 : Nat := 450747467761460814496283

theorem tailTrace_987556 : CollatzResearch.WordTrace tailWord_987556 prefixEnd_987556 450747467761460814496283 := by
  unfold tailWord_987556
  simp only [CollatzResearch.WordTrace]
  refine ⟨18009563205130373991055261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24012750940173831988073681 18009563205130373991055261)
  ·
    refine ⟨6753586201923890246645723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18009563205130373991055261 6753586201923890246645723)
    ·
      refine ⟨10130379302885835369968585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6753586201923890246645723 10130379302885835369968585)
      ·
        refine ⟨7597784477164376527476439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10130379302885835369968585 7597784477164376527476439)
        ·
          refine ⟨11396676715746564791214659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7597784477164376527476439 11396676715746564791214659)
          ·
            refine ⟨17095015073619847186821989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11396676715746564791214659 17095015073619847186821989)
            ·
              refine ⟨3205315326303721347529123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17095015073619847186821989 3205315326303721347529123)
              ·
                refine ⟨4807972989455582021293685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3205315326303721347529123 4807972989455582021293685)
                ·
                  refine ⟨450747467761460814496283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4807972989455582021293685 450747467761460814496283)
                  ·
                    rfl

theorem cell20_987556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_987556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987556 prefixEnd_987556 := by exact prefixLift 987556
  have htrace : WordTrace (prefixWord ++ tailWord_987556) baseStart_987556 baseEnd_987556 := by
    simpa [prefixWord, tailWord_987556, baseEnd_987556] using wordTrace_append hprefix tailTrace_987556
  have hstable : (prefixWord ++ tailWord_987556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987556).length < 2 ^ (prefixWord ++ tailWord_987556).sum := by decide
  have hdescent : baseEnd_987556 < baseStart_987556 := by decide
  rcases family_descends (prefixWord ++ tailWord_987556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987559 : List Nat := [1, 1, 6, 1, 1, 4, 1, 1, 4]
def baseStart_987559 : Nat := 118140960795 + 987559 * 2 ^ 59
def prefixEnd_987559 : Nat := 4983230072969 + 3 ^ 40 * 987559 * 2
def baseEnd_987559 : Nat := 450748837043206137396271

theorem tailTrace_987559 : CollatzResearch.WordTrace tailWord_987559 prefixEnd_987559 450748837043206137396271 := by
  unfold tailWord_987559
  simp only [CollatzResearch.WordTrace]
  refine ⟨36019235829249879494469731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24012823886166586329646487 36019235829249879494469731)
  ·
    refine ⟨54028853743874819241704597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36019235829249879494469731 54028853743874819241704597)
    ·
      refine ⟨2532602519244132151954903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54028853743874819241704597 2532602519244132151954903)
      ·
        refine ⟨3798903778866198227932355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2532602519244132151954903 3798903778866198227932355)
        ·
          refine ⟨5698355668299297341898533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3798903778866198227932355 5698355668299297341898533)
          ·
            refine ⟨1068441687806118251605975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5698355668299297341898533 1068441687806118251605975)
            ·
              refine ⟨1602662531709177377408963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068441687806118251605975 1602662531709177377408963)
              ·
                refine ⟨2403993797563766066113445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1602662531709177377408963 2403993797563766066113445)
                ·
                  refine ⟨450748837043206137396271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2403993797563766066113445 450748837043206137396271)
                  ·
                    rfl

theorem cell20_987559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 4].length) (baseStart_987559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987559 prefixEnd_987559 := by exact prefixLift 987559
  have htrace : WordTrace (prefixWord ++ tailWord_987559) baseStart_987559 baseEnd_987559 := by
    simpa [prefixWord, tailWord_987559, baseEnd_987559] using wordTrace_append hprefix tailTrace_987559
  have hstable : (prefixWord ++ tailWord_987559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987559).length < 2 ^ (prefixWord ++ tailWord_987559).sum := by decide
  have hdescent : baseEnd_987559 < baseStart_987559 := by decide
  rcases family_descends (prefixWord ++ tailWord_987559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987562 : List Nat := [3, 1, 6, 1, 1, 1, 2, 5]
def baseStart_987562 : Nat := 118140960795 + 987562 * 2 ^ 59
def prefixEnd_987562 : Nat := 4983230072969 + 3 ^ 40 * 987562 * 2
def baseEnd_987562 : Nat := 150250068774983820098753

theorem tailTrace_987562 : CollatzResearch.WordTrace tailWord_987562 prefixEnd_987562 150250068774983820098753 := by
  unfold tailWord_987562
  simp only [CollatzResearch.WordTrace]
  refine ⟨9004836312059752751707235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24012896832159340671219293 9004836312059752751707235)
  ·
    refine ⟨13507254468089629127560853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9004836312059752751707235 13507254468089629127560853)
    ·
      refine ⟨633152553191701365354415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13507254468089629127560853 633152553191701365354415)
      ·
        refine ⟨949728829787552048031623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633152553191701365354415 949728829787552048031623)
        ·
          refine ⟨1424593244681328072047435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949728829787552048031623 1424593244681328072047435)
          ·
            refine ⟨2136889867021992108071153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424593244681328072047435 2136889867021992108071153)
            ·
              refine ⟨1602667400266494081053365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2136889867021992108071153 1602667400266494081053365)
              ·
                refine ⟨150250068774983820098753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1602667400266494081053365 150250068774983820098753)
                ·
                  rfl

theorem cell20_987562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_987562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987562 prefixEnd_987562 := by exact prefixLift 987562
  have htrace : WordTrace (prefixWord ++ tailWord_987562) baseStart_987562 baseEnd_987562 := by
    simpa [prefixWord, tailWord_987562, baseEnd_987562] using wordTrace_append hprefix tailTrace_987562
  have hstable : (prefixWord ++ tailWord_987562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987562).length < 2 ^ (prefixWord ++ tailWord_987562).sum := by decide
  have hdescent : baseEnd_987562 < baseStart_987562 := by decide
  rcases family_descends (prefixWord ++ tailWord_987562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987621 : List Nat := [1, 3, 1, 5, 3, 1, 1, 5]
def baseStart_987621 : Nat := 118140960795 + 987621 * 2 ^ 59
def prefixEnd_987621 : Nat := 4983230072969 + 3 ^ 40 * 987621 * 2
def baseEnd_987621 : Nat := 150259045177536492443117

theorem tailTrace_987621 : CollatzResearch.WordTrace tailWord_987621 prefixEnd_987621 150259045177536492443117 := by
  unfold tailWord_987621
  simp only [CollatzResearch.WordTrace]
  refine ⟨36021497155025264083226717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24014331436683509388817811 36021497155025264083226717)
  ·
    refine ⟨13508061433134474031210019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36021497155025264083226717 13508061433134474031210019)
    ·
      refine ⟨20262092149701711046815029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13508061433134474031210019 20262092149701711046815029)
      ·
        refine ⟨1899571139034535410638909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20262092149701711046815029 1899571139034535410638909)
        ·
          refine ⟨712339177137950778989591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1899571139034535410638909 712339177137950778989591)
          ·
            refine ⟨1068508765706926168484387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712339177137950778989591 1068508765706926168484387)
            ·
              refine ⟨1602763148560389252726581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068508765706926168484387 1602763148560389252726581)
              ·
                refine ⟨150259045177536492443117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1602763148560389252726581 150259045177536492443117)
                ·
                  rfl

theorem cell20_987621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 5].length) (baseStart_987621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987621 prefixEnd_987621 := by exact prefixLift 987621
  have htrace : WordTrace (prefixWord ++ tailWord_987621) baseStart_987621 baseEnd_987621 := by
    simpa [prefixWord, tailWord_987621, baseEnd_987621] using wordTrace_append hprefix tailTrace_987621
  have hstable : (prefixWord ++ tailWord_987621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987621).length < 2 ^ (prefixWord ++ tailWord_987621).sum := by decide
  have hdescent : baseEnd_987621 < baseStart_987621 := by decide
  rcases family_descends (prefixWord ++ tailWord_987621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987632 : List Nat := [2, 1, 1, 1, 3, 3, 1, 5, 3]
def baseStart_987632 : Nat := 118140960795 + 987632 * 2 ^ 59
def prefixEnd_987632 : Nat := 4983230072969 + 3 ^ 40 * 987632 * 2
def baseEnd_987632 : Nat := 450782156232342327962639

theorem tailTrace_987632 : CollatzResearch.WordTrace tailWord_987632 prefixEnd_987632 450782156232342327962639 := by
  unfold tailWord_987632
  simp only [CollatzResearch.WordTrace]
  refine ⟨18010949178992706480938575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24014598905323608641251433 18010949178992706480938575)
  ·
    refine ⟨27016423768489059721407863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18010949178992706480938575 27016423768489059721407863)
    ·
      refine ⟨40524635652733589582111795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27016423768489059721407863 40524635652733589582111795)
      ·
        refine ⟨60786953479100384373167693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40524635652733589582111795 60786953479100384373167693)
        ·
          refine ⟨22795107554662644139937885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60786953479100384373167693 22795107554662644139937885)
          ·
            refine ⟨8548165332998491552476707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22795107554662644139937885 8548165332998491552476707)
            ·
              refine ⟨12822247999497737328715061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8548165332998491552476707 12822247999497737328715061)
              ·
                refine ⟨1202085749952912874567037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12822247999497737328715061 1202085749952912874567037)
                ·
                  refine ⟨450782156232342327962639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202085749952912874567037 450782156232342327962639)
                  ·
                    rfl

theorem cell20_987632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_987632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987632 prefixEnd_987632 := by exact prefixLift 987632
  have htrace : WordTrace (prefixWord ++ tailWord_987632) baseStart_987632 baseEnd_987632 := by
    simpa [prefixWord, tailWord_987632, baseEnd_987632] using wordTrace_append hprefix tailTrace_987632
  have hstable : (prefixWord ++ tailWord_987632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987632).length < 2 ^ (prefixWord ++ tailWord_987632).sum := by decide
  have hdescent : baseEnd_987632 < baseStart_987632 := by decide
  rcases family_descends (prefixWord ++ tailWord_987632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987652 : List Nat := [2, 3, 2, 3, 1, 2, 2, 3, 2]
def baseStart_987652 : Nat := 118140960795 + 987652 * 2 ^ 59
def prefixEnd_987652 : Nat := 4983230072969 + 3 ^ 40 * 987652 * 2
def baseEnd_987652 : Nat := 450791284777311147295891

theorem tailTrace_987652 : CollatzResearch.WordTrace tailWord_987652 prefixEnd_987652 450791284777311147295891 := by
  unfold tailWord_987652
  simp only [CollatzResearch.WordTrace]
  refine ⟨18011313908956478188802605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24015085211941970918403473 18011313908956478188802605)
  ·
    refine ⟨6754242715858679320800977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18011313908956478188802605 6754242715858679320800977)
    ·
      refine ⟨5065682036894009490600733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6754242715858679320800977 5065682036894009490600733)
      ·
        refine ⟨1899630763835253558975275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5065682036894009490600733 1899630763835253558975275)
        ·
          refine ⟨2849446145752880338462913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1899630763835253558975275 2849446145752880338462913)
          ·
            refine ⟨2137084609314660253847185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2849446145752880338462913 2137084609314660253847185)
            ·
              refine ⟨1602813456985995190385389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2137084609314660253847185 1602813456985995190385389)
              ·
                refine ⟨601055046369748196394521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1602813456985995190385389 601055046369748196394521)
                ·
                  refine ⟨450791284777311147295891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601055046369748196394521 450791284777311147295891)
                  ·
                    rfl

theorem cell20_987652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_987652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987652 prefixEnd_987652 := by exact prefixLift 987652
  have htrace : WordTrace (prefixWord ++ tailWord_987652) baseStart_987652 baseEnd_987652 := by
    simpa [prefixWord, tailWord_987652, baseEnd_987652] using wordTrace_append hprefix tailTrace_987652
  have hstable : (prefixWord ++ tailWord_987652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987652).length < 2 ^ (prefixWord ++ tailWord_987652).sum := by decide
  have hdescent : baseEnd_987652 < baseStart_987652 := by decide
  rcases family_descends (prefixWord ++ tailWord_987652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987693 : List Nat := [1, 5, 4, 1, 1, 2, 2, 4]
def baseStart_987693 : Nat := 118140960795 + 987693 * 2 ^ 59
def prefixEnd_987693 : Nat := 4983230072969 + 3 ^ 40 * 987693 * 2
def baseEnd_987693 : Nat := 150269999431499075643019

theorem tailTrace_987693 : CollatzResearch.WordTrace tailWord_987693 prefixEnd_987693 150269999431499075643019 := by
  unfold tailWord_987693
  simp only [CollatzResearch.WordTrace]
  refine ⟨36024123210764420379847733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24016082140509613586565155 36024123210764420379847733)
  ·
    refine ⟨3377261551009164410610725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36024123210764420379847733 3377261551009164410610725)
    ·
      refine ⟨633236540814218326989511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3377261551009164410610725 633236540814218326989511)
      ·
        refine ⟨949854811221327490484267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633236540814218326989511 949854811221327490484267)
        ·
          refine ⟨1424782216831991235726401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949854811221327490484267 1424782216831991235726401)
          ·
            refine ⟨1068586662623993426794801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1424782216831991235726401 1068586662623993426794801)
            ·
              refine ⟨801439996967995070096101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1068586662623993426794801 801439996967995070096101)
              ·
                refine ⟨150269999431499075643019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 801439996967995070096101 150269999431499075643019)
                ·
                  rfl

theorem cell20_987693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 4].length) (baseStart_987693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987693 prefixEnd_987693 := by exact prefixLift 987693
  have htrace : WordTrace (prefixWord ++ tailWord_987693) baseStart_987693 baseEnd_987693 := by
    simpa [prefixWord, tailWord_987693, baseEnd_987693] using wordTrace_append hprefix tailTrace_987693
  have hstable : (prefixWord ++ tailWord_987693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987693).length < 2 ^ (prefixWord ++ tailWord_987693).sum := by decide
  have hdescent : baseEnd_987693 < baseStart_987693 := by decide
  rcases family_descends (prefixWord ++ tailWord_987693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987708 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 5]
def baseStart_987708 : Nat := 118140960795 + 987708 * 2 ^ 59
def prefixEnd_987708 : Nat := 4983230072969 + 3 ^ 40 * 987708 * 2
def baseEnd_987708 : Nat := 450816844703223841428995

theorem tailTrace_987708 : CollatzResearch.WordTrace tailWord_987708 prefixEnd_987708 450816844703223841428995 := by
  unfold tailWord_987708
  simp only [CollatzResearch.WordTrace]
  refine ⟨18012335152855038970821889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24016446870473385294429185 18012335152855038970821889)
  ·
    refine ⟨13509251364641279228116417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18012335152855038970821889 13509251364641279228116417)
    ·
      refine ⟨10131938523480959421087313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13509251364641279228116417 10131938523480959421087313)
      ·
        refine ⟨7598953892610719565815485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10131938523480959421087313 7598953892610719565815485)
        ·
          refine ⟨2849607709729019837180807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7598953892610719565815485 2849607709729019837180807)
          ·
            refine ⟨4274411564593529755771211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2849607709729019837180807 4274411564593529755771211)
            ·
              refine ⟨6411617346890294633656817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4274411564593529755771211 6411617346890294633656817)
              ·
                refine ⟨4808713010167720975242613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6411617346890294633656817 4808713010167720975242613)
                ·
                  refine ⟨450816844703223841428995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4808713010167720975242613 450816844703223841428995)
                  ·
                    rfl

theorem cell20_987708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_987708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987708 prefixEnd_987708 := by exact prefixLift 987708
  have htrace : WordTrace (prefixWord ++ tailWord_987708) baseStart_987708 baseEnd_987708 := by
    simpa [prefixWord, tailWord_987708, baseEnd_987708] using wordTrace_append hprefix tailTrace_987708
  have hstable : (prefixWord ++ tailWord_987708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987708).length < 2 ^ (prefixWord ++ tailWord_987708).sum := by decide
  have hdescent : baseEnd_987708 < baseStart_987708 := by decide
  rcases family_descends (prefixWord ++ tailWord_987708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987718 : List Nat := [6, 1, 1, 1, 2, 1, 8]
def baseStart_987718 : Nat := 118140960795 + 987718 * 2 ^ 59
def prefixEnd_987718 : Nat := 4983230072969 + 3 ^ 40 * 987718 * 2
def baseEnd_987718 : Nat := 50091267663967583455069

theorem tailTrace_987718 : CollatzResearch.WordTrace tailWord_987718 prefixEnd_987718 50091267663967583455069 := by
  unfold tailWord_987718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1125782344864807801547119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24016690023782566433005205 1125782344864807801547119)
  ·
    refine ⟨1688673517297211702320679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1125782344864807801547119 1688673517297211702320679)
    ·
      refine ⟨2533010275945817553481019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1688673517297211702320679 2533010275945817553481019)
      ·
        refine ⟨3799515413918726330221529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2533010275945817553481019 3799515413918726330221529)
        ·
          refine ⟨2849636560439044747666147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3799515413918726330221529 2849636560439044747666147)
          ·
            refine ⟨4274454840658567121499221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2849636560439044747666147 4274454840658567121499221)
            ·
              refine ⟨50091267663967583455069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4274454840658567121499221 50091267663967583455069)
              ·
                rfl

theorem cell20_987718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 8].length) (baseStart_987718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987718 prefixEnd_987718 := by exact prefixLift 987718
  have htrace : WordTrace (prefixWord ++ tailWord_987718) baseStart_987718 baseEnd_987718 := by
    simpa [prefixWord, tailWord_987718, baseEnd_987718] using wordTrace_append hprefix tailTrace_987718
  have hstable : (prefixWord ++ tailWord_987718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987718).length < 2 ^ (prefixWord ++ tailWord_987718).sum := by decide
  have hdescent : baseEnd_987718 < baseStart_987718 := by decide
  rcases family_descends (prefixWord ++ tailWord_987718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987722 : List Nat := [3, 1, 2, 1, 1, 4, 8]
def baseStart_987722 : Nat := 118140960795 + 987722 * 2 ^ 59
def prefixEnd_987722 : Nat := 4983230072969 + 3 ^ 40 * 987722 * 2
def baseEnd_987722 : Nat := 50091470520522446106919

theorem tailTrace_987722 : CollatzResearch.WordTrace tailWord_987722 prefixEnd_987722 50091470520522446106919 := by
  unfold tailWord_987722
  simp only [CollatzResearch.WordTrace]
  refine ⟨9006295231914839583163355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24016787285106238888435613 9006295231914839583163355)
  ·
    refine ⟨13509442847872259374745033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9006295231914839583163355 13509442847872259374745033)
    ·
      refine ⟨10132082135904194531058775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13509442847872259374745033 10132082135904194531058775)
      ·
        refine ⟨15198123203856291796588163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10132082135904194531058775 15198123203856291796588163)
        ·
          refine ⟨22797184805784437694882245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15198123203856291796588163 22797184805784437694882245)
          ·
            refine ⟨4274472151084582067790421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22797184805784437694882245 4274472151084582067790421)
            ·
              refine ⟨50091470520522446106919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4274472151084582067790421 50091470520522446106919)
              ·
                rfl

theorem cell20_987722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 8].length) (baseStart_987722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987722 prefixEnd_987722 := by exact prefixLift 987722
  have htrace : WordTrace (prefixWord ++ tailWord_987722) baseStart_987722 baseEnd_987722 := by
    simpa [prefixWord, tailWord_987722, baseEnd_987722] using wordTrace_append hprefix tailTrace_987722
  have hstable : (prefixWord ++ tailWord_987722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987722).length < 2 ^ (prefixWord ++ tailWord_987722).sum := by decide
  have hdescent : baseEnd_987722 < baseStart_987722 := by decide
  rcases family_descends (prefixWord ++ tailWord_987722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987725 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 5]
def baseStart_987725 : Nat := 118140960795 + 987725 * 2 ^ 59
def prefixEnd_987725 : Nat := 4983230072969 + 3 ^ 40 * 987725 * 2
def baseEnd_987725 : Nat := 450824603966447337862259

theorem tailTrace_987725 : CollatzResearch.WordTrace tailWord_987725 prefixEnd_987725 450824603966447337862259 := by
  unfold tailWord_987725
  simp only [CollatzResearch.WordTrace]
  refine ⟨36025290346648489845012629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24016860231098993230008419 36025290346648489845012629)
  ·
    refine ⟨1688685484999147961484967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36025290346648489845012629 1688685484999147961484967)
    ·
      refine ⟨2533028227498721942227451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1688685484999147961484967 2533028227498721942227451)
      ·
        refine ⟨3799542341248082913341177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2533028227498721942227451 3799542341248082913341177)
        ·
          refine ⟨2849656755936062185005883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3799542341248082913341177 2849656755936062185005883)
          ·
            refine ⟨4274485133904093277508825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2849656755936062185005883 4274485133904093277508825)
            ·
              refine ⟨3205863850428069958131619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4274485133904093277508825 3205863850428069958131619)
              ·
                refine ⟨4808795775642104937197429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3205863850428069958131619 4808795775642104937197429)
                ·
                  refine ⟨450824603966447337862259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4808795775642104937197429 450824603966447337862259)
                  ·
                    rfl

theorem cell20_987725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_987725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987725 prefixEnd_987725 := by exact prefixLift 987725
  have htrace : WordTrace (prefixWord ++ tailWord_987725) baseStart_987725 baseEnd_987725 := by
    simpa [prefixWord, tailWord_987725, baseEnd_987725] using wordTrace_append hprefix tailTrace_987725
  have hstable : (prefixWord ++ tailWord_987725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987725).length < 2 ^ (prefixWord ++ tailWord_987725).sum := by decide
  have hdescent : baseEnd_987725 < baseStart_987725 := by decide
  rcases family_descends (prefixWord ++ tailWord_987725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987732 : List Nat := [2, 4, 1, 1, 1, 3, 3, 1, 4]
def baseStart_987732 : Nat := 118140960795 + 987732 * 2 ^ 59
def prefixEnd_987732 : Nat := 4983230072969 + 3 ^ 40 * 987732 * 2
def baseEnd_987732 : Nat := 450827798957186424628897

theorem tailTrace_987732 : CollatzResearch.WordTrace tailWord_987732 prefixEnd_987732 450827798957186424628897 := by
  unfold tailWord_987732
  simp only [CollatzResearch.WordTrace]
  refine ⟨18012772828811565020258725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24017030438415420027011633 18012772828811565020258725)
  ·
    refine ⟨3377394905402168441298511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18012772828811565020258725 3377394905402168441298511)
    ·
      refine ⟨5066092358103252661947767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3377394905402168441298511 5066092358103252661947767)
      ·
        refine ⟨7599138537154878992921651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5066092358103252661947767 7599138537154878992921651)
        ·
          refine ⟨11398707805732318489382477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7599138537154878992921651 11398707805732318489382477)
          ·
            refine ⟨4274515427149619433518429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11398707805732318489382477 4274515427149619433518429)
            ·
              refine ⟨1602943285181107287569411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4274515427149619433518429 1602943285181107287569411)
              ·
                refine ⟨2404414927771660931354117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1602943285181107287569411 2404414927771660931354117)
                ·
                  refine ⟨450827798957186424628897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2404414927771660931354117 450827798957186424628897)
                  ·
                    rfl

theorem cell20_987732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_987732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987732 prefixEnd_987732 := by exact prefixLift 987732
  have htrace : WordTrace (prefixWord ++ tailWord_987732) baseStart_987732 baseEnd_987732 := by
    simpa [prefixWord, tailWord_987732, baseEnd_987732] using wordTrace_append hprefix tailTrace_987732
  have hstable : (prefixWord ++ tailWord_987732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987732).length < 2 ^ (prefixWord ++ tailWord_987732).sum := by decide
  have hdescent : baseEnd_987732 < baseStart_987732 := by decide
  rcases family_descends (prefixWord ++ tailWord_987732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987767 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 7]
def baseStart_987767 : Nat := 118140960795 + 987767 * 2 ^ 59
def prefixEnd_987767 : Nat := 4983230072969 + 3 ^ 40 * 987767 * 2
def baseEnd_987767 : Nat := 450843773910881858462087

theorem tailTrace_987767 : CollatzResearch.WordTrace tailWord_987767 prefixEnd_987767 450843773910881858462087 := by
  unfold tailWord_987767
  simp only [CollatzResearch.WordTrace]
  refine ⟨36026822212496331018041555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24017881474997554012027703 36026822212496331018041555)
  ·
    refine ⟨54040233318744496527062333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36026822212496331018041555 54040233318744496527062333)
    ·
      refine ⟨20265087494529186197648375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54040233318744496527062333 20265087494529186197648375)
      ·
        refine ⟨30397631241793779296472563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20265087494529186197648375 30397631241793779296472563)
        ·
          refine ⟨45596446862690668944708845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30397631241793779296472563 45596446862690668944708845)
          ·
            refine ⟨17098667573509000854265817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45596446862690668944708845 17098667573509000854265817)
            ·
              refine ⟨12824000680131750640699363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17098667573509000854265817 12824000680131750640699363)
              ·
                refine ⟨19236001020197625961049045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12824000680131750640699363 19236001020197625961049045)
                ·
                  refine ⟨450843773910881858462087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19236001020197625961049045 450843773910881858462087)
                  ·
                    rfl

theorem cell20_987767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_987767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987767 prefixEnd_987767 := by exact prefixLift 987767
  have htrace : WordTrace (prefixWord ++ tailWord_987767) baseStart_987767 baseEnd_987767 := by
    simpa [prefixWord, tailWord_987767, baseEnd_987767] using wordTrace_append hprefix tailTrace_987767
  have hstable : (prefixWord ++ tailWord_987767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987767).length < 2 ^ (prefixWord ++ tailWord_987767).sum := by decide
  have hdescent : baseEnd_987767 < baseStart_987767 := by decide
  rcases family_descends (prefixWord ++ tailWord_987767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987794 : List Nat := [3, 2, 3, 1, 2, 3, 1, 5]
def baseStart_987794 : Nat := 118140960795 + 987794 * 2 ^ 59
def prefixEnd_987794 : Nat := 4983230072969 + 3 ^ 40 * 987794 * 2
def baseEnd_987794 : Nat := 150285365815529921520659

theorem tailTrace_987794 : CollatzResearch.WordTrace tailWord_987794 prefixEnd_987794 150285365815529921520659 := by
  unfold tailWord_987794
  simp only [CollatzResearch.WordTrace]
  refine ⟨9006951745849628657318609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24018537988932343086182957 9006951745849628657318609)
  ·
    refine ⟨6755213809387221492988957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9006951745849628657318609 6755213809387221492988957)
    ·
      refine ⟨2533205178520208059870859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6755213809387221492988957 2533205178520208059870859)
      ·
        refine ⟨3799807767780312089806289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2533205178520208059870859 3799807767780312089806289)
        ·
          refine ⟨2849855825835234067354717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3799807767780312089806289 2849855825835234067354717)
          ·
            refine ⟨1068695934688212775258019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2849855825835234067354717 1068695934688212775258019)
            ·
              refine ⟨1603043902032319162887029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068695934688212775258019 1603043902032319162887029)
              ·
                refine ⟨150285365815529921520659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1603043902032319162887029 150285365815529921520659)
                ·
                  rfl

theorem cell20_987794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_987794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987794 prefixEnd_987794 := by exact prefixLift 987794
  have htrace : WordTrace (prefixWord ++ tailWord_987794) baseStart_987794 baseEnd_987794 := by
    simpa [prefixWord, tailWord_987794, baseEnd_987794] using wordTrace_append hprefix tailTrace_987794
  have hstable : (prefixWord ++ tailWord_987794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987794).length < 2 ^ (prefixWord ++ tailWord_987794).sum := by decide
  have hdescent : baseEnd_987794 < baseStart_987794 := by decide
  rcases family_descends (prefixWord ++ tailWord_987794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987808 : List Nat := [2, 1, 1, 4, 4, 1, 1, 2, 4]
def baseStart_987808 : Nat := 118140960795 + 987808 * 2 ^ 59
def prefixEnd_987808 : Nat := 4983230072969 + 3 ^ 40 * 987808 * 2
def baseEnd_987808 : Nat := 450862487428067938095253

theorem tailTrace_987808 : CollatzResearch.WordTrace tailWord_987808 prefixEnd_987808 450862487428067938095253 := by
  unfold tailWord_987808
  simp only [CollatzResearch.WordTrace]
  refine ⟨18014158802673897510142039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24018878403565196680189385 18014158802673897510142039)
  ·
    refine ⟨27021238204010846265213059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18014158802673897510142039 27021238204010846265213059)
    ·
      refine ⟨40531857306016269397819589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27021238204010846265213059 40531857306016269397819589)
      ·
        refine ⟨7599723244878050512091173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40531857306016269397819589 7599723244878050512091173)
        ·
          refine ⟨1424948108414634471017095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7599723244878050512091173 1424948108414634471017095)
          ·
            refine ⟨2137422162621951706525643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424948108414634471017095 2137422162621951706525643)
            ·
              refine ⟨3206133243932927559788465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2137422162621951706525643 3206133243932927559788465)
              ·
                refine ⟨2404599932949695669841349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3206133243932927559788465 2404599932949695669841349)
                ·
                  refine ⟨450862487428067938095253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2404599932949695669841349 450862487428067938095253)
                  ·
                    rfl

theorem cell20_987808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_987808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987808 prefixEnd_987808 := by exact prefixLift 987808
  have htrace : WordTrace (prefixWord ++ tailWord_987808) baseStart_987808 baseEnd_987808 := by
    simpa [prefixWord, tailWord_987808, baseEnd_987808] using wordTrace_append hprefix tailTrace_987808
  have hstable : (prefixWord ++ tailWord_987808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987808).length < 2 ^ (prefixWord ++ tailWord_987808).sum := by decide
  have hdescent : baseEnd_987808 < baseStart_987808 := by decide
  rcases family_descends (prefixWord ++ tailWord_987808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987836 : List Nat := [2, 2, 2, 3, 1, 1, 9]
def baseStart_987836 : Nat := 118140960795 + 987836 * 2 ^ 59
def prefixEnd_987836 : Nat := 4983230072969 + 3 ^ 40 * 987836 * 2
def baseEnd_987836 : Nat := 50097251932336031684645

theorem tailTrace_987836 : CollatzResearch.WordTrace tailWord_987836 prefixEnd_987836 50097251932336031684645 := by
  unfold tailWord_987836
  simp only [CollatzResearch.WordTrace]
  refine ⟨18014669424623177901151681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24019559232830903868202241 18014669424623177901151681)
  ·
    refine ⟨13511002068467383425863761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18014669424623177901151681 13511002068467383425863761)
    ·
      refine ⟨10133251551350537569397821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13511002068467383425863761 10133251551350537569397821)
      ·
        refine ⟨3799969331756451588524183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10133251551350537569397821 3799969331756451588524183)
        ·
          refine ⟨5699953997634677382786275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3799969331756451588524183 5699953997634677382786275)
          ·
            refine ⟨8549930996452016074179413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5699953997634677382786275 8549930996452016074179413)
            ·
              refine ⟨50097251932336031684645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8549930996452016074179413 50097251932336031684645)
              ·
                rfl

theorem cell20_987836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 9].length) (baseStart_987836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987836 prefixEnd_987836 := by exact prefixLift 987836
  have htrace : WordTrace (prefixWord ++ tailWord_987836) baseStart_987836 baseEnd_987836 := by
    simpa [prefixWord, tailWord_987836, baseEnd_987836] using wordTrace_append hprefix tailTrace_987836
  have hstable : (prefixWord ++ tailWord_987836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987836).length < 2 ^ (prefixWord ++ tailWord_987836).sum := by decide
  have hdescent : baseEnd_987836 < baseStart_987836 := by decide
  rcases family_descends (prefixWord ++ tailWord_987836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987839 : List Nat := [1, 1, 2, 2, 2, 6, 1, 2, 3]
def baseStart_987839 : Nat := 118140960795 + 987839 * 2 ^ 59
def prefixEnd_987839 : Nat := 4983230072969 + 3 ^ 40 * 987839 * 2
def baseEnd_987839 : Nat := 450876636672769608061793

theorem tailTrace_987839 : CollatzResearch.WordTrace tailWord_987839 prefixEnd_987839 450876636672769608061793 := by
  unfold tailWord_987839
  simp only [CollatzResearch.WordTrace]
  refine ⟨36029448268235487314662571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24019632178823658209775047 36029448268235487314662571)
  ·
    refine ⟨54044172402353230971993857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36029448268235487314662571 54044172402353230971993857)
    ·
      refine ⟨40533129301764923228995393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54044172402353230971993857 40533129301764923228995393)
      ·
        refine ⟨30399846976323692421746545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40533129301764923228995393 30399846976323692421746545)
        ·
          refine ⟨22799885232242769316309909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30399846976323692421746545 22799885232242769316309909)
          ·
            refine ⟨1068744620261379811702027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22799885232242769316309909 1068744620261379811702027)
            ·
              refine ⟨1603116930392069717553041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068744620261379811702027 1603116930392069717553041)
              ·
                refine ⟨1202337697794052288164781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1603116930392069717553041 1202337697794052288164781)
                ·
                  refine ⟨450876636672769608061793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202337697794052288164781 450876636672769608061793)
                  ·
                    rfl

theorem cell20_987839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 3].length) (baseStart_987839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987839 prefixEnd_987839 := by exact prefixLift 987839
  have htrace : WordTrace (prefixWord ++ tailWord_987839) baseStart_987839 baseEnd_987839 := by
    simpa [prefixWord, tailWord_987839, baseEnd_987839] using wordTrace_append hprefix tailTrace_987839
  have hstable : (prefixWord ++ tailWord_987839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987839).length < 2 ^ (prefixWord ++ tailWord_987839).sum := by decide
  have hdescent : baseEnd_987839 < baseStart_987839 := by decide
  rcases family_descends (prefixWord ++ tailWord_987839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987880 : List Nat := [2, 1, 4, 1, 4, 2, 1, 3, 2]
def baseStart_987880 : Nat := 118140960795 + 987880 * 2 ^ 59
def prefixEnd_987880 : Nat := 4983230072969 + 3 ^ 40 * 987880 * 2
def baseEnd_987880 : Nat := 450895350189955687694959

theorem tailTrace_987880 : CollatzResearch.WordTrace tailWord_987880 prefixEnd_987880 450895350189955687694959 := by
  unfold tailWord_987880
  simp only [CollatzResearch.WordTrace]
  refine ⟨18015471830543475658452547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24020629107391300877936729 18015471830543475658452547)
  ·
    refine ⟨27023207745815213487678821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18015471830543475658452547 27023207745815213487678821)
    ·
      refine ⟨5066851452340352528939779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27023207745815213487678821 5066851452340352528939779)
      ·
        refine ⟨7600277178510528793409669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5066851452340352528939779 7600277178510528793409669)
        ·
          refine ⟨1425051970970724148764313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7600277178510528793409669 1425051970970724148764313)
          ·
            refine ⟨1068788978228043111573235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1425051970970724148764313 1068788978228043111573235)
            ·
              refine ⟨1603183467342064667359853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068788978228043111573235 1603183467342064667359853)
              ·
                refine ⟨601193800253274250259945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1603183467342064667359853 601193800253274250259945)
                ·
                  refine ⟨450895350189955687694959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601193800253274250259945 450895350189955687694959)
                  ·
                    rfl

theorem cell20_987880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 2].length) (baseStart_987880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987880 prefixEnd_987880 := by exact prefixLift 987880
  have htrace : WordTrace (prefixWord ++ tailWord_987880) baseStart_987880 baseEnd_987880 := by
    simpa [prefixWord, tailWord_987880, baseEnd_987880] using wordTrace_append hprefix tailTrace_987880
  have hstable : (prefixWord ++ tailWord_987880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987880).length < 2 ^ (prefixWord ++ tailWord_987880).sum := by decide
  have hdescent : baseEnd_987880 < baseStart_987880 := by decide
  rcases family_descends (prefixWord ++ tailWord_987880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987881 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 5]
def baseStart_987881 : Nat := 118140960795 + 987881 * 2 ^ 59
def prefixEnd_987881 : Nat := 4983230072969 + 3 ^ 40 * 987881 * 2
def baseEnd_987881 : Nat := 450895806617204128661621

theorem tailTrace_987881 : CollatzResearch.WordTrace tailWord_987881 prefixEnd_987881 450895806617204128661621 := by
  unfold tailWord_987881
  simp only [CollatzResearch.WordTrace]
  refine ⟨36030980134083328487691497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24020653422722218991794331 36030980134083328487691497)
  ·
    refine ⟨27023235100562496365768623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36030980134083328487691497 27023235100562496365768623)
    ·
      refine ⟨40534852650843744548652935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27023235100562496365768623 40534852650843744548652935)
      ·
        refine ⟨60802278976265616822979403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40534852650843744548652935 60802278976265616822979403)
        ·
          refine ⟨91203418464398425234469105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60802278976265616822979403 91203418464398425234469105)
          ·
            refine ⟨68402563848298818925851829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91203418464398425234469105 68402563848298818925851829)
            ·
              refine ⟨6412740360778014274298609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68402563848298818925851829 6412740360778014274298609)
              ·
                refine ⟨4809555270583510705723957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6412740360778014274298609 4809555270583510705723957)
                ·
                  refine ⟨450895806617204128661621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4809555270583510705723957 450895806617204128661621)
                  ·
                    rfl

theorem cell20_987881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_987881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987881 prefixEnd_987881 := by exact prefixLift 987881
  have htrace : WordTrace (prefixWord ++ tailWord_987881) baseStart_987881 baseEnd_987881 := by
    simpa [prefixWord, tailWord_987881, baseEnd_987881] using wordTrace_append hprefix tailTrace_987881
  have hstable : (prefixWord ++ tailWord_987881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987881).length < 2 ^ (prefixWord ++ tailWord_987881).sum := by decide
  have hdescent : baseEnd_987881 < baseStart_987881 := by decide
  rcases family_descends (prefixWord ++ tailWord_987881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987901 : List Nat := [1, 4, 1, 1, 1, 1, 7, 2, 2]
def baseStart_987901 : Nat := 118140960795 + 987901 * 2 ^ 59
def prefixEnd_987901 : Nat := 4983230072969 + 3 ^ 40 * 987901 * 2
def baseEnd_987901 : Nat := 450904935162172947994873

theorem tailTrace_987901 : CollatzResearch.WordTrace tailWord_987901 prefixEnd_987901 450904935162172947994873 := by
  unfold tailWord_987901
  simp only [CollatzResearch.WordTrace]
  refine ⟨36031709594010871903419557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24021139729340581268946371 36031709594010871903419557)
  ·
    refine ⟨6755945548877038481891167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36031709594010871903419557 6755945548877038481891167)
    ·
      refine ⟨10133918323315557722836751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6755945548877038481891167 10133918323315557722836751)
      ·
        refine ⟨15200877484973336584255127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10133918323315557722836751 15200877484973336584255127)
        ·
          refine ⟨22801316227460004876382691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15200877484973336584255127 22801316227460004876382691)
          ·
            refine ⟨34201974341190007314574037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22801316227460004876382691 34201974341190007314574037)
            ·
              refine ⟨801608773621640796435329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 34201974341190007314574037 801608773621640796435329)
              ·
                refine ⟨601206580216230597326497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 801608773621640796435329 601206580216230597326497)
                ·
                  refine ⟨450904935162172947994873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601206580216230597326497 450904935162172947994873)
                  ·
                    rfl

theorem cell20_987901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_987901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987901 prefixEnd_987901 := by exact prefixLift 987901
  have htrace : WordTrace (prefixWord ++ tailWord_987901) baseStart_987901 baseEnd_987901 := by
    simpa [prefixWord, tailWord_987901, baseEnd_987901] using wordTrace_append hprefix tailTrace_987901
  have hstable : (prefixWord ++ tailWord_987901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987901).length < 2 ^ (prefixWord ++ tailWord_987901).sum := by decide
  have hdescent : baseEnd_987901 < baseStart_987901 := by decide
  rcases family_descends (prefixWord ++ tailWord_987901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987912 : List Nat := [2, 1, 3, 2, 2, 2, 1, 7]
def baseStart_987912 : Nat := 118140960795 + 987912 * 2 ^ 59
def prefixEnd_987912 : Nat := 4983230072969 + 3 ^ 40 * 987912 * 2
def baseEnd_987912 : Nat := 150303318620635266209387

theorem tailTrace_987912 : CollatzResearch.WordTrace tailWord_987912 prefixEnd_987912 150303318620635266209387 := by
  unfold tailWord_987912
  simp only [CollatzResearch.WordTrace]
  refine ⟨18016055398485510391034995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24021407197980680521379993 18016055398485510391034995)
  ·
    refine ⟨27024083097728265586552493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18016055398485510391034995 27024083097728265586552493)
    ·
      refine ⟨10134031161648099594957185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27024083097728265586552493 10134031161648099594957185)
      ·
        refine ⟨7600523371236074696217889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10134031161648099594957185 7600523371236074696217889)
        ·
          refine ⟨5700392528427056022163417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7600523371236074696217889 5700392528427056022163417)
          ·
            refine ⟨4275294396320292016622563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5700392528427056022163417 4275294396320292016622563)
            ·
              refine ⟨6412941594480438024933845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4275294396320292016622563 6412941594480438024933845)
              ·
                refine ⟨150303318620635266209387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6412941594480438024933845 150303318620635266209387)
                ·
                  rfl

theorem cell20_987912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_987912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987912 prefixEnd_987912 := by exact prefixLift 987912
  have htrace : WordTrace (prefixWord ++ tailWord_987912) baseStart_987912 baseEnd_987912 := by
    simpa [prefixWord, tailWord_987912, baseEnd_987912] using wordTrace_append hprefix tailTrace_987912
  have hstable : (prefixWord ++ tailWord_987912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987912).length < 2 ^ (prefixWord ++ tailWord_987912).sum := by decide
  have hdescent : baseEnd_987912 < baseStart_987912 := by decide
  rcases family_descends (prefixWord ++ tailWord_987912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987946 : List Nat := [3, 1, 4, 3, 2, 7]
def baseStart_987946 : Nat := 118140960795 + 987946 * 2 ^ 59
def prefixEnd_987946 : Nat := 4983230072969 + 3 ^ 40 * 987946 * 2
def baseEnd_987946 : Nat := 16700943495864918203507

theorem tailTrace_987946 : CollatzResearch.WordTrace tailWord_987946 prefixEnd_987946 16700943495864918203507 := by
  unfold tailWord_987946
  simp only [CollatzResearch.WordTrace]
  refine ⟨9008337719711961147201923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24022233919231896392538461 9008337719711961147201923)
  ·
    refine ⟨13512506579567941720802885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9008337719711961147201923 13512506579567941720802885)
    ·
      refine ⟨2533594983668989072650541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13512506579567941720802885 2533594983668989072650541)
      ·
        refine ⟨950098118875870902243953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2533594983668989072650541 950098118875870902243953)
        ·
          refine ⟨712573589156903176682965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 950098118875870902243953 712573589156903176682965)
          ·
            refine ⟨16700943495864918203507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 712573589156903176682965 16700943495864918203507)
            ·
              rfl

theorem cell20_987946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 7].length) (baseStart_987946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987946 prefixEnd_987946 := by exact prefixLift 987946
  have htrace : WordTrace (prefixWord ++ tailWord_987946) baseStart_987946 baseEnd_987946 := by
    simpa [prefixWord, tailWord_987946, baseEnd_987946] using wordTrace_append hprefix tailTrace_987946
  have hstable : (prefixWord ++ tailWord_987946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987946).length < 2 ^ (prefixWord ++ tailWord_987946).sum := by decide
  have hdescent : baseEnd_987946 < baseStart_987946 := by decide
  rcases family_descends (prefixWord ++ tailWord_987946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987949 : List Nat := [1, 5, 3, 2, 1, 1, 2, 2, 3]
def baseStart_987949 : Nat := 118140960795 + 987949 * 2 ^ 59
def prefixEnd_987949 : Nat := 4983230072969 + 3 ^ 40 * 987949 * 2
def baseEnd_987949 : Nat := 450926843670098114394677

theorem tailTrace_987949 : CollatzResearch.WordTrace tailWord_987949 prefixEnd_987949 450926843670098114394677 := by
  unfold tailWord_987949
  simp only [CollatzResearch.WordTrace]
  refine ⟨36033460297836976101166901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24022306865224650734111267 36033460297836976101166901)
  ·
    refine ⟨3378136902922216509484397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36033460297836976101166901 3378136902922216509484397)
    ·
      refine ⟨1266801338595831191056649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3378136902922216509484397 1266801338595831191056649)
      ·
        refine ⟨950101003946873393292487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1266801338595831191056649 950101003946873393292487)
        ·
          refine ⟨1425151505920310089938731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 950101003946873393292487 1425151505920310089938731)
          ·
            refine ⟨2137727258880465134908097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1425151505920310089938731 2137727258880465134908097)
            ·
              refine ⟨1603295444160348851181073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2137727258880465134908097 1603295444160348851181073)
              ·
                refine ⟨1202471583120261638385805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1603295444160348851181073 1202471583120261638385805)
                ·
                  refine ⟨450926843670098114394677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202471583120261638385805 450926843670098114394677)
                  ·
                    rfl

theorem cell20_987949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_987949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987949 prefixEnd_987949 := by exact prefixLift 987949
  have htrace : WordTrace (prefixWord ++ tailWord_987949) baseStart_987949 baseEnd_987949 := by
    simpa [prefixWord, tailWord_987949, baseEnd_987949] using wordTrace_append hprefix tailTrace_987949
  have hstable : (prefixWord ++ tailWord_987949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987949).length < 2 ^ (prefixWord ++ tailWord_987949).sum := by decide
  have hdescent : baseEnd_987949 < baseStart_987949 := by decide
  rcases family_descends (prefixWord ++ tailWord_987949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987956 : List Nat := [2, 5, 1, 1, 3, 1, 1, 4, 2]
def baseStart_987956 : Nat := 118140960795 + 987956 * 2 ^ 59
def prefixEnd_987956 : Nat := 4983230072969 + 3 ^ 40 * 987956 * 2
def baseEnd_987956 : Nat := 450930038660837201161315

theorem tailTrace_987956 : CollatzResearch.WordTrace tailWord_987956 prefixEnd_987956 450930038660837201161315 := by
  unfold tailWord_987956
  simp only [CollatzResearch.WordTrace]
  refine ⟨18016857804405808148335861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24022477072541077531114481 18016857804405808148335861)
  ·
    refine ⟨1689080419163044513906487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18016857804405808148335861 1689080419163044513906487)
    ·
      refine ⟨2533620628744566770859731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1689080419163044513906487 2533620628744566770859731)
      ·
        refine ⟨3800430943116850156289597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2533620628744566770859731 3800430943116850156289597)
        ·
          refine ⟨1425161603668818808608599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3800430943116850156289597 1425161603668818808608599)
          ·
            refine ⟨2137742405503228212912899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1425161603668818808608599 2137742405503228212912899)
            ·
              refine ⟨3206613608254842319369349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2137742405503228212912899 3206613608254842319369349)
              ·
                refine ⟨601240051547782934881753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3206613608254842319369349 601240051547782934881753)
                ·
                  refine ⟨450930038660837201161315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601240051547782934881753 450930038660837201161315)
                  ·
                    rfl

theorem cell20_987956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_987956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987956 prefixEnd_987956 := by exact prefixLift 987956
  have htrace : WordTrace (prefixWord ++ tailWord_987956) baseStart_987956 baseEnd_987956 := by
    simpa [prefixWord, tailWord_987956, baseEnd_987956] using wordTrace_append hprefix tailTrace_987956
  have hstable : (prefixWord ++ tailWord_987956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987956).length < 2 ^ (prefixWord ++ tailWord_987956).sum := by decide
  have hdescent : baseEnd_987956 < baseStart_987956 := by decide
  rcases family_descends (prefixWord ++ tailWord_987956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987960 : List Nat := [2, 1, 2, 1, 3, 2, 3, 4, 2]
def baseStart_987960 : Nat := 118140960795 + 987960 * 2 ^ 59
def prefixEnd_987960 : Nat := 4983230072969 + 3 ^ 40 * 987960 * 2
def baseEnd_987960 : Nat := 450931864369830965027965

theorem tailTrace_987960 : CollatzResearch.WordTrace tailWord_987960 prefixEnd_987960 450931864369830965027965 := by
  unfold tailWord_987960
  simp only [CollatzResearch.WordTrace]
  refine ⟨18016930750398562489908667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24022574333864749986544889 18016930750398562489908667)
  ·
    refine ⟨27025396125597843734863001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18016930750398562489908667 27025396125597843734863001)
    ·
      refine ⟨20269047094198382801147251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27025396125597843734863001 20269047094198382801147251)
      ·
        refine ⟨30403570641297574201720877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20269047094198382801147251 30403570641297574201720877)
        ·
          refine ⟨11401338990486590325645329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30403570641297574201720877 11401338990486590325645329)
          ·
            refine ⟨8551004242864942744233997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11401338990486590325645329 8551004242864942744233997)
            ·
              refine ⟨3206626591074353529087749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8551004242864942744233997 3206626591074353529087749)
              ·
                refine ⟨601242485826441286703953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3206626591074353529087749 601242485826441286703953)
                ·
                  refine ⟨450931864369830965027965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601242485826441286703953 450931864369830965027965)
                  ·
                    rfl

theorem cell20_987960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 2].length) (baseStart_987960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987960 prefixEnd_987960 := by exact prefixLift 987960
  have htrace : WordTrace (prefixWord ++ tailWord_987960) baseStart_987960 baseEnd_987960 := by
    simpa [prefixWord, tailWord_987960, baseEnd_987960] using wordTrace_append hprefix tailTrace_987960
  have hstable : (prefixWord ++ tailWord_987960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987960).length < 2 ^ (prefixWord ++ tailWord_987960).sum := by decide
  have hdescent : baseEnd_987960 < baseStart_987960 := by decide
  rcases family_descends (prefixWord ++ tailWord_987960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_987967 : List Nat := [1, 1, 2, 2, 5, 3, 1, 5]
def baseStart_987967 : Nat := 118140960795 + 987967 * 2 ^ 59
def prefixEnd_987967 : Nat := 4983230072969 + 3 ^ 40 * 987967 * 2
def baseEnd_987967 : Nat := 150311686453523350598201

theorem tailTrace_987967 : CollatzResearch.WordTrace tailWord_987967 prefixEnd_987967 150311686453523350598201 := by
  unfold tailWord_987967
  simp only [CollatzResearch.WordTrace]
  refine ⟨36034116811771765175322155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24022744541181176783548103 36034116811771765175322155)
  ·
    refine ⟨54051175217657647762983233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36034116811771765175322155 54051175217657647762983233)
    ·
      refine ⟨40538381413243235822237425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54051175217657647762983233 40538381413243235822237425)
      ·
        refine ⟨30403786059932426866678069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40538381413243235822237425 30403786059932426866678069)
        ·
          refine ⟨2850354943118665018751069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30403786059932426866678069 2850354943118665018751069)
          ·
            refine ⟨1068883103669499382031651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2850354943118665018751069 1068883103669499382031651)
            ·
              refine ⟨1603324655504249073047477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068883103669499382031651 1603324655504249073047477)
              ·
                refine ⟨150311686453523350598201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1603324655504249073047477 150311686453523350598201)
                ·
                  rfl

theorem cell20_987967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 5].length) (baseStart_987967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_987967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_987967 prefixEnd_987967 := by exact prefixLift 987967
  have htrace : WordTrace (prefixWord ++ tailWord_987967) baseStart_987967 baseEnd_987967 := by
    simpa [prefixWord, tailWord_987967, baseEnd_987967] using wordTrace_append hprefix tailTrace_987967
  have hstable : (prefixWord ++ tailWord_987967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_987967).length < 2 ^ (prefixWord ++ tailWord_987967).sum := by decide
  have hdescent : baseEnd_987967 < baseStart_987967 := by decide
  rcases family_descends (prefixWord ++ tailWord_987967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988053 : List Nat := [1, 3, 2, 1, 1, 6, 1, 3, 2]
def baseStart_988053 : Nat := 118140960795 + 988053 * 2 ^ 59
def prefixEnd_988053 : Nat := 4983230072969 + 3 ^ 40 * 988053 * 2
def baseEnd_988053 : Nat := 450974312103935974927585

theorem tailTrace_988053 : CollatzResearch.WordTrace tailWord_988053 prefixEnd_988053 450974312103935974927585 := by
  unfold tailWord_988053
  simp only [CollatzResearch.WordTrace]
  refine ⟨36037253489460201862952813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24024835659640134575301875 36037253489460201862952813)
  ·
    refine ⟨13513970058547575698607305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36037253489460201862952813 13513970058547575698607305)
    ·
      refine ⟨10135477543910681773955479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13513970058547575698607305 10135477543910681773955479)
      ·
        refine ⟨15203216315866022660933219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10135477543910681773955479 15203216315866022660933219)
        ·
          refine ⟨22804824473799033991399829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15203216315866022660933219 22804824473799033991399829)
          ·
            refine ⟨1068976147209329718346867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22804824473799033991399829 1068976147209329718346867)
            ·
              refine ⟨1603464220813994577520301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068976147209329718346867 1603464220813994577520301)
              ·
                refine ⟨601299082805247966570113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1603464220813994577520301 601299082805247966570113)
                ·
                  refine ⟨450974312103935974927585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601299082805247966570113 450974312103935974927585)
                  ·
                    rfl

theorem cell20_988053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_988053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988053 prefixEnd_988053 := by exact prefixLift 988053
  have htrace : WordTrace (prefixWord ++ tailWord_988053) baseStart_988053 baseEnd_988053 := by
    simpa [prefixWord, tailWord_988053, baseEnd_988053] using wordTrace_append hprefix tailTrace_988053
  have hstable : (prefixWord ++ tailWord_988053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988053).length < 2 ^ (prefixWord ++ tailWord_988053).sum := by decide
  have hdescent : baseEnd_988053 < baseStart_988053 := by decide
  rcases family_descends (prefixWord ++ tailWord_988053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988060 : List Nat := [2, 2, 3, 3, 3, 1, 6]
def baseStart_988060 : Nat := 118140960795 + 988060 * 2 ^ 59
def prefixEnd_988060 : Nat := 4983230072969 + 3 ^ 40 * 988060 * 2
def baseEnd_988060 : Nat := 50108611899408340188247

theorem tailTrace_988060 : CollatzResearch.WordTrace tailWord_988060 prefixEnd_988060 50108611899408340188247 := by
  unfold tailWord_988060
  simp only [CollatzResearch.WordTrace]
  refine ⟨18018754400217421029228817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24025005866956561372305089 18018754400217421029228817)
  ·
    refine ⟨13514065800163065771921613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18018754400217421029228817 13514065800163065771921613)
    ·
      refine ⟨5067774675061149664470605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13514065800163065771921613 5067774675061149664470605)
      ·
        refine ⟨1900415503147931124176477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5067774675061149664470605 1900415503147931124176477)
        ·
          refine ⟨712655813680474171566179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1900415503147931124176477 712655813680474171566179)
          ·
            refine ⟨1068983720520711257349269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712655813680474171566179 1068983720520711257349269)
            ·
              refine ⟨50108611899408340188247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1068983720520711257349269 50108611899408340188247)
              ·
                rfl

theorem cell20_988060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 6].length) (baseStart_988060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988060 prefixEnd_988060 := by exact prefixLift 988060
  have htrace : WordTrace (prefixWord ++ tailWord_988060) baseStart_988060 baseEnd_988060 := by
    simpa [prefixWord, tailWord_988060, baseEnd_988060] using wordTrace_append hprefix tailTrace_988060
  have hstable : (prefixWord ++ tailWord_988060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988060).length < 2 ^ (prefixWord ++ tailWord_988060).sum := by decide
  have hdescent : baseEnd_988060 < baseStart_988060 := by decide
  rcases family_descends (prefixWord ++ tailWord_988060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988081 : List Nat := [1, 2, 2, 4, 3, 1, 2, 5]
def baseStart_988081 : Nat := 118140960795 + 988081 * 2 ^ 59
def prefixEnd_988081 : Nat := 4983230072969 + 3 ^ 40 * 988081 * 2
def baseEnd_988081 : Nat := 150329030688964107331379

theorem tailTrace_988081 : CollatzResearch.WordTrace tailWord_988081 prefixEnd_988081 150329030688964107331379 := by
  unfold tailWord_988081
  simp only [CollatzResearch.WordTrace]
  refine ⟨36038274733358762644972097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24025516488905841763314731 36038274733358762644972097)
  ·
    refine ⟨27028706050019071983729073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36038274733358762644972097 27028706050019071983729073)
    ·
      refine ⟨20271529537514303987796805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27028706050019071983729073 20271529537514303987796805)
      ·
        refine ⟨3800911788283931997711901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20271529537514303987796805 3800911788283931997711901)
        ·
          refine ⟨1425341920606474499141963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3800911788283931997711901 1425341920606474499141963)
          ·
            refine ⟨2138012880909711748712945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1425341920606474499141963 2138012880909711748712945)
            ·
              refine ⟨1603509660682283811534709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2138012880909711748712945 1603509660682283811534709)
              ·
                refine ⟨150329030688964107331379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1603509660682283811534709 150329030688964107331379)
                ·
                  rfl

theorem cell20_988081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 5].length) (baseStart_988081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988081 prefixEnd_988081 := by exact prefixLift 988081
  have htrace : WordTrace (prefixWord ++ tailWord_988081) baseStart_988081 baseEnd_988081 := by
    simpa [prefixWord, tailWord_988081, baseEnd_988081] using wordTrace_append hprefix tailTrace_988081
  have hstable : (prefixWord ++ tailWord_988081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988081).length < 2 ^ (prefixWord ++ tailWord_988081).sum := by decide
  have hdescent : baseEnd_988081 < baseStart_988081 := by decide
  rcases family_descends (prefixWord ++ tailWord_988081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988084 : List Nat := [2, 5, 2, 1, 1, 2, 1, 3, 3]
def baseStart_988084 : Nat := 118140960795 + 988084 * 2 ^ 59
def prefixEnd_988084 : Nat := 4983230072969 + 3 ^ 40 * 988084 * 2
def baseEnd_988084 : Nat := 450988461348637644894125

theorem tailTrace_988084 : CollatzResearch.WordTrace tailWord_988084 prefixEnd_988084 450988461348637644894125 := by
  unfold tailWord_988084
  simp only [CollatzResearch.WordTrace]
  refine ⟨18019192076173947078665653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24025589434898596104887537 18019192076173947078665653)
  ·
    refine ⟨1689299257141307538624905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18019192076173947078665653 1689299257141307538624905)
    ·
      refine ⟨1266974442855980653968679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1689299257141307538624905 1266974442855980653968679)
      ·
        refine ⟨1900461664283970980953019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1266974442855980653968679 1900461664283970980953019)
        ·
          refine ⟨2850692496425956471429529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900461664283970980953019 2850692496425956471429529)
          ·
            refine ⟨2138019372319467353572147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2850692496425956471429529 2138019372319467353572147)
            ·
              refine ⟨3207029058479201030358221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2138019372319467353572147 3207029058479201030358221)
              ·
                refine ⟨1202635896929700386384333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3207029058479201030358221 1202635896929700386384333)
                ·
                  refine ⟨450988461348637644894125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202635896929700386384333 450988461348637644894125)
                  ·
                    rfl

theorem cell20_988084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_988084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988084 prefixEnd_988084 := by exact prefixLift 988084
  have htrace : WordTrace (prefixWord ++ tailWord_988084) baseStart_988084 baseEnd_988084 := by
    simpa [prefixWord, tailWord_988084, baseEnd_988084] using wordTrace_append hprefix tailTrace_988084
  have hstable : (prefixWord ++ tailWord_988084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988084).length < 2 ^ (prefixWord ++ tailWord_988084).sum := by decide
  have hdescent : baseEnd_988084 < baseStart_988084 := by decide
  rcases family_descends (prefixWord ++ tailWord_988084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988088 : List Nat := [2, 1, 2, 1, 2, 5, 1, 3, 3]
def baseStart_988088 : Nat := 118140960795 + 988088 * 2 ^ 59
def prefixEnd_988088 : Nat := 4983230072969 + 3 ^ 40 * 988088 * 2
def baseEnd_988088 : Nat := 450990287057631408760775

theorem tailTrace_988088 : CollatzResearch.WordTrace tailWord_988088 prefixEnd_988088 450990287057631408760775 := by
  unfold tailWord_988088
  simp only [CollatzResearch.WordTrace]
  refine ⟨18019265022166701420238459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24025686696222268560317945 18019265022166701420238459)
  ·
    refine ⟨27028897533250052130357689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18019265022166701420238459 27028897533250052130357689)
    ·
      refine ⟨20271673149937539097768267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27028897533250052130357689 20271673149937539097768267)
      ·
        refine ⟨30407509724906308646652401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20271673149937539097768267 30407509724906308646652401)
        ·
          refine ⟨22805632293679731484989301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30407509724906308646652401 22805632293679731484989301)
          ·
            refine ⟨2138028027532474826717747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22805632293679731484989301 2138028027532474826717747)
            ·
              refine ⟨3207042041298712240076621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2138028027532474826717747 3207042041298712240076621)
              ·
                refine ⟨1202640765487017090028733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3207042041298712240076621 1202640765487017090028733)
                ·
                  refine ⟨450990287057631408760775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202640765487017090028733 450990287057631408760775)
                  ·
                    rfl

theorem cell20_988088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_988088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988088 prefixEnd_988088 := by exact prefixLift 988088
  have htrace : WordTrace (prefixWord ++ tailWord_988088) baseStart_988088 baseEnd_988088 := by
    simpa [prefixWord, tailWord_988088, baseEnd_988088] using wordTrace_append hprefix tailTrace_988088
  have hstable : (prefixWord ++ tailWord_988088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988088).length < 2 ^ (prefixWord ++ tailWord_988088).sum := by decide
  have hdescent : baseEnd_988088 < baseStart_988088 := by decide
  rcases family_descends (prefixWord ++ tailWord_988088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988150 : List Nat := [5, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_988150 : Nat := 118140960795 + 988150 * 2 ^ 59
def prefixEnd_988150 : Nat := 4983230072969 + 3 ^ 40 * 988150 * 2
def baseEnd_988150 : Nat := 451018585547034748693855

theorem tailTrace_988150 : CollatzResearch.WordTrace tailWord_988150 prefixEnd_988150 451018585547034748693855 := by
  unfold tailWord_988150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2252549460631799214327119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24027194246739191619489269 2252549460631799214327119)
  ·
    refine ⟨3378824190947698821490679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2252549460631799214327119 3378824190947698821490679)
    ·
      refine ⟨5068236286421548232236019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3378824190947698821490679 5068236286421548232236019)
      ·
        refine ⟨7602354429632322348354029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5068236286421548232236019 7602354429632322348354029)
        ·
          refine ⟨2850882911112120880632761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7602354429632322348354029 2850882911112120880632761)
          ·
            refine ⟨2138162183334090660474571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2850882911112120880632761 2138162183334090660474571)
            ·
              refine ⟨3207243275001135990711857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2138162183334090660474571 3207243275001135990711857)
              ·
                refine ⟨2405432456250851993033893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3207243275001135990711857 2405432456250851993033893)
                ·
                  refine ⟨451018585547034748693855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2405432456250851993033893 451018585547034748693855)
                  ·
                    rfl

theorem cell20_988150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_988150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988150 prefixEnd_988150 := by exact prefixLift 988150
  have htrace : WordTrace (prefixWord ++ tailWord_988150) baseStart_988150 baseEnd_988150 := by
    simpa [prefixWord, tailWord_988150, baseEnd_988150] using wordTrace_append hprefix tailTrace_988150
  have hstable : (prefixWord ++ tailWord_988150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988150).length < 2 ^ (prefixWord ++ tailWord_988150).sum := by decide
  have hdescent : baseEnd_988150 < baseStart_988150 := by decide
  rcases family_descends (prefixWord ++ tailWord_988150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988181 : List Nat := [1, 3, 2, 1, 4, 3, 1, 2, 3]
def baseStart_988181 : Nat := 118140960795 + 988181 * 2 ^ 59
def prefixEnd_988181 : Nat := 4983230072969 + 3 ^ 40 * 988181 * 2
def baseEnd_988181 : Nat := 451032734791736418660395

theorem tailTrace_988181 : CollatzResearch.WordTrace tailWord_988181 prefixEnd_988181 451032734791736418660395 := by
  unfold tailWord_988181
  simp only [CollatzResearch.WordTrace]
  refine ⟨36041922032996479723612397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24027948021997653149074931 36041922032996479723612397)
  ·
    refine ⟨13515720762373679896354649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36041922032996479723612397 13515720762373679896354649)
    ·
      refine ⟨10136790571780259922265987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13515720762373679896354649 10136790571780259922265987)
      ·
        refine ⟨15205185857670389883398981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10136790571780259922265987 15205185857670389883398981)
        ·
          refine ⟨2850972348313198103137309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15205185857670389883398981 2850972348313198103137309)
          ·
            refine ⟨1069114630617449288676491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2850972348313198103137309 1069114630617449288676491)
            ·
              refine ⟨1603671945926173933014737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1069114630617449288676491 1603671945926173933014737)
              ·
                refine ⟨1202753959444630449761053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1603671945926173933014737 1202753959444630449761053)
                ·
                  refine ⟨451032734791736418660395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202753959444630449761053 451032734791736418660395)
                  ·
                    rfl

theorem cell20_988181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_988181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988181 prefixEnd_988181 := by exact prefixLift 988181
  have htrace : WordTrace (prefixWord ++ tailWord_988181) baseStart_988181 baseEnd_988181 := by
    simpa [prefixWord, tailWord_988181, baseEnd_988181] using wordTrace_append hprefix tailTrace_988181
  have hstable : (prefixWord ++ tailWord_988181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988181).length < 2 ^ (prefixWord ++ tailWord_988181).sum := by decide
  have hdescent : baseEnd_988181 < baseStart_988181 := by decide
  rcases family_descends (prefixWord ++ tailWord_988181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988188 : List Nat := [2, 2, 3, 1, 4, 1, 2, 1, 4]
def baseStart_988188 : Nat := 118140960795 + 988188 * 2 ^ 59
def prefixEnd_988188 : Nat := 4983230072969 + 3 ^ 40 * 988188 * 2
def baseEnd_988188 : Nat := 451035929782475505427033

theorem tailTrace_988188 : CollatzResearch.WordTrace tailWord_988188 prefixEnd_988188 451035929782475505427033 := by
  unfold tailWord_988188
  simp only [CollatzResearch.WordTrace]
  refine ⟨18021088671985559959558609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24028118229314079946078145 18021088671985559959558609)
  ·
    refine ⟨13515816503989169969668957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18021088671985559959558609 13515816503989169969668957)
    ·
      refine ⟨5068431188995938738625859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13515816503989169969668957 5068431188995938738625859)
      ·
        refine ⟨7602646783493908107938789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5068431188995938738625859 7602646783493908107938789)
        ·
          refine ⟨1425496271905107770238523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7602646783493908107938789 1425496271905107770238523)
          ·
            refine ⟨2138244407857661655357785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1425496271905107770238523 2138244407857661655357785)
            ·
              refine ⟨1603683305893246241518339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2138244407857661655357785 1603683305893246241518339)
              ·
                refine ⟨2405524958839869362277509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1603683305893246241518339 2405524958839869362277509)
                ·
                  refine ⟨451035929782475505427033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2405524958839869362277509 451035929782475505427033)
                  ·
                    rfl

theorem cell20_988188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_988188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988188 prefixEnd_988188 := by exact prefixLift 988188
  have htrace : WordTrace (prefixWord ++ tailWord_988188) baseStart_988188 baseEnd_988188 := by
    simpa [prefixWord, tailWord_988188, baseEnd_988188] using wordTrace_append hprefix tailTrace_988188
  have hstable : (prefixWord ++ tailWord_988188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988188).length < 2 ^ (prefixWord ++ tailWord_988188).sum := by decide
  have hdescent : baseEnd_988188 < baseStart_988188 := by decide
  rcases family_descends (prefixWord ++ tailWord_988188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988212 : List Nat := [2, 5, 1, 2, 1, 1, 4, 4]
def baseStart_988212 : Nat := 118140960795 + 988212 * 2 ^ 59
def prefixEnd_988212 : Nat := 4983230072969 + 3 ^ 40 * 988212 * 2
def baseEnd_988212 : Nat := 150348961345479362875645

theorem tailTrace_988212 : CollatzResearch.WordTrace tailWord_988212 prefixEnd_988212 150348961345479362875645 := by
  unfold tailWord_988212
  simp only [CollatzResearch.WordTrace]
  refine ⟨18021526347942086008995445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24028701797256114678660593 18021526347942086008995445)
  ·
    refine ⟨1689518095119570563343323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18021526347942086008995445 1689518095119570563343323)
    ·
      refine ⟨2534277142679355845014985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1689518095119570563343323 2534277142679355845014985)
      ·
        refine ⟨1900707857009516883761239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2534277142679355845014985 1900707857009516883761239)
        ·
          refine ⟨2851061785514275325641859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900707857009516883761239 2851061785514275325641859)
          ·
            refine ⟨4276592678271412988462789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2851061785514275325641859 4276592678271412988462789)
            ·
              refine ⟨801861127175889935336773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4276592678271412988462789 801861127175889935336773)
              ·
                refine ⟨150348961345479362875645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 801861127175889935336773 150348961345479362875645)
                ·
                  rfl

theorem cell20_988212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_988212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988212 prefixEnd_988212 := by exact prefixLift 988212
  have htrace : WordTrace (prefixWord ++ tailWord_988212) baseStart_988212 baseEnd_988212 := by
    simpa [prefixWord, tailWord_988212, baseEnd_988212] using wordTrace_append hprefix tailTrace_988212
  have hstable : (prefixWord ++ tailWord_988212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988212).length < 2 ^ (prefixWord ++ tailWord_988212).sum := by decide
  have hdescent : baseEnd_988212 < baseStart_988212 := by decide
  rcases family_descends (prefixWord ++ tailWord_988212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988216 : List Nat := [2, 1, 2, 1, 5, 2, 1, 6]
def baseStart_988216 : Nat := 118140960795 + 988216 * 2 ^ 59
def prefixEnd_988216 : Nat := 4983230072969 + 3 ^ 40 * 988216 * 2
def baseEnd_988216 : Nat := 150349569915143950831195

theorem tailTrace_988216 : CollatzResearch.WordTrace tailWord_988216 prefixEnd_988216 150349569915143950831195 := by
  unfold tailWord_988216
  simp only [CollatzResearch.WordTrace]
  refine ⟨18021599293934840350568251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24028799058579787134091001 18021599293934840350568251)
  ·
    refine ⟨27032398940902260525852377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18021599293934840350568251 27032398940902260525852377)
    ·
      refine ⟨20274299205676695394389283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27032398940902260525852377 20274299205676695394389283)
      ·
        refine ⟨30411448808515043091583925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20274299205676695394389283 30411448808515043091583925)
        ·
          refine ⟨2851073325798285289835993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30411448808515043091583925 2851073325798285289835993)
          ·
            refine ⟨2138304994348713967376995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2851073325798285289835993 2138304994348713967376995)
            ·
              refine ⟨3207457491523070951065493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2138304994348713967376995 3207457491523070951065493)
              ·
                refine ⟨150349569915143950831195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3207457491523070951065493 150349569915143950831195)
                ·
                  rfl

theorem cell20_988216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_988216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988216 prefixEnd_988216 := by exact prefixLift 988216
  have htrace : WordTrace (prefixWord ++ tailWord_988216) baseStart_988216 baseEnd_988216 := by
    simpa [prefixWord, tailWord_988216, baseEnd_988216] using wordTrace_append hprefix tailTrace_988216
  have hstable : (prefixWord ++ tailWord_988216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988216).length < 2 ^ (prefixWord ++ tailWord_988216).sum := by decide
  have hdescent : baseEnd_988216 < baseStart_988216 := by decide
  rcases family_descends (prefixWord ++ tailWord_988216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988222 : List Nat := [4, 2, 1, 3, 1, 3, 1, 3, 2]
def baseStart_988222 : Nat := 118140960795 + 988222 * 2 ^ 59
def prefixEnd_988222 : Nat := 4983230072969 + 3 ^ 40 * 988222 * 2
def baseEnd_988222 : Nat := 451051448308922498293561

theorem tailTrace_988222 : CollatzResearch.WordTrace tailWord_988222 prefixEnd_988222 451051448308922498293561 := by
  unfold tailWord_988222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4505427178230992965731865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24028944950565295817236613 4505427178230992965731865)
  ·
    refine ⟨3379070383673244724298899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4505427178230992965731865 3379070383673244724298899)
    ·
      refine ⟨5068605575509867086448349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3379070383673244724298899 5068605575509867086448349)
      ·
        refine ⟨1900727090816200157418131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5068605575509867086448349 1900727090816200157418131)
        ·
          refine ⟨2851090636224300236127197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900727090816200157418131 2851090636224300236127197)
          ·
            refine ⟨1069158988584112588547699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2851090636224300236127197 1069158988584112588547699)
            ·
              refine ⟨1603738482876168882821549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1069158988584112588547699 1603738482876168882821549)
              ·
                refine ⟨601401931078563331058081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1603738482876168882821549 601401931078563331058081)
                ·
                  refine ⟨451051448308922498293561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601401931078563331058081 451051448308922498293561)
                  ·
                    rfl

theorem cell20_988222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_988222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988222 prefixEnd_988222 := by exact prefixLift 988222
  have htrace : WordTrace (prefixWord ++ tailWord_988222) baseStart_988222 baseEnd_988222 := by
    simpa [prefixWord, tailWord_988222, baseEnd_988222] using wordTrace_append hprefix tailTrace_988222
  have hstable : (prefixWord ++ tailWord_988222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988222).length < 2 ^ (prefixWord ++ tailWord_988222).sum := by decide
  have hdescent : baseEnd_988222 < baseStart_988222 := by decide
  rcases family_descends (prefixWord ++ tailWord_988222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988253 : List Nat := [1, 4, 4, 1, 2, 2, 2, 1, 3]
def baseStart_988253 : Nat := 118140960795 + 988253 * 2 ^ 59
def prefixEnd_988253 : Nat := 4983230072969 + 3 ^ 40 * 988253 * 2
def baseEnd_988253 : Nat := 451065597553624168260101

theorem tailTrace_988253 : CollatzResearch.WordTrace tailWord_988253 prefixEnd_988253 451065597553624168260101 := by
  unfold tailWord_988253
  simp only [CollatzResearch.WordTrace]
  refine ⟨36044548088735636020233413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24029698725823757346822275 36044548088735636020233413)
  ·
    refine ⟨6758352766637931753793765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36044548088735636020233413 6758352766637931753793765)
    ·
      refine ⟨1267191143744612203836331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6758352766637931753793765 1267191143744612203836331)
      ·
        refine ⟨1900786715616918305754497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1267191143744612203836331 1900786715616918305754497)
        ·
          refine ⟨1425590036712688729315873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1900786715616918305754497 1425590036712688729315873)
          ·
            refine ⟨1069192527534516546986905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1425590036712688729315873 1069192527534516546986905)
            ·
              refine ⟨801894395650887410240179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1069192527534516546986905 801894395650887410240179)
              ·
                refine ⟨1202841593476331115360269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801894395650887410240179 1202841593476331115360269)
                ·
                  refine ⟨451065597553624168260101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202841593476331115360269 451065597553624168260101)
                  ·
                    rfl

theorem cell20_988253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_988253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988253 prefixEnd_988253 := by exact prefixLift 988253
  have htrace : WordTrace (prefixWord ++ tailWord_988253) baseStart_988253 baseEnd_988253 := by
    simpa [prefixWord, tailWord_988253, baseEnd_988253] using wordTrace_append hprefix tailTrace_988253
  have hstable : (prefixWord ++ tailWord_988253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988253).length < 2 ^ (prefixWord ++ tailWord_988253).sum := by decide
  have hdescent : baseEnd_988253 < baseStart_988253 := by decide
  rcases family_descends (prefixWord ++ tailWord_988253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988268 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 6]
def baseStart_988268 : Nat := 118140960795 + 988268 * 2 ^ 59
def prefixEnd_988268 : Nat := 4983230072969 + 3 ^ 40 * 988268 * 2
def baseEnd_988268 : Nat := 451072443962350782760039

theorem tailTrace_988268 : CollatzResearch.WordTrace tailWord_988268 prefixEnd_988268 451072443962350782760039 := by
  unfold tailWord_988268
  simp only [CollatzResearch.WordTrace]
  refine ⟨18022547591840646791014729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24030063455787529054686305 18022547591840646791014729)
  ·
    refine ⟨13516910693880485093261047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18022547591840646791014729 13516910693880485093261047)
    ·
      refine ⟨20275366040820727639891571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13516910693880485093261047 20275366040820727639891571)
      ·
        refine ⟨30413049061231091459837357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20275366040820727639891571 30413049061231091459837357)
        ·
          refine ⟨11404893397961659297439009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30413049061231091459837357 11404893397961659297439009)
          ·
            refine ⟨8553670048471244473079257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11404893397961659297439009 8553670048471244473079257)
            ·
              refine ⟨6415252536353433354809443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8553670048471244473079257 6415252536353433354809443)
              ·
                refine ⟨9622878804530150032214165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6415252536353433354809443 9622878804530150032214165)
                ·
                  refine ⟨451072443962350782760039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9622878804530150032214165 451072443962350782760039)
                  ·
                    rfl

theorem cell20_988268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_988268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988268 prefixEnd_988268 := by exact prefixLift 988268
  have htrace : WordTrace (prefixWord ++ tailWord_988268) baseStart_988268 baseEnd_988268 := by
    simpa [prefixWord, tailWord_988268, baseEnd_988268] using wordTrace_append hprefix tailTrace_988268
  have hstable : (prefixWord ++ tailWord_988268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988268).length < 2 ^ (prefixWord ++ tailWord_988268).sum := by decide
  have hdescent : baseEnd_988268 < baseStart_988268 := by decide
  rcases family_descends (prefixWord ++ tailWord_988268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988316 : List Nat := [2, 2, 3, 2, 1, 2, 2, 3, 3]
def baseStart_988316 : Nat := 118140960795 + 988316 * 2 ^ 59
def prefixEnd_988316 : Nat := 4983230072969 + 3 ^ 40 * 988316 * 2
def baseEnd_988316 : Nat := 451094352470275949159843

theorem tailTrace_988316 : CollatzResearch.WordTrace tailWord_988316 prefixEnd_988316 451094352470275949159843 := by
  unfold tailWord_988316
  simp only [CollatzResearch.WordTrace]
  refine ⟨18023422943753698889888401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24031230591671598519851201 18023422943753698889888401)
  ·
    refine ⟨13517567207815274167416301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18023422943753698889888401 13517567207815274167416301)
    ·
      refine ⟨5069087702930727812781113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13517567207815274167416301 5069087702930727812781113)
      ·
        refine ⟨3801815777198045859585835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5069087702930727812781113 3801815777198045859585835)
        ·
          refine ⟨5702723665797068789378753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3801815777198045859585835 5702723665797068789378753)
          ·
            refine ⟨4277042749347801592034065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5702723665797068789378753 4277042749347801592034065)
            ·
              refine ⟨3207782062010851194025549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4277042749347801592034065 3207782062010851194025549)
              ·
                refine ⟨1202918273254069197759581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3207782062010851194025549 1202918273254069197759581)
                ·
                  refine ⟨451094352470275949159843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202918273254069197759581 451094352470275949159843)
                  ·
                    rfl

theorem cell20_988316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_988316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988316 prefixEnd_988316 := by exact prefixLift 988316
  have htrace : WordTrace (prefixWord ++ tailWord_988316) baseStart_988316 baseEnd_988316 := by
    simpa [prefixWord, tailWord_988316, baseEnd_988316] using wordTrace_append hprefix tailTrace_988316
  have hstable : (prefixWord ++ tailWord_988316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988316).length < 2 ^ (prefixWord ++ tailWord_988316).sum := by decide
  have hdescent : baseEnd_988316 < baseStart_988316 := by decide
  rcases family_descends (prefixWord ++ tailWord_988316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988375 : List Nat := [1, 1, 3, 2, 1, 2, 2, 5, 3]
def baseStart_988375 : Nat := 118140960795 + 988375 * 2 ^ 59
def prefixEnd_988375 : Nat := 4983230072969 + 3 ^ 40 * 988375 * 2
def baseEnd_988375 : Nat := 451121281677933966192935

theorem tailTrace_988375 : CollatzResearch.WordTrace tailWord_988375 prefixEnd_988375 451121281677933966192935 := by
  unfold tailWord_988375
  simp only [CollatzResearch.WordTrace]
  refine ⟨36048997794293650856174579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24032665196195767237449719 36048997794293650856174579)
  ·
    refine ⟨54073496691440476284261869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36048997794293650856174579 54073496691440476284261869)
    ·
      refine ⟨20277561259290178606598201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54073496691440476284261869 20277561259290178606598201)
      ·
        refine ⟨15208170944467633954948651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20277561259290178606598201 15208170944467633954948651)
        ·
          refine ⟨22812256416701450932422977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15208170944467633954948651 22812256416701450932422977)
          ·
            refine ⟨17109192312526088199317233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22812256416701450932422977 17109192312526088199317233)
            ·
              refine ⟨12831894234394566149487925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17109192312526088199317233 12831894234394566149487925)
              ·
                refine ⟨1202990084474490576514493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12831894234394566149487925 1202990084474490576514493)
                ·
                  refine ⟨451121281677933966192935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202990084474490576514493 451121281677933966192935)
                  ·
                    rfl

theorem cell20_988375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 3].length) (baseStart_988375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988375 prefixEnd_988375 := by exact prefixLift 988375
  have htrace : WordTrace (prefixWord ++ tailWord_988375) baseStart_988375 baseEnd_988375 := by
    simpa [prefixWord, tailWord_988375, baseEnd_988375] using wordTrace_append hprefix tailTrace_988375
  have hstable : (prefixWord ++ tailWord_988375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988375).length < 2 ^ (prefixWord ++ tailWord_988375).sum := by decide
  have hdescent : baseEnd_988375 < baseStart_988375 := by decide
  rcases family_descends (prefixWord ++ tailWord_988375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988381 : List Nat := [1, 4, 3, 2, 3, 1, 2, 4]
def baseStart_988381 : Nat := 118140960795 + 988381 * 2 ^ 59
def prefixEnd_988381 : Nat := 4983230072969 + 3 ^ 40 * 988381 * 2
def baseEnd_988381 : Nat := 150374673413808203997637

theorem tailTrace_988381 : CollatzResearch.WordTrace tailWord_988381 prefixEnd_988381 150374673413808203997637 := by
  unfold tailWord_988381
  simp only [CollatzResearch.WordTrace]
  refine ⟨36049216632271913880892997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24032811088181275920595331 36049216632271913880892997)
  ·
    refine ⟨6759228118550983852667437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36049216632271913880892997 6759228118550983852667437)
    ·
      refine ⟨2534710544456618944750289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6759228118550983852667437 2534710544456618944750289)
      ·
        refine ⟨1901032908342464208562717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2534710544456618944750289 1901032908342464208562717)
        ·
          refine ⟨712887340628424078211019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1901032908342464208562717 712887340628424078211019)
          ·
            refine ⟨1069331010942636117316529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712887340628424078211019 1069331010942636117316529)
            ·
              refine ⟨801998258206977087987397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1069331010942636117316529 801998258206977087987397)
              ·
                refine ⟨150374673413808203997637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 801998258206977087987397 150374673413808203997637)
                ·
                  rfl

theorem cell20_988381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 4].length) (baseStart_988381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988381 prefixEnd_988381 := by exact prefixLift 988381
  have htrace : WordTrace (prefixWord ++ tailWord_988381) baseStart_988381 baseEnd_988381 := by
    simpa [prefixWord, tailWord_988381, baseEnd_988381] using wordTrace_append hprefix tailTrace_988381
  have hstable : (prefixWord ++ tailWord_988381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988381).length < 2 ^ (prefixWord ++ tailWord_988381).sum := by decide
  have hdescent : baseEnd_988381 < baseStart_988381 := by decide
  rcases family_descends (prefixWord ++ tailWord_988381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988385 : List Nat := [1, 2, 3, 1, 3, 4, 2, 4]
def baseStart_988385 : Nat := 118140960795 + 988385 * 2 ^ 59
def prefixEnd_988385 : Nat := 4983230072969 + 3 ^ 40 * 988385 * 2
def baseEnd_988385 : Nat := 150375281983472791953187

theorem tailTrace_988385 : CollatzResearch.WordTrace tailWord_988385 prefixEnd_988385 150375281983472791953187 := by
  unfold tailWord_988385
  simp only [CollatzResearch.WordTrace]
  refine ⟨36049362524257422564038609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24032908349504948376025739 36049362524257422564038609)
  ·
    refine ⟨27037021893193066923028957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36049362524257422564038609 27037021893193066923028957)
    ·
      refine ⟨10138883209947400096135859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27037021893193066923028957 10138883209947400096135859)
      ·
        refine ⟨15208324814921100144203789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10138883209947400096135859 15208324814921100144203789)
        ·
          refine ⟨5703121805595412554076421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15208324814921100144203789 5703121805595412554076421)
          ·
            refine ⟨1069335338549139853889329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5703121805595412554076421 1069335338549139853889329)
            ·
              refine ⟨802001503911854890416997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1069335338549139853889329 802001503911854890416997)
              ·
                refine ⟨150375281983472791953187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 802001503911854890416997 150375281983472791953187)
                ·
                  rfl

theorem cell20_988385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 4].length) (baseStart_988385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988385 prefixEnd_988385 := by exact prefixLift 988385
  have htrace : WordTrace (prefixWord ++ tailWord_988385) baseStart_988385 baseEnd_988385 := by
    simpa [prefixWord, tailWord_988385, baseEnd_988385] using wordTrace_append hprefix tailTrace_988385
  have hstable : (prefixWord ++ tailWord_988385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988385).length < 2 ^ (prefixWord ++ tailWord_988385).sum := by decide
  have hdescent : baseEnd_988385 < baseStart_988385 := by decide
  rcases family_descends (prefixWord ++ tailWord_988385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988427 : List Nat := [1, 1, 1, 1, 5, 3, 1, 7]
def baseStart_988427 : Nat := 118140960795 + 988427 * 2 ^ 59
def prefixEnd_988427 : Nat := 4983230072969 + 3 ^ 40 * 988427 * 2
def baseEnd_988427 : Nat := 150381671964950965486463

theorem tailTrace_988427 : CollatzResearch.WordTrace tailWord_988427 prefixEnd_988427 150381671964950965486463 := by
  unfold tailWord_988427
  simp only [CollatzResearch.WordTrace]
  refine ⟨36050894390105263737067535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24033929593403509158045023 36050894390105263737067535)
  ·
    refine ⟨54076341585157895605601303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36050894390105263737067535 54076341585157895605601303)
    ·
      refine ⟨81114512377736843408401955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54076341585157895605601303 81114512377736843408401955)
      ·
        refine ⟨121671768566605265112602933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81114512377736843408401955 121671768566605265112602933)
        ·
          refine ⟨11406728303119243604306525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121671768566605265112602933 11406728303119243604306525)
          ·
            refine ⟨4277523113669716351614947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11406728303119243604306525 4277523113669716351614947)
            ·
              refine ⟨6416284670504574527422421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4277523113669716351614947 6416284670504574527422421)
              ·
                refine ⟨150381671964950965486463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6416284670504574527422421 150381671964950965486463)
                ·
                  rfl

theorem cell20_988427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 7].length) (baseStart_988427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988427 prefixEnd_988427 := by exact prefixLift 988427
  have htrace : WordTrace (prefixWord ++ tailWord_988427) baseStart_988427 baseEnd_988427 := by
    simpa [prefixWord, tailWord_988427, baseEnd_988427] using wordTrace_append hprefix tailTrace_988427
  have hstable : (prefixWord ++ tailWord_988427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988427).length < 2 ^ (prefixWord ++ tailWord_988427).sum := by decide
  have hdescent : baseEnd_988427 < baseStart_988427 := by decide
  rcases family_descends (prefixWord ++ tailWord_988427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988430 : List Nat := [4, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_988430 : Nat := 118140960795 + 988430 * 2 ^ 59
def prefixEnd_988430 : Nat := 4983230072969 + 3 ^ 40 * 988430 * 2
def baseEnd_988430 : Nat := 451146385176598219359377

theorem tailTrace_988430 : CollatzResearch.WordTrace tailWord_988430 prefixEnd_988430 451146385176598219359377 := by
  unfold tailWord_988430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4506375476136799406178343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24034002539396263499617829 4506375476136799406178343)
  ·
    refine ⟨6759563214205199109267515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4506375476136799406178343 6759563214205199109267515)
    ·
      refine ⟨10139344821307798663901273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6759563214205199109267515 10139344821307798663901273)
      ·
        refine ⟨7604508615980848997925955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10139344821307798663901273 7604508615980848997925955)
        ·
          refine ⟨11406762923971273496888933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7604508615980848997925955 11406762923971273496888933)
          ·
            refine ⟨2138768048244613780666675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11406762923971273496888933 2138768048244613780666675)
            ·
              refine ⟨3208152072366920671000013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2138768048244613780666675 3208152072366920671000013)
              ·
                refine ⟨1203057027137595251625005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3208152072366920671000013 1203057027137595251625005)
                ·
                  refine ⟨451146385176598219359377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1203057027137595251625005 451146385176598219359377)
                  ·
                    rfl

theorem cell20_988430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_988430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988430 prefixEnd_988430 := by exact prefixLift 988430
  have htrace : WordTrace (prefixWord ++ tailWord_988430) baseStart_988430 baseEnd_988430 := by
    simpa [prefixWord, tailWord_988430, baseEnd_988430] using wordTrace_append hprefix tailTrace_988430
  have hstable : (prefixWord ++ tailWord_988430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988430).length < 2 ^ (prefixWord ++ tailWord_988430).sum := by decide
  have hdescent : baseEnd_988430 < baseStart_988430 := by decide
  rcases family_descends (prefixWord ++ tailWord_988430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988465 : List Nat := [1, 2, 2, 3, 3, 9]
def baseStart_988465 : Nat := 118140960795 + 988465 * 2 ^ 59
def prefixEnd_988465 : Nat := 4983230072969 + 3 ^ 40 * 988465 * 2
def baseEnd_988465 : Nat := 16709717041862727896021

theorem tailTrace_988465 : CollatzResearch.WordTrace tailWord_988465 prefixEnd_988465 16709717041862727896021 := by
  unfold tailWord_988465
  simp only [CollatzResearch.WordTrace]
  refine ⟨36052280363967596226950849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24034853575978397484633899 36052280363967596226950849)
  ·
    refine ⟨27039210272975697170213137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36052280363967596226950849 27039210272975697170213137)
    ·
      refine ⟨20279407704731772877659853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27039210272975697170213137 20279407704731772877659853)
      ·
        refine ⟨7604777889274414829122445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20279407704731772877659853 7604777889274414829122445)
        ·
          refine ⟨2851791708477905560920917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7604777889274414829122445 2851791708477905560920917)
          ·
            refine ⟨16709717041862727896021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2851791708477905560920917 16709717041862727896021)
            ·
              rfl

theorem cell20_988465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 9].length) (baseStart_988465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988465 prefixEnd_988465 := by exact prefixLift 988465
  have htrace : WordTrace (prefixWord ++ tailWord_988465) baseStart_988465 baseEnd_988465 := by
    simpa [prefixWord, tailWord_988465, baseEnd_988465] using wordTrace_append hprefix tailTrace_988465
  have hstable : (prefixWord ++ tailWord_988465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988465).length < 2 ^ (prefixWord ++ tailWord_988465).sum := by decide
  have hdescent : baseEnd_988465 < baseStart_988465 := by decide
  rcases family_descends (prefixWord ++ tailWord_988465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988489 : List Nat := [1, 2, 1, 1, 2, 3, 4, 3, 3]
def baseStart_988489 : Nat := 118140960795 + 988489 * 2 ^ 59
def prefixEnd_988489 : Nat := 4983230072969 + 3 ^ 40 * 988489 * 2
def baseEnd_988489 : Nat := 451173314384256236392469

theorem tailTrace_988489 : CollatzResearch.WordTrace tailWord_988489 prefixEnd_988489 451173314384256236392469 := by
  unfold tailWord_988489
  simp only [CollatzResearch.WordTrace]
  refine ⟨36053155715880648325824521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24035437143920432217216347 36053155715880648325824521)
  ·
    refine ⟨27039866786910486244368391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36053155715880648325824521 27039866786910486244368391)
    ·
      refine ⟨40559800180365729366552587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27039866786910486244368391 40559800180365729366552587)
      ·
        refine ⟨60839700270548594049828881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40559800180365729366552587 60839700270548594049828881)
        ·
          refine ⟨45629775202911445537371661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60839700270548594049828881 45629775202911445537371661)
          ·
            refine ⟨17111165701091792076514373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45629775202911445537371661 17111165701091792076514373)
            ·
              refine ⟨3208343568954711014346445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17111165701091792076514373 3208343568954711014346445)
              ·
                refine ⟨1203128838358016630379917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3208343568954711014346445 1203128838358016630379917)
                ·
                  refine ⟨451173314384256236392469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1203128838358016630379917 451173314384256236392469)
                  ·
                    rfl

theorem cell20_988489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_988489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988489 prefixEnd_988489 := by exact prefixLift 988489
  have htrace : WordTrace (prefixWord ++ tailWord_988489) baseStart_988489 baseEnd_988489 := by
    simpa [prefixWord, tailWord_988489, baseEnd_988489] using wordTrace_append hprefix tailTrace_988489
  have hstable : (prefixWord ++ tailWord_988489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988489).length < 2 ^ (prefixWord ++ tailWord_988489).sum := by decide
  have hdescent : baseEnd_988489 < baseStart_988489 := by decide
  rcases family_descends (prefixWord ++ tailWord_988489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988496 : List Nat := [2, 1, 1, 1, 1, 5, 3, 2, 4]
def baseStart_988496 : Nat := 118140960795 + 988496 * 2 ^ 59
def prefixEnd_988496 : Nat := 4983230072969 + 3 ^ 40 * 988496 * 2
def baseEnd_988496 : Nat := 451176509374995323159107

theorem tailTrace_988496 : CollatzResearch.WordTrace tailWord_988496 prefixEnd_988496 451176509374995323159107 := by
  unfold tailWord_988496
  simp only [CollatzResearch.WordTrace]
  refine ⟨18026705513427644260664671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24035607351236859014219561 18026705513427644260664671)
  ·
    refine ⟨27040058270141466390997007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18026705513427644260664671 27040058270141466390997007)
    ·
      refine ⟨40560087405212199586495511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27040058270141466390997007 40560087405212199586495511)
      ·
        refine ⟨60840131107818299379743267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40560087405212199586495511 60840131107818299379743267)
        ·
          refine ⟨91260196661727449069614901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60840131107818299379743267 91260196661727449069614901)
          ·
            refine ⟨8555643437036948350276397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91260196661727449069614901 8555643437036948350276397)
            ·
              refine ⟨3208366288888855631353649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8555643437036948350276397 3208366288888855631353649)
              ·
                refine ⟨2406274716666641723515237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3208366288888855631353649 2406274716666641723515237)
                ·
                  refine ⟨451176509374995323159107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2406274716666641723515237 451176509374995323159107)
                  ·
                    rfl

theorem cell20_988496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_988496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988496 prefixEnd_988496 := by exact prefixLift 988496
  have htrace : WordTrace (prefixWord ++ tailWord_988496) baseStart_988496 baseEnd_988496 := by
    simpa [prefixWord, tailWord_988496, baseEnd_988496] using wordTrace_append hprefix tailTrace_988496
  have hstable : (prefixWord ++ tailWord_988496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988496).length < 2 ^ (prefixWord ++ tailWord_988496).sum := by decide
  have hdescent : baseEnd_988496 < baseStart_988496 := by decide
  rcases family_descends (prefixWord ++ tailWord_988496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988520 : List Nat := [2, 1, 4, 2, 3, 1, 7]
def baseStart_988520 : Nat := 118140960795 + 988520 * 2 ^ 59
def prefixEnd_988520 : Nat := 4983230072969 + 3 ^ 40 * 988520 * 2
def baseEnd_988520 : Nat := 50131940403217545151001

theorem tailTrace_988520 : CollatzResearch.WordTrace tailWord_988520 prefixEnd_988520 50131940403217545151001 := by
  unfold tailWord_988520
  simp only [CollatzResearch.WordTrace]
  refine ⟨18027143189384170310101507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24036190919178893746802009 18027143189384170310101507)
  ·
    refine ⟨27040714784076255465152261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18027143189384170310101507 27040714784076255465152261)
    ·
      refine ⟨5070134022014297899716049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27040714784076255465152261 5070134022014297899716049)
      ·
        refine ⟨3802600516510723424787037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5070134022014297899716049 3802600516510723424787037)
        ·
          refine ⟨1425975193691521284295139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3802600516510723424787037 1425975193691521284295139)
          ·
            refine ⟨2138962790537281926442709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1425975193691521284295139 2138962790537281926442709)
            ·
              refine ⟨50131940403217545151001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2138962790537281926442709 50131940403217545151001)
              ·
                rfl

theorem cell20_988520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 7].length) (baseStart_988520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988520 prefixEnd_988520 := by exact prefixLift 988520
  have htrace : WordTrace (prefixWord ++ tailWord_988520) baseStart_988520 baseEnd_988520 := by
    simpa [prefixWord, tailWord_988520, baseEnd_988520] using wordTrace_append hprefix tailTrace_988520
  have hstable : (prefixWord ++ tailWord_988520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988520).length < 2 ^ (prefixWord ++ tailWord_988520).sum := by decide
  have hdescent : baseEnd_988520 < baseStart_988520 := by decide
  rcases family_descends (prefixWord ++ tailWord_988520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988541 : List Nat := [1, 4, 1, 1, 2, 2, 2, 7]
def baseStart_988541 : Nat := 118140960795 + 988541 * 2 ^ 59
def prefixEnd_988541 : Nat := 4983230072969 + 3 ^ 40 * 988541 * 2
def baseEnd_988541 : Nat := 150399016200391722219641

theorem tailTrace_988541 : CollatzResearch.WordTrace tailWord_988541 prefixEnd_988541 150399016200391722219641 := by
  unfold tailWord_988541
  simp only [CollatzResearch.WordTrace]
  refine ⟨36055052311692261206717477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24036701541128174137811651 36055052311692261206717477)
  ·
    refine ⟨6760322308442298976259527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36055052311692261206717477 6760322308442298976259527)
    ·
      refine ⟨10140483462663448464389291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6760322308442298976259527 10140483462663448464389291)
      ·
        refine ⟨15210725193995172696583937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10140483462663448464389291 15210725193995172696583937)
        ·
          refine ⟨11408043895496379522437953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15210725193995172696583937 11408043895496379522437953)
          ·
            refine ⟨8556032921622284641828465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11408043895496379522437953 8556032921622284641828465)
            ·
              refine ⟨6417024691216713481371349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8556032921622284641828465 6417024691216713481371349)
              ·
                refine ⟨150399016200391722219641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6417024691216713481371349 150399016200391722219641)
                ·
                  rfl

theorem cell20_988541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 7].length) (baseStart_988541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988541 prefixEnd_988541 := by exact prefixLift 988541
  have htrace : WordTrace (prefixWord ++ tailWord_988541) baseStart_988541 baseEnd_988541 := by
    simpa [prefixWord, tailWord_988541, baseEnd_988541] using wordTrace_append hprefix tailTrace_988541
  have hstable : (prefixWord ++ tailWord_988541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988541).length < 2 ^ (prefixWord ++ tailWord_988541).sum := by decide
  have hdescent : baseEnd_988541 < baseStart_988541 := by decide
  rcases family_descends (prefixWord ++ tailWord_988541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988641 : List Nat := [1, 2, 3, 1, 2, 3, 1, 4, 3]
def baseStart_988641 : Nat := 118140960795 + 988641 * 2 ^ 59
def prefixEnd_988641 : Nat := 4983230072969 + 3 ^ 40 * 988641 * 2
def baseEnd_988641 : Nat := 451242691326019263325181

theorem tailTrace_988641 : CollatzResearch.WordTrace tailWord_988641 prefixEnd_988641 451242691326019263325181 := by
  unfold tailWord_988641
  simp only [CollatzResearch.WordTrace]
  refine ⟨36058699611329978285357777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24039133074219985523571851 36058699611329978285357777)
  ·
    refine ⟨27044024708497483714018333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36058699611329978285357777 27044024708497483714018333)
    ·
      refine ⟨10141509265686556392756875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27044024708497483714018333 10141509265686556392756875)
      ·
        refine ⟨15212263898529834589135313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10141509265686556392756875 15212263898529834589135313)
        ·
          refine ⟨11409197923897375941851485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15212263898529834589135313 11409197923897375941851485)
          ·
            refine ⟨4278449221461515978194307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11409197923897375941851485 4278449221461515978194307)
            ·
              refine ⟨6417673832192273967291461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4278449221461515978194307 6417673832192273967291461)
              ·
                refine ⟨1203313843536051368867149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6417673832192273967291461 1203313843536051368867149)
                ·
                  refine ⟨451242691326019263325181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1203313843536051368867149 451242691326019263325181)
                  ·
                    rfl

theorem cell20_988641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_988641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988641 prefixEnd_988641 := by exact prefixLift 988641
  have htrace : WordTrace (prefixWord ++ tailWord_988641) baseStart_988641 baseEnd_988641 := by
    simpa [prefixWord, tailWord_988641, baseEnd_988641] using wordTrace_append hprefix tailTrace_988641
  have hstable : (prefixWord ++ tailWord_988641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988641).length < 2 ^ (prefixWord ++ tailWord_988641).sum := by decide
  have hdescent : baseEnd_988641 < baseStart_988641 := by decide
  rcases family_descends (prefixWord ++ tailWord_988641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988648 : List Nat := [2, 1, 4, 1, 1, 2, 2, 3, 4]
def baseStart_988648 : Nat := 118140960795 + 988648 * 2 ^ 59
def prefixEnd_988648 : Nat := 4983230072969 + 3 ^ 40 * 988648 * 2
def baseEnd_988648 : Nat := 451245886316758350091819

theorem tailTrace_988648 : CollatzResearch.WordTrace tailWord_988648 prefixEnd_988648 451245886316758350091819 := by
  unfold tailWord_988648
  simp only [CollatzResearch.WordTrace]
  refine ⟨18029477461152309240431299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24039303281536412320575065 18029477461152309240431299)
  ·
    refine ⟨27044216191728463860646949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18029477461152309240431299 27044216191728463860646949)
    ·
      refine ⟨5070790535949086973871303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27044216191728463860646949 5070790535949086973871303)
      ·
        refine ⟨7606185803923630460806955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5070790535949086973871303 7606185803923630460806955)
        ·
          refine ⟨11409278705885445691210433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7606185803923630460806955 11409278705885445691210433)
          ·
            refine ⟨8556959029414084268407825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11409278705885445691210433 8556959029414084268407825)
            ·
              refine ⟨6417719272060563201305869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8556959029414084268407825 6417719272060563201305869)
              ·
                refine ⟨2406644727022711200489701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6417719272060563201305869 2406644727022711200489701)
                ·
                  refine ⟨451245886316758350091819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2406644727022711200489701 451245886316758350091819)
                  ·
                    rfl

theorem cell20_988648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_988648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988648 prefixEnd_988648 := by exact prefixLift 988648
  have htrace : WordTrace (prefixWord ++ tailWord_988648) baseStart_988648 baseEnd_988648 := by
    simpa [prefixWord, tailWord_988648, baseEnd_988648] using wordTrace_append hprefix tailTrace_988648
  have hstable : (prefixWord ++ tailWord_988648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988648).length < 2 ^ (prefixWord ++ tailWord_988648).sum := by decide
  have hdescent : baseEnd_988648 < baseStart_988648 := by decide
  rcases family_descends (prefixWord ++ tailWord_988648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988655 : List Nat := [1, 1, 2, 1, 4, 1, 5, 5]
def baseStart_988655 : Nat := 118140960795 + 988655 * 2 ^ 59
def prefixEnd_988655 : Nat := 4983230072969 + 3 ^ 40 * 988655 * 2
def baseEnd_988655 : Nat := 150416360435832478952819

theorem tailTrace_988655 : CollatzResearch.WordTrace tailWord_988655 prefixEnd_988655 150416360435832478952819 := by
  unfold tailWord_988655
  simp only [CollatzResearch.WordTrace]
  refine ⟨36059210233279258676367419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24039473488852839117578279 36059210233279258676367419)
  ·
    refine ⟨54088815349918888014551129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36059210233279258676367419 54088815349918888014551129)
    ·
      refine ⟨40566611512439166010913347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54088815349918888014551129 40566611512439166010913347)
      ·
        refine ⟨60849917268658749016370021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40566611512439166010913347 60849917268658749016370021)
        ·
          refine ⟨11409359487873515440569379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60849917268658749016370021 11409359487873515440569379)
          ·
            refine ⟨17114039231810273160854069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11409359487873515440569379 17114039231810273160854069)
            ·
              refine ⟨1604441177982213108830069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17114039231810273160854069 1604441177982213108830069)
              ·
                refine ⟨150416360435832478952819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1604441177982213108830069 150416360435832478952819)
                ·
                  rfl

theorem cell20_988655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 5].length) (baseStart_988655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988655 prefixEnd_988655 := by exact prefixLift 988655
  have htrace : WordTrace (prefixWord ++ tailWord_988655) baseStart_988655 baseEnd_988655 := by
    simpa [prefixWord, tailWord_988655, baseEnd_988655] using wordTrace_append hprefix tailTrace_988655
  have hstable : (prefixWord ++ tailWord_988655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988655).length < 2 ^ (prefixWord ++ tailWord_988655).sum := by decide
  have hdescent : baseEnd_988655 < baseStart_988655 := by decide
  rcases family_descends (prefixWord ++ tailWord_988655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988658 : List Nat := [3, 2, 1, 4, 1, 1, 2, 3, 3]
def baseStart_988658 : Nat := 118140960795 + 988658 * 2 ^ 59
def prefixEnd_988658 : Nat := 4983230072969 + 3 ^ 40 * 988658 * 2
def baseEnd_988658 : Nat := 451250450589242759758445

theorem tailTrace_988658 : CollatzResearch.WordTrace tailWord_988658 prefixEnd_988658 451250450589242759758445 := by
  unfold tailWord_988658
  simp only [CollatzResearch.WordTrace]
  refine ⟨9014829913067097547181657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24039546434845593459151085 9014829913067097547181657)
  ·
    refine ⟨6761122434800323160386243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9014829913067097547181657 6761122434800323160386243)
    ·
      refine ⟨10141683652200484740579365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6761122434800323160386243 10141683652200484740579365)
      ·
        refine ⟨1901565684787590888858631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10141683652200484740579365 1901565684787590888858631)
        ·
          refine ⟨2852348527181386333287947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1901565684787590888858631 2852348527181386333287947)
          ·
            refine ⟨4278522790772079499931921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2852348527181386333287947 4278522790772079499931921)
            ·
              refine ⟨3208892093079059624948941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4278522790772079499931921 3208892093079059624948941)
              ·
                refine ⟨1203334534904647359355853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3208892093079059624948941 1203334534904647359355853)
                ·
                  refine ⟨451250450589242759758445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1203334534904647359355853 451250450589242759758445)
                  ·
                    rfl

theorem cell20_988658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_988658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988658 prefixEnd_988658 := by exact prefixLift 988658
  have htrace : WordTrace (prefixWord ++ tailWord_988658) baseStart_988658 baseEnd_988658 := by
    simpa [prefixWord, tailWord_988658, baseEnd_988658] using wordTrace_append hprefix tailTrace_988658
  have hstable : (prefixWord ++ tailWord_988658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988658).length < 2 ^ (prefixWord ++ tailWord_988658).sum := by decide
  have hdescent : baseEnd_988658 < baseStart_988658 := by decide
  rcases family_descends (prefixWord ++ tailWord_988658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988682 : List Nat := [3, 1, 2, 2, 2, 3, 2, 3, 2]
def baseStart_988682 : Nat := 118140960795 + 988682 * 2 ^ 59
def prefixEnd_988682 : Nat := 4983230072969 + 3 ^ 40 * 988682 * 2
def baseEnd_988682 : Nat := 451261404843205342958347

theorem tailTrace_988682 : CollatzResearch.WordTrace tailWord_988682 prefixEnd_988682 451261404843205342958347 := by
  unfold tailWord_988682
  simp only [CollatzResearch.WordTrace]
  refine ⟨9015048751045360571900075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24040130002787628191733533 9015048751045360571900075)
  ·
    refine ⟨13522573126568040857850113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9015048751045360571900075 13522573126568040857850113)
    ·
      refine ⟨10141929844926030643387585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13522573126568040857850113 10141929844926030643387585)
      ·
        refine ⟨7606447383694522982540689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10141929844926030643387585 7606447383694522982540689)
        ·
          refine ⟨5704835537770892236905517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7606447383694522982540689 5704835537770892236905517)
          ·
            refine ⟨2139313326664084588839569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5704835537770892236905517 2139313326664084588839569)
            ·
              refine ⟨1604484994998063441629677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2139313326664084588839569 1604484994998063441629677)
              ·
                refine ⟨601681873124273790611129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1604484994998063441629677 601681873124273790611129)
                ·
                  refine ⟨451261404843205342958347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601681873124273790611129 451261404843205342958347)
                  ·
                    rfl

theorem cell20_988682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_988682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988682 prefixEnd_988682 := by exact prefixLift 988682
  have htrace : WordTrace (prefixWord ++ tailWord_988682) baseStart_988682 baseEnd_988682 := by
    simpa [prefixWord, tailWord_988682, baseEnd_988682] using wordTrace_append hprefix tailTrace_988682
  have hstable : (prefixWord ++ tailWord_988682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988682).length < 2 ^ (prefixWord ++ tailWord_988682).sum := by decide
  have hdescent : baseEnd_988682 < baseStart_988682 := by decide
  rcases family_descends (prefixWord ++ tailWord_988682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988692 : List Nat := [2, 4, 3, 1, 2, 2, 1, 2, 3]
def baseStart_988692 : Nat := 118140960795 + 988692 * 2 ^ 59
def prefixEnd_988692 : Nat := 4983230072969 + 3 ^ 40 * 988692 * 2
def baseEnd_988692 : Nat := 451265969115689752624973

theorem tailTrace_988692 : CollatzResearch.WordTrace tailWord_988692 prefixEnd_988692 451265969115689752624973 := by
  unfold tailWord_988692
  simp only [CollatzResearch.WordTrace]
  refine ⟨18030279867072606997732165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24040373156096809330309553 18030279867072606997732165)
  ·
    refine ⟨3380677475076113812074781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18030279867072606997732165 3380677475076113812074781)
    ·
      refine ⟨1267754053153542679528043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3380677475076113812074781 1267754053153542679528043)
      ·
        refine ⟨1901631079730314019292065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1267754053153542679528043 1901631079730314019292065)
        ·
          refine ⟨1426223309797735514469049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1901631079730314019292065 1426223309797735514469049)
          ·
            refine ⟨1069667482348301635851787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1426223309797735514469049 1069667482348301635851787)
            ·
              refine ⟨1604501223522452453777681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1069667482348301635851787 1604501223522452453777681)
              ·
                refine ⟨1203375917641839340333261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1604501223522452453777681 1203375917641839340333261)
                ·
                  refine ⟨451265969115689752624973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1203375917641839340333261 451265969115689752624973)
                  ·
                    rfl

theorem cell20_988692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_988692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988692 prefixEnd_988692 := by exact prefixLift 988692
  have htrace : WordTrace (prefixWord ++ tailWord_988692) baseStart_988692 baseEnd_988692 := by
    simpa [prefixWord, tailWord_988692, baseEnd_988692] using wordTrace_append hprefix tailTrace_988692
  have hstable : (prefixWord ++ tailWord_988692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988692).length < 2 ^ (prefixWord ++ tailWord_988692).sum := by decide
  have hdescent : baseEnd_988692 < baseStart_988692 := by decide
  rcases family_descends (prefixWord ++ tailWord_988692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988693 : List Nat := [1, 3, 2, 1, 3, 3, 7]
def baseStart_988693 : Nat := 118140960795 + 988693 * 2 ^ 59
def prefixEnd_988693 : Nat := 4983230072969 + 3 ^ 40 * 988693 * 2
def baseEnd_988693 : Nat := 50140713949215354843515

theorem tailTrace_988693 : CollatzResearch.WordTrace tailWord_988693 prefixEnd_988693 50140713949215354843515 := by
  unfold tailWord_988693
  simp only [CollatzResearch.WordTrace]
  refine ⟨36060596207141591166250733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24040397471427727444167155 36060596207141591166250733)
  ·
    refine ⟨13522723577678096687344025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36060596207141591166250733 13522723577678096687344025)
    ·
      refine ⟨10142042683258572515508019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13522723577678096687344025 10142042683258572515508019)
      ·
        refine ⟨15213064024887858773262029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10142042683258572515508019 15213064024887858773262029)
        ·
          refine ⟨5704899009332947039973261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15213064024887858773262029 5704899009332947039973261)
          ·
            refine ⟨2139337128499855139989973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5704899009332947039973261 2139337128499855139989973)
            ·
              refine ⟨50140713949215354843515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2139337128499855139989973 50140713949215354843515)
              ·
                rfl

theorem cell20_988693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 7].length) (baseStart_988693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988693 prefixEnd_988693 := by exact prefixLift 988693
  have htrace : WordTrace (prefixWord ++ tailWord_988693) baseStart_988693 baseEnd_988693 := by
    simpa [prefixWord, tailWord_988693, baseEnd_988693] using wordTrace_append hprefix tailTrace_988693
  have hstable : (prefixWord ++ tailWord_988693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988693).length < 2 ^ (prefixWord ++ tailWord_988693).sum := by decide
  have hdescent : baseEnd_988693 < baseStart_988693 := by decide
  rcases family_descends (prefixWord ++ tailWord_988693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988703 : List Nat := [1, 1, 2, 4, 1, 1, 4, 4, 2]
def baseStart_988703 : Nat := 118140960795 + 988703 * 2 ^ 59
def prefixEnd_988703 : Nat := 4983230072969 + 3 ^ 40 * 988703 * 2
def baseEnd_988703 : Nat := 451270989815422603258261

theorem tailTrace_988703 : CollatzResearch.WordTrace tailWord_988703 prefixEnd_988703 451270989815422603258261 := by
  unfold tailWord_988703
  simp only [CollatzResearch.WordTrace]
  refine ⟨36060960937105362874114763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24040640624736908582743175 36060960937105362874114763)
  ·
    refine ⟨54091441405658044311172145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36060960937105362874114763 54091441405658044311172145)
    ·
      refine ⟨40568581054243533233379109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54091441405658044311172145 40568581054243533233379109)
      ·
        refine ⟨7606608947670662481258583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40568581054243533233379109 7606608947670662481258583)
        ·
          refine ⟨11409913421505993721887875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7606608947670662481258583 11409913421505993721887875)
          ·
            refine ⟨17114870132258990582831813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11409913421505993721887875 17114870132258990582831813)
            ·
              refine ⟨3209038149798560734280965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17114870132258990582831813 3209038149798560734280965)
              ·
                refine ⟨601694653087230137677681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3209038149798560734280965 601694653087230137677681)
                ·
                  refine ⟨451270989815422603258261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601694653087230137677681 451270989815422603258261)
                  ·
                    rfl

theorem cell20_988703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 2].length) (baseStart_988703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988703 prefixEnd_988703 := by exact prefixLift 988703
  have htrace : WordTrace (prefixWord ++ tailWord_988703) baseStart_988703 baseEnd_988703 := by
    simpa [prefixWord, tailWord_988703, baseEnd_988703] using wordTrace_append hprefix tailTrace_988703
  have hstable : (prefixWord ++ tailWord_988703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988703).length < 2 ^ (prefixWord ++ tailWord_988703).sum := by decide
  have hdescent : baseEnd_988703 < baseStart_988703 := by decide
  rcases family_descends (prefixWord ++ tailWord_988703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988745 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 6]
def baseStart_988745 : Nat := 118140960795 + 988745 * 2 ^ 59
def prefixEnd_988745 : Nat := 4983230072969 + 3 ^ 40 * 988745 * 2
def baseEnd_988745 : Nat := 451290159759857123858089

theorem tailTrace_988745 : CollatzResearch.WordTrace tailWord_988745 prefixEnd_988745 451290159759857123858089 := by
  unfold tailWord_988745
  simp only [CollatzResearch.WordTrace]
  refine ⟨36062492802953204047143689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24041661868635469364762459 36062492802953204047143689)
  ·
    refine ⟨27046869602214903035357767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36062492802953204047143689 27046869602214903035357767)
    ·
      refine ⟨40570304403322354553036651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27046869602214903035357767 40570304403322354553036651)
      ·
        refine ⟨60855456604983531829554977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40570304403322354553036651 60855456604983531829554977)
        ·
          refine ⟨45641592453737648872166233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60855456604983531829554977 45641592453737648872166233)
          ·
            refine ⟨34231194340303236654124675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45641592453737648872166233 34231194340303236654124675)
            ·
              refine ⟨51346791510454854981187013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34231194340303236654124675 51346791510454854981187013)
              ·
                refine ⟨9627523408210285308972565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51346791510454854981187013 9627523408210285308972565)
                ·
                  refine ⟨451290159759857123858089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9627523408210285308972565 451290159759857123858089)
                  ·
                    rfl

theorem cell20_988745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_988745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988745 prefixEnd_988745 := by exact prefixLift 988745
  have htrace : WordTrace (prefixWord ++ tailWord_988745) baseStart_988745 baseEnd_988745 := by
    simpa [prefixWord, tailWord_988745, baseEnd_988745] using wordTrace_append hprefix tailTrace_988745
  have hstable : (prefixWord ++ tailWord_988745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988745).length < 2 ^ (prefixWord ++ tailWord_988745).sum := by decide
  have hdescent : baseEnd_988745 < baseStart_988745 := by decide
  rcases family_descends (prefixWord ++ tailWord_988745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988769 : List Nat := [1, 2, 3, 1, 1, 3, 4, 5]
def baseStart_988769 : Nat := 118140960795 + 988769 * 2 ^ 59
def prefixEnd_988769 : Nat := 4983230072969 + 3 ^ 40 * 988769 * 2
def baseEnd_988769 : Nat := 150433704671273235685997

theorem tailTrace_988769 : CollatzResearch.WordTrace tailWord_988769 prefixEnd_988769 150433704671273235685997 := by
  unfold tailWord_988769
  simp only [CollatzResearch.WordTrace]
  refine ⟨36063368154866256146017361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24042245436577504097344907 36063368154866256146017361)
  ·
    refine ⟨27047526116149692109513021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36063368154866256146017361 27047526116149692109513021)
    ·
      refine ⟨10142822293556134541067383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27047526116149692109513021 10142822293556134541067383)
      ·
        refine ⟨15214233440334201811601075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10142822293556134541067383 15214233440334201811601075)
        ·
          refine ⟨22821350160501302717401613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15214233440334201811601075 22821350160501302717401613)
          ·
            refine ⟨8558006310187988519025605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22821350160501302717401613 8558006310187988519025605)
            ·
              refine ⟨1604626183160247847317301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8558006310187988519025605 1604626183160247847317301)
              ·
                refine ⟨150433704671273235685997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1604626183160247847317301 150433704671273235685997)
                ·
                  rfl

theorem cell20_988769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 5].length) (baseStart_988769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988769 prefixEnd_988769 := by exact prefixLift 988769
  have htrace : WordTrace (prefixWord ++ tailWord_988769) baseStart_988769 baseEnd_988769 := by
    simpa [prefixWord, tailWord_988769, baseEnd_988769] using wordTrace_append hprefix tailTrace_988769
  have hstable : (prefixWord ++ tailWord_988769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988769).length < 2 ^ (prefixWord ++ tailWord_988769).sum := by decide
  have hdescent : baseEnd_988769 < baseStart_988769 := by decide
  rcases family_descends (prefixWord ++ tailWord_988769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988772 : List Nat := [2, 3, 1, 1, 2, 3, 4, 1, 3]
def baseStart_988772 : Nat := 118140960795 + 988772 * 2 ^ 59
def prefixEnd_988772 : Nat := 4983230072969 + 3 ^ 40 * 988772 * 2
def baseEnd_988772 : Nat := 451302483295565029957979

theorem tailTrace_988772 : CollatzResearch.WordTrace tailWord_988772 prefixEnd_988772 451302483295565029957979 := by
  unfold tailWord_988772
  simp only [CollatzResearch.WordTrace]
  refine ⟨18031738786927693829188285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24042318382570258438917713 18031738786927693829188285)
  ·
    refine ⟨6761902045097885185945607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18031738786927693829188285 6761902045097885185945607)
    ·
      refine ⟨10142853067646827778918411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6761902045097885185945607 10142853067646827778918411)
      ·
        refine ⟨15214279601470241668377617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10142853067646827778918411 15214279601470241668377617)
        ·
          refine ⟨11410709701102681251283213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15214279601470241668377617 11410709701102681251283213)
          ·
            refine ⟨4279016137913505469231205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11410709701102681251283213 4279016137913505469231205)
            ·
              refine ⟨802315525858782275480851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4279016137913505469231205 802315525858782275480851)
              ·
                refine ⟨1203473288788173413221277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802315525858782275480851 1203473288788173413221277)
                ·
                  refine ⟨451302483295565029957979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1203473288788173413221277 451302483295565029957979)
                  ·
                    rfl

theorem cell20_988772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_988772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988772 prefixEnd_988772 := by exact prefixLift 988772
  have htrace : WordTrace (prefixWord ++ tailWord_988772) baseStart_988772 baseEnd_988772 := by
    simpa [prefixWord, tailWord_988772, baseEnd_988772] using wordTrace_append hprefix tailTrace_988772
  have hstable : (prefixWord ++ tailWord_988772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988772).length < 2 ^ (prefixWord ++ tailWord_988772).sum := by decide
  have hdescent : baseEnd_988772 < baseStart_988772 := by decide
  rcases family_descends (prefixWord ++ tailWord_988772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988783 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 6]
def baseStart_988783 : Nat := 118140960795 + 988783 * 2 ^ 59
def prefixEnd_988783 : Nat := 4983230072969 + 3 ^ 40 * 988783 * 2
def baseEnd_988783 : Nat := 451307503995297880591267

theorem tailTrace_988783 : CollatzResearch.WordTrace tailWord_988783 prefixEnd_988783 451307503995297880591267 := by
  unfold tailWord_988783
  simp only [CollatzResearch.WordTrace]
  refine ⟨36063878776815536537027003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24042585851210357691351335 36063878776815536537027003)
  ·
    refine ⟨54095818165223304805540505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36063878776815536537027003 54095818165223304805540505)
    ·
      refine ⟨40571863623917478604155379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54095818165223304805540505 40571863623917478604155379)
      ·
        refine ⟨60857795435876217906233069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40571863623917478604155379 60857795435876217906233069)
        ·
          refine ⟨22821673288453581714837401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60857795435876217906233069 22821673288453581714837401)
          ·
            refine ⟨17116254966340186286128051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22821673288453581714837401 17116254966340186286128051)
            ·
              refine ⟨25674382449510279429192077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17116254966340186286128051 25674382449510279429192077)
              ·
                refine ⟨9627893418566354785947029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25674382449510279429192077 9627893418566354785947029)
                ·
                  refine ⟨451307503995297880591267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9627893418566354785947029 451307503995297880591267)
                  ·
                    rfl

theorem cell20_988783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_988783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988783 prefixEnd_988783 := by exact prefixLift 988783
  have htrace : WordTrace (prefixWord ++ tailWord_988783) baseStart_988783 baseEnd_988783 := by
    simpa [prefixWord, tailWord_988783, baseEnd_988783] using wordTrace_append hprefix tailTrace_988783
  have hstable : (prefixWord ++ tailWord_988783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988783).length < 2 ^ (prefixWord ++ tailWord_988783).sum := by decide
  have hdescent : baseEnd_988783 < baseStart_988783 := by decide
  rcases family_descends (prefixWord ++ tailWord_988783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988810 : List Nat := [3, 1, 2, 3, 2, 2, 2, 2, 3]
def baseStart_988810 : Nat := 118140960795 + 988810 * 2 ^ 59
def prefixEnd_988810 : Nat := 4983230072969 + 3 ^ 40 * 988810 * 2
def baseEnd_988810 : Nat := 451319827531005786691157

theorem tailTrace_988810 : CollatzResearch.WordTrace tailWord_988810 prefixEnd_988810 451319827531005786691157 := by
  unfold tailWord_988810
  simp only [CollatzResearch.WordTrace]
  refine ⟨9016215886929430037064971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24043242365145146765506589 9016215886929430037064971)
  ·
    refine ⟨13524323830394145055597457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9016215886929430037064971 13524323830394145055597457)
    ·
      refine ⟨10143242872795608791698093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13524323830394145055597457 10143242872795608791698093)
      ·
        refine ⟨3803716077298353296886785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10143242872795608791698093 3803716077298353296886785)
        ·
          refine ⟨2852787057973764972665089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3803716077298353296886785 2852787057973764972665089)
          ·
            refine ⟨2139590293480323729498817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2852787057973764972665089 2139590293480323729498817)
            ·
              refine ⟨1604692720110242797124113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2139590293480323729498817 1604692720110242797124113)
              ·
                refine ⟨1203519540082682097843085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1604692720110242797124113 1203519540082682097843085)
                ·
                  refine ⟨451319827531005786691157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1203519540082682097843085 451319827531005786691157)
                  ·
                    rfl

theorem cell20_988810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_988810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988810 prefixEnd_988810 := by exact prefixLift 988810
  have htrace : WordTrace (prefixWord ++ tailWord_988810) baseStart_988810 baseEnd_988810 := by
    simpa [prefixWord, tailWord_988810, baseEnd_988810] using wordTrace_append hprefix tailTrace_988810
  have hstable : (prefixWord ++ tailWord_988810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988810).length < 2 ^ (prefixWord ++ tailWord_988810).sum := by decide
  have hdescent : baseEnd_988810 < baseStart_988810 := by decide
  rcases family_descends (prefixWord ++ tailWord_988810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988820 : List Nat := [2, 4, 2, 2, 3, 1, 1, 5]
def baseStart_988820 : Nat := 118140960795 + 988820 * 2 ^ 59
def prefixEnd_988820 : Nat := 4983230072969 + 3 ^ 40 * 988820 * 2
def baseEnd_988820 : Nat := 150441463934496732119261

theorem tailTrace_988820 : CollatzResearch.WordTrace tailWord_988820 prefixEnd_988820 150441463934496732119261 := by
  unfold tailWord_988820
  simp only [CollatzResearch.WordTrace]
  refine ⟨18032614138840745928061957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24043485518454327904082609 18032614138840745928061957)
  ·
    refine ⟨3381115151032639861511617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18032614138840745928061957 3381115151032639861511617)
    ·
      refine ⟨2535836363274479896133713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3381115151032639861511617 2535836363274479896133713)
      ·
        refine ⟨1901877272455859922100285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2535836363274479896133713 1901877272455859922100285)
        ·
          refine ⟨713203977170947470787607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1901877272455859922100285 713203977170947470787607)
          ·
            refine ⟨1069805965756421206181411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713203977170947470787607 1069805965756421206181411)
            ·
              refine ⟨1604708948634631809272117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1069805965756421206181411 1604708948634631809272117)
              ·
                refine ⟨150441463934496732119261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1604708948634631809272117 150441463934496732119261)
                ·
                  rfl

theorem cell20_988820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 5].length) (baseStart_988820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988820 prefixEnd_988820 := by exact prefixLift 988820
  have htrace : WordTrace (prefixWord ++ tailWord_988820) baseStart_988820 baseEnd_988820 := by
    simpa [prefixWord, tailWord_988820, baseEnd_988820] using wordTrace_append hprefix tailTrace_988820
  have hstable : (prefixWord ++ tailWord_988820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988820).length < 2 ^ (prefixWord ++ tailWord_988820).sum := by decide
  have hdescent : baseEnd_988820 < baseStart_988820 := by decide
  rcases family_descends (prefixWord ++ tailWord_988820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988821 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 8]
def baseStart_988821 : Nat := 118140960795 + 988821 * 2 ^ 59
def prefixEnd_988821 : Nat := 4983230072969 + 3 ^ 40 * 988821 * 2
def baseEnd_988821 : Nat := 451324848230738637324445

theorem tailTrace_988821 : CollatzResearch.WordTrace tailWord_988821 prefixEnd_988821 451324848230738637324445 := by
  unfold tailWord_988821
  simp only [CollatzResearch.WordTrace]
  refine ⟨36065264750677869026910317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24043509833785246017940211 36065264750677869026910317)
  ·
    refine ⟨13524474281504200885091369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36065264750677869026910317 13524474281504200885091369)
    ·
      refine ⟨10143355711128150663818527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13524474281504200885091369 10143355711128150663818527)
      ·
        refine ⟨15215033566692225995727791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10143355711128150663818527 15215033566692225995727791)
        ·
          refine ⟨22822550350038338993591687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15215033566692225995727791 22822550350038338993591687)
          ·
            refine ⟨34233825525057508490387531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22822550350038338993591687 34233825525057508490387531)
            ·
              refine ⟨51350738287586262735581297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34233825525057508490387531 51350738287586262735581297)
              ·
                refine ⟨38513053715689697051685973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51350738287586262735581297 38513053715689697051685973)
                ·
                  refine ⟨451324848230738637324445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38513053715689697051685973 451324848230738637324445)
                  ·
                    rfl

theorem cell20_988821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_988821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988821 prefixEnd_988821 := by exact prefixLift 988821
  have htrace : WordTrace (prefixWord ++ tailWord_988821) baseStart_988821 baseEnd_988821 := by
    simpa [prefixWord, tailWord_988821, baseEnd_988821] using wordTrace_append hprefix tailTrace_988821
  have hstable : (prefixWord ++ tailWord_988821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988821).length < 2 ^ (prefixWord ++ tailWord_988821).sum := by decide
  have hdescent : baseEnd_988821 < baseStart_988821 := by decide
  rcases family_descends (prefixWord ++ tailWord_988821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988824 : List Nat := [2, 1, 2, 4, 1, 4, 1, 5]
def baseStart_988824 : Nat := 118140960795 + 988824 * 2 ^ 59
def prefixEnd_988824 : Nat := 4983230072969 + 3 ^ 40 * 988824 * 2
def baseEnd_988824 : Nat := 150442072504161320074811

theorem tailTrace_988824 : CollatzResearch.WordTrace tailWord_988824 prefixEnd_988824 150442072504161320074811 := by
  unfold tailWord_988824
  simp only [CollatzResearch.WordTrace]
  refine ⟨18032687084833500269634763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24043582779778000359513017 18032687084833500269634763)
  ·
    refine ⟨27049030627250250404452145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18032687084833500269634763 27049030627250250404452145)
    ·
      refine ⟨20286772970437687803339109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27049030627250250404452145 20286772970437687803339109)
      ·
        refine ⟨3803769931957066463126083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20286772970437687803339109 3803769931957066463126083)
        ·
          refine ⟨5705654897935599694689125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3803769931957066463126083 5705654897935599694689125)
          ·
            refine ⟨1069810293362924942754211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5705654897935599694689125 1069810293362924942754211)
            ·
              refine ⟨1604715440044387414131317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1069810293362924942754211 1604715440044387414131317)
              ·
                refine ⟨150442072504161320074811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1604715440044387414131317 150442072504161320074811)
                ·
                  rfl

theorem cell20_988824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_988824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988824 prefixEnd_988824 := by exact prefixLift 988824
  have htrace : WordTrace (prefixWord ++ tailWord_988824) baseStart_988824 baseEnd_988824 := by
    simpa [prefixWord, tailWord_988824, baseEnd_988824] using wordTrace_append hprefix tailTrace_988824
  have hstable : (prefixWord ++ tailWord_988824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988824).length < 2 ^ (prefixWord ++ tailWord_988824).sum := by decide
  have hdescent : baseEnd_988824 < baseStart_988824 := by decide
  rcases family_descends (prefixWord ++ tailWord_988824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988834 : List Nat := [3, 3, 1, 4, 1, 1, 1, 2, 4]
def baseStart_988834 : Nat := 118140960795 + 988834 * 2 ^ 59
def prefixEnd_988834 : Nat := 4983230072969 + 3 ^ 40 * 988834 * 2
def baseEnd_988834 : Nat := 451330781784968369891059

theorem tailTrace_988834 : CollatzResearch.WordTrace tailWord_988834 prefixEnd_988834 451330781784968369891059 := by
  unfold tailWord_988834
  simp only [CollatzResearch.WordTrace]
  refine ⟨9016434724907693061783389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24043825933087181498089037 9016434724907693061783389)
  ·
    refine ⟨3381163021840384898168771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9016434724907693061783389 3381163021840384898168771)
    ·
      refine ⟨5071744532760577347253157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3381163021840384898168771 5071744532760577347253157)
      ·
        refine ⟨950952099892608252609967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5071744532760577347253157 950952099892608252609967)
        ·
          refine ⟨1426428149838912378914951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 950952099892608252609967 1426428149838912378914951)
          ·
            refine ⟨2139642224758368568372427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426428149838912378914951 2139642224758368568372427)
            ·
              refine ⟨3209463337137552852558641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2139642224758368568372427 3209463337137552852558641)
              ·
                refine ⟨2407097502853164639418981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3209463337137552852558641 2407097502853164639418981)
                ·
                  refine ⟨451330781784968369891059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2407097502853164639418981 451330781784968369891059)
                  ·
                    rfl

theorem cell20_988834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_988834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988834 prefixEnd_988834 := by exact prefixLift 988834
  have htrace : WordTrace (prefixWord ++ tailWord_988834) baseStart_988834 baseEnd_988834 := by
    simpa [prefixWord, tailWord_988834, baseEnd_988834] using wordTrace_append hprefix tailTrace_988834
  have hstable : (prefixWord ++ tailWord_988834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988834).length < 2 ^ (prefixWord ++ tailWord_988834).sum := by decide
  have hdescent : baseEnd_988834 < baseStart_988834 := by decide
  rcases family_descends (prefixWord ++ tailWord_988834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988855 : List Nat := [1, 1, 3, 1, 5, 1, 1, 5, 2]
def baseStart_988855 : Nat := 118140960795 + 988855 * 2 ^ 59
def prefixEnd_988855 : Nat := 4983230072969 + 3 ^ 40 * 988855 * 2
def baseEnd_988855 : Nat := 451340366757185630190973

theorem tailTrace_988855 : CollatzResearch.WordTrace tailWord_988855 prefixEnd_988855 451340366757185630190973 := by
  unfold tailWord_988855
  simp only [CollatzResearch.WordTrace]
  refine ⟨36066504832554692833648019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24044336555036461889098679 36066504832554692833648019)
  ·
    refine ⟨54099757248832039250472029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36066504832554692833648019 54099757248832039250472029)
    ·
      refine ⟨20287408968312014718927011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54099757248832039250472029 20287408968312014718927011)
      ·
        refine ⟨30431113452468022078390517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20287408968312014718927011 30431113452468022078390517)
        ·
          refine ⟨2852916886168877069849111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30431113452468022078390517 2852916886168877069849111)
          ·
            refine ⟨4279375329253315604773667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2852916886168877069849111 4279375329253315604773667)
            ·
              refine ⟨6419062993879973407160501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4279375329253315604773667 6419062993879973407160501)
              ·
                refine ⟨601787155676247506921297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6419062993879973407160501 601787155676247506921297)
                ·
                  refine ⟨451340366757185630190973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601787155676247506921297 451340366757185630190973)
                  ·
                    rfl

theorem cell20_988855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 2].length) (baseStart_988855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988855 prefixEnd_988855 := by exact prefixLift 988855
  have htrace : WordTrace (prefixWord ++ tailWord_988855) baseStart_988855 baseEnd_988855 := by
    simpa [prefixWord, tailWord_988855, baseEnd_988855] using wordTrace_append hprefix tailTrace_988855
  have hstable : (prefixWord ++ tailWord_988855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988855).length < 2 ^ (prefixWord ++ tailWord_988855).sum := by decide
  have hdescent : baseEnd_988855 < baseStart_988855 := by decide
  rcases family_descends (prefixWord ++ tailWord_988855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988982 : List Nat := [5, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_988982 : Nat := 118140960795 + 988982 * 2 ^ 59
def prefixEnd_988982 : Nat := 4983230072969 + 3 ^ 40 * 988982 * 2
def baseEnd_988982 : Nat := 451398333017737632957121

theorem tailTrace_988982 : CollatzResearch.WordTrace tailWord_988982 prefixEnd_988982 451398333017737632957121 := by
  unfold tailWord_988982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2254446056443412095220075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24047424602063062349014133 2254446056443412095220075)
  ·
    refine ⟨3381669084665118142830113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2254446056443412095220075 3381669084665118142830113)
    ·
      refine ⟨2536251813498838607122585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3381669084665118142830113 2536251813498838607122585)
      ·
        refine ⟨1902188860124128955341939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2536251813498838607122585 1902188860124128955341939)
        ·
          refine ⟨2853283290186193433012909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1902188860124128955341939 2853283290186193433012909)
          ·
            refine ⟨1069981233819822537379841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2853283290186193433012909 1069981233819822537379841)
            ·
              refine ⟨802485925364866903034881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1069981233819822537379841 802485925364866903034881)
              ·
                refine ⟨601864444023650177276161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 802485925364866903034881 601864444023650177276161)
                ·
                  refine ⟨451398333017737632957121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601864444023650177276161 451398333017737632957121)
                  ·
                    rfl

theorem cell20_988982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_988982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988982 prefixEnd_988982 := by exact prefixLift 988982
  have htrace : WordTrace (prefixWord ++ tailWord_988982) baseStart_988982 baseEnd_988982 := by
    simpa [prefixWord, tailWord_988982, baseEnd_988982] using wordTrace_append hprefix tailTrace_988982
  have hstable : (prefixWord ++ tailWord_988982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988982).length < 2 ^ (prefixWord ++ tailWord_988982).sum := by decide
  have hdescent : baseEnd_988982 < baseStart_988982 := by decide
  rcases family_descends (prefixWord ++ tailWord_988982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_988986 : List Nat := [3, 1, 1, 1, 5, 1, 4, 2, 2]
def baseStart_988986 : Nat := 118140960795 + 988986 * 2 ^ 59
def prefixEnd_988986 : Nat := 4983230072969 + 3 ^ 40 * 988986 * 2
def baseEnd_988986 : Nat := 451400158726731396823771

theorem tailTrace_988986 : CollatzResearch.WordTrace tailWord_988986 prefixEnd_988986 451400158726731396823771 := by
  unfold tailWord_988986
  simp only [CollatzResearch.WordTrace]
  refine ⟨9017820698770025551666703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24047521863386734804444541 9017820698770025551666703)
  ·
    refine ⟨13526731048155038327500055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9017820698770025551666703 13526731048155038327500055)
    ·
      refine ⟨20290096572232557491250083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13526731048155038327500055 20290096572232557491250083)
      ·
        refine ⟨30435144858348836236875125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20290096572232557491250083 30435144858348836236875125)
        ·
          refine ⟨2853294830470203397207043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30435144858348836236875125 2853294830470203397207043)
          ·
            refine ⟨4279942245705305095810565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2853294830470203397207043 4279942245705305095810565)
            ·
              refine ⟨802489171069744705464481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4279942245705305095810565 802489171069744705464481)
              ·
                refine ⟨601866878302308529098361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 802489171069744705464481 601866878302308529098361)
                ·
                  refine ⟨451400158726731396823771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601866878302308529098361 451400158726731396823771)
                  ·
                    rfl

theorem cell20_988986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_988986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_988986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_988986 prefixEnd_988986 := by exact prefixLift 988986
  have htrace : WordTrace (prefixWord ++ tailWord_988986) baseStart_988986 baseEnd_988986 := by
    simpa [prefixWord, tailWord_988986, baseEnd_988986] using wordTrace_append hprefix tailTrace_988986
  have hstable : (prefixWord ++ tailWord_988986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_988986).length < 2 ^ (prefixWord ++ tailWord_988986).sum := by decide
  have hdescent : baseEnd_988986 < baseStart_988986 := by decide
  rcases family_descends (prefixWord ++ tailWord_988986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989034 : List Nat := [3, 1, 3, 4, 2, 1, 1, 2, 3]
def baseStart_989034 : Nat := 118140960795 + 989034 * 2 ^ 59
def prefixEnd_989034 : Nat := 4983230072969 + 3 ^ 40 * 989034 * 2
def baseEnd_989034 : Nat := 451422067234656563223575

theorem tailTrace_989034 : CollatzResearch.WordTrace tailWord_989034 prefixEnd_989034 451422067234656563223575 := by
  unfold tailWord_989034
  simp only [CollatzResearch.WordTrace]
  refine ⟨9018258374726551601103539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24048688999270804269609437 9018258374726551601103539)
  ·
    refine ⟨13527387562089827401655309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9018258374726551601103539 13527387562089827401655309)
    ·
      refine ⟨5072770335783685275620741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13527387562089827401655309 5072770335783685275620741)
      ·
        refine ⟨951144437959440989178889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5072770335783685275620741 951144437959440989178889)
        ·
          refine ⟨713358328469580741884167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 951144437959440989178889 713358328469580741884167)
          ·
            refine ⟨1070037492704371112826251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713358328469580741884167 1070037492704371112826251)
            ·
              refine ⟨1605056239056556669239377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070037492704371112826251 1605056239056556669239377)
              ·
                refine ⟨1203792179292417501929533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1605056239056556669239377 1203792179292417501929533)
                ·
                  refine ⟨451422067234656563223575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1203792179292417501929533 451422067234656563223575)
                  ·
                    rfl

theorem cell20_989034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_989034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989034 prefixEnd_989034 := by exact prefixLift 989034
  have htrace : WordTrace (prefixWord ++ tailWord_989034) baseStart_989034 baseEnd_989034 := by
    simpa [prefixWord, tailWord_989034, baseEnd_989034] using wordTrace_append hprefix tailTrace_989034
  have hstable : (prefixWord ++ tailWord_989034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989034).length < 2 ^ (prefixWord ++ tailWord_989034).sum := by decide
  have hdescent : baseEnd_989034 < baseStart_989034 := by decide
  rcases family_descends (prefixWord ++ tailWord_989034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989038 : List Nat := [4, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_989038 : Nat := 118140960795 + 989038 * 2 ^ 59
def prefixEnd_989038 : Nat := 4983230072969 + 3 ^ 40 * 989038 * 2
def baseEnd_989038 : Nat := 451423892943650327090225

theorem tailTrace_989038 : CollatzResearch.WordTrace tailWord_989038 prefixEnd_989038 451423892943650327090225 := by
  unfold tailWord_989038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4509147423861464385944971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24048786260594476725039845 4509147423861464385944971)
  ·
    refine ⟨6763721135792196578917457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4509147423861464385944971 6763721135792196578917457)
    ·
      refine ⟨5072790851844147434188093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6763721135792196578917457 5072790851844147434188093)
      ·
        refine ⟨1902296569441555287820535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5072790851844147434188093 1902296569441555287820535)
        ·
          refine ⟨2853444854162332931730803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1902296569441555287820535 2853444854162332931730803)
          ·
            refine ⟨4280167281243499397596205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2853444854162332931730803 4280167281243499397596205)
            ·
              refine ⟨1605062730466312274098577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4280167281243499397596205 1605062730466312274098577)
              ·
                refine ⟨1203797047849734205573933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1605062730466312274098577 1203797047849734205573933)
                ·
                  refine ⟨451423892943650327090225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1203797047849734205573933 451423892943650327090225)
                  ·
                    rfl

theorem cell20_989038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_989038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989038 prefixEnd_989038 := by exact prefixLift 989038
  have htrace : WordTrace (prefixWord ++ tailWord_989038) baseStart_989038 baseEnd_989038 := by
    simpa [prefixWord, tailWord_989038, baseEnd_989038] using wordTrace_append hprefix tailTrace_989038
  have hstable : (prefixWord ++ tailWord_989038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989038).length < 2 ^ (prefixWord ++ tailWord_989038).sum := by decide
  have hdescent : baseEnd_989038 < baseStart_989038 := by decide
  rcases family_descends (prefixWord ++ tailWord_989038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989045 : List Nat := [1, 3, 4, 1, 1, 1, 1, 6, 2]
def baseStart_989045 : Nat := 118140960795 + 989045 * 2 ^ 59
def prefixEnd_989045 : Nat := 4983230072969 + 3 ^ 40 * 989045 * 2
def baseEnd_989045 : Nat := 451427087934389413856863

theorem tailTrace_989045 : CollatzResearch.WordTrace tailWord_989045 prefixEnd_989045 451427087934389413856863 := by
  unfold tailWord_989045
  simp only [CollatzResearch.WordTrace]
  refine ⟨36073434701866355283064589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24048956467910903522043059 36073434701866355283064589)
  ·
    refine ⟨13527538013199883231149221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36073434701866355283064589 13527538013199883231149221)
    ·
      refine ⟨2536413377474978105840479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13527538013199883231149221 2536413377474978105840479)
      ·
        refine ⟨3804620066212467158760719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2536413377474978105840479 3804620066212467158760719)
        ·
          refine ⟨5706930099318700738141079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3804620066212467158760719 5706930099318700738141079)
          ·
            refine ⟨8560395148978051107211619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5706930099318700738141079 8560395148978051107211619)
            ·
              refine ⟨12840592723467076660817429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8560395148978051107211619 12840592723467076660817429)
              ·
                refine ⟨601902783912519218475817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12840592723467076660817429 601902783912519218475817)
                ·
                  refine ⟨451427087934389413856863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601902783912519218475817 451427087934389413856863)
                  ·
                    rfl

theorem cell20_989045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_989045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989045 prefixEnd_989045 := by exact prefixLift 989045
  have htrace : WordTrace (prefixWord ++ tailWord_989045) baseStart_989045 baseEnd_989045 := by
    simpa [prefixWord, tailWord_989045, baseEnd_989045] using wordTrace_append hprefix tailTrace_989045
  have hstable : (prefixWord ++ tailWord_989045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989045).length < 2 ^ (prefixWord ++ tailWord_989045).sum := by decide
  have hdescent : baseEnd_989045 < baseStart_989045 := by decide
  rcases family_descends (prefixWord ++ tailWord_989045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989056 : List Nat := [2, 1, 1, 2, 1, 2, 4, 7]
def baseStart_989056 : Nat := 118140960795 + 989056 * 2 ^ 59
def prefixEnd_989056 : Nat := 4983230072969 + 3 ^ 40 * 989056 * 2
def baseEnd_989056 : Nat := 150477369544707421496717

theorem tailTrace_989056 : CollatzResearch.WordTrace tailWord_989056 prefixEnd_989056 150477369544707421496717 := by
  unfold tailWord_989056
  simp only [CollatzResearch.WordTrace]
  refine ⟨18036917952413252080857511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24049223936551002774476681 18036917952413252080857511)
  ·
    refine ⟨27055376928619878121286267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18036917952413252080857511 27055376928619878121286267)
    ·
      refine ⟨40583065392929817181929401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27055376928619878121286267 40583065392929817181929401)
      ·
        refine ⟨30437299044697362886447051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40583065392929817181929401 30437299044697362886447051)
        ·
          refine ⟨45655948567046044329670577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30437299044697362886447051 45655948567046044329670577)
          ·
            refine ⟨34241961425284533247252933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45655948567046044329670577 34241961425284533247252933)
            ·
              refine ⟨6420367767240849983859925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34241961425284533247252933 6420367767240849983859925)
              ·
                refine ⟨150477369544707421496717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6420367767240849983859925 150477369544707421496717)
                ·
                  rfl

theorem cell20_989056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 7].length) (baseStart_989056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989056 prefixEnd_989056 := by exact prefixLift 989056
  have htrace : WordTrace (prefixWord ++ tailWord_989056) baseStart_989056 baseEnd_989056 := by
    simpa [prefixWord, tailWord_989056, baseEnd_989056] using wordTrace_append hprefix tailTrace_989056
  have hstable : (prefixWord ++ tailWord_989056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989056).length < 2 ^ (prefixWord ++ tailWord_989056).sum := by decide
  have hdescent : baseEnd_989056 < baseStart_989056 := by decide
  rcases family_descends (prefixWord ++ tailWord_989056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989073 : List Nat := [1, 2, 2, 1, 1, 1, 8, 4]
def baseStart_989073 : Nat := 118140960795 + 989073 * 2 ^ 59
def prefixEnd_989073 : Nat := 4983230072969 + 3 ^ 40 * 989073 * 2
def baseEnd_989073 : Nat := 150479955965781920307805

theorem tailTrace_989073 : CollatzResearch.WordTrace tailWord_989073 prefixEnd_989073 150479955965781920307805 := by
  unfold tailWord_989073
  simp only [CollatzResearch.WordTrace]
  refine ⟨36074455945764916065083873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24049637297176610710055915 36074455945764916065083873)
  ·
    refine ⟨27055841959323687048812905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36074455945764916065083873 27055841959323687048812905)
    ·
      refine ⟨20291881469492765286609679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27055841959323687048812905 20291881469492765286609679)
      ·
        refine ⟨30437822204239147929914519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20291881469492765286609679 30437822204239147929914519)
        ·
          refine ⟨45656733306358721894871779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30437822204239147929914519 45656733306358721894871779)
          ·
            refine ⟨68485099959538082842307669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45656733306358721894871779 68485099959538082842307669)
            ·
              refine ⟨802559765150836908308293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 68485099959538082842307669 802559765150836908308293)
              ·
                refine ⟨150479955965781920307805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 802559765150836908308293 150479955965781920307805)
                ·
                  rfl

theorem cell20_989073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 4].length) (baseStart_989073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989073 prefixEnd_989073 := by exact prefixLift 989073
  have htrace : WordTrace (prefixWord ++ tailWord_989073) baseStart_989073 baseEnd_989073 := by
    simpa [prefixWord, tailWord_989073, baseEnd_989073] using wordTrace_append hprefix tailTrace_989073
  have hstable : (prefixWord ++ tailWord_989073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989073).length < 2 ^ (prefixWord ++ tailWord_989073).sum := by decide
  have hdescent : baseEnd_989073 < baseStart_989073 := by decide
  rcases family_descends (prefixWord ++ tailWord_989073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989086 : List Nat := [4, 3, 1, 3, 2, 1, 6]
def baseStart_989086 : Nat := 118140960795 + 989086 * 2 ^ 59
def prefixEnd_989086 : Nat := 4983230072969 + 3 ^ 40 * 989086 * 2
def baseEnd_989086 : Nat := 50160644605730610387781

theorem tailTrace_989086 : CollatzResearch.WordTrace tailWord_989086 prefixEnd_989086 50160644605730610387781 := by
  unfold tailWord_989086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4509366261839727410663389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24049953396478546190204741 4509366261839727410663389)
  ·
    refine ⟨1691012348189897778998771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4509366261839727410663389 1691012348189897778998771)
    ·
      refine ⟨2536518522284846668498157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1691012348189897778998771 2536518522284846668498157)
      ·
        refine ⟨951194445856817500686809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2536518522284846668498157 951194445856817500686809)
        ·
          refine ⟨713395834392613125515107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 951194445856817500686809 713395834392613125515107)
          ·
            refine ⟨1070093751588919688272661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713395834392613125515107 1070093751588919688272661)
            ·
              refine ⟨50160644605730610387781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1070093751588919688272661 50160644605730610387781)
              ·
                rfl

theorem cell20_989086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 6].length) (baseStart_989086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989086 prefixEnd_989086 := by exact prefixLift 989086
  have htrace : WordTrace (prefixWord ++ tailWord_989086) baseStart_989086 baseEnd_989086 := by
    simpa [prefixWord, tailWord_989086, baseEnd_989086] using wordTrace_append hprefix tailTrace_989086
  have hstable : (prefixWord ++ tailWord_989086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989086).length < 2 ^ (prefixWord ++ tailWord_989086).sum := by decide
  have hdescent : baseEnd_989086 < baseStart_989086 := by decide
  rcases family_descends (prefixWord ++ tailWord_989086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989090 : List Nat := [3, 3, 1, 2, 3, 2, 6]
def baseStart_989090 : Nat := 118140960795 + 989090 * 2 ^ 59
def prefixEnd_989090 : Nat := 4983230072969 + 3 ^ 40 * 989090 * 2
def baseEnd_989090 : Nat := 50160847462285473039631

theorem tailTrace_989090 : CollatzResearch.WordTrace tailWord_989090 prefixEnd_989090 50160847462285473039631 := by
  unfold tailWord_989090
  simp only [CollatzResearch.WordTrace]
  refine ⟨9018768996675831992113181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24050050657802218645635149 9018768996675831992113181)
  ·
    refine ⟨3382038373753436997042443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9018768996675831992113181 3382038373753436997042443)
    ·
      refine ⟨5073057560630155495563665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3382038373753436997042443 5073057560630155495563665)
      ·
        refine ⟨3804793170472616621672749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5073057560630155495563665 3804793170472616621672749)
        ·
          refine ⟨1426797438927231233127281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3804793170472616621672749 1426797438927231233127281)
          ·
            refine ⟨1070098079195423424845461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1426797438927231233127281 1070098079195423424845461)
            ·
              refine ⟨50160847462285473039631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1070098079195423424845461 50160847462285473039631)
              ·
                rfl

theorem cell20_989090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 6].length) (baseStart_989090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989090 prefixEnd_989090 := by exact prefixLift 989090
  have htrace : WordTrace (prefixWord ++ tailWord_989090) baseStart_989090 baseEnd_989090 := by
    simpa [prefixWord, tailWord_989090, baseEnd_989090] using wordTrace_append hprefix tailTrace_989090
  have hstable : (prefixWord ++ tailWord_989090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989090).length < 2 ^ (prefixWord ++ tailWord_989090).sum := by decide
  have hdescent : baseEnd_989090 < baseStart_989090 := by decide
  rcases family_descends (prefixWord ++ tailWord_989090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989096 : List Nat := [2, 1, 6, 2, 1, 1, 3, 2, 2]
def baseStart_989096 : Nat := 118140960795 + 989096 * 2 ^ 59
def prefixEnd_989096 : Nat := 4983230072969 + 3 ^ 40 * 989096 * 2
def baseEnd_989096 : Nat := 451450365724059903156655

theorem tailTrace_989096 : CollatzResearch.WordTrace tailWord_989096 prefixEnd_989096 451450365724059903156655 := by
  unfold tailWord_989096
  simp only [CollatzResearch.WordTrace]
  refine ⟨18037647412340795496585571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24050196549787727328780761 18037647412340795496585571)
  ·
    refine ⟨27056471118511193244878357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18037647412340795496585571 27056471118511193244878357)
    ·
      refine ⟨1268272083680212183353673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27056471118511193244878357 1268272083680212183353673)
      ·
        refine ⟨951204062760159137515255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1268272083680212183353673 951204062760159137515255)
        ·
          refine ⟨1426806094140238706272883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951204062760159137515255 1426806094140238706272883)
          ·
            refine ⟨2140209141210358059409325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426806094140238706272883 2140209141210358059409325)
            ·
              refine ⟨802578427953884272278497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2140209141210358059409325 802578427953884272278497)
              ·
                refine ⟨601933820965413204208873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 802578427953884272278497 601933820965413204208873)
                ·
                  refine ⟨451450365724059903156655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601933820965413204208873 451450365724059903156655)
                  ·
                    rfl

theorem cell20_989096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 2].length) (baseStart_989096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989096 prefixEnd_989096 := by exact prefixLift 989096
  have htrace : WordTrace (prefixWord ++ tailWord_989096) baseStart_989096 baseEnd_989096 := by
    simpa [prefixWord, tailWord_989096, baseEnd_989096] using wordTrace_append hprefix tailTrace_989096
  have hstable : (prefixWord ++ tailWord_989096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989096).length < 2 ^ (prefixWord ++ tailWord_989096).sum := by decide
  have hdescent : baseEnd_989096 < baseStart_989096 := by decide
  rcases family_descends (prefixWord ++ tailWord_989096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989148 : List Nat := [2, 2, 6, 1, 1, 1, 2, 2, 3]
def baseStart_989148 : Nat := 118140960795 + 989148 * 2 ^ 59
def prefixEnd_989148 : Nat := 4983230072969 + 3 ^ 40 * 989148 * 2
def baseEnd_989148 : Nat := 451474099940978833423109

theorem tailTrace_989148 : CollatzResearch.WordTrace tailWord_989148 prefixEnd_989148 451474099940978833423109 := by
  unfold tailWord_989148
  simp only [CollatzResearch.WordTrace]
  refine ⟨18038595710246601937032049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24051460946995469249376065 18038595710246601937032049)
  ·
    refine ⟨13528946782684951452774037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18038595710246601937032049 13528946782684951452774037)
    ·
      refine ⟨634169380438357099348783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13528946782684951452774037 634169380438357099348783)
      ·
        refine ⟨951254070657535649023175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634169380438357099348783 951254070657535649023175)
        ·
          refine ⟨1426881105986303473534763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951254070657535649023175 1426881105986303473534763)
          ·
            refine ⟨2140321658979455210302145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426881105986303473534763 2140321658979455210302145)
            ·
              refine ⟨1605241244234591407726609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2140321658979455210302145 1605241244234591407726609)
              ·
                refine ⟨1203930933175943555794957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1605241244234591407726609 1203930933175943555794957)
                ·
                  refine ⟨451474099940978833423109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1203930933175943555794957 451474099940978833423109)
                  ·
                    rfl

theorem cell20_989148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_989148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989148 prefixEnd_989148 := by exact prefixLift 989148
  have htrace : WordTrace (prefixWord ++ tailWord_989148) baseStart_989148 baseEnd_989148 := by
    simpa [prefixWord, tailWord_989148, baseEnd_989148] using wordTrace_append hprefix tailTrace_989148
  have hstable : (prefixWord ++ tailWord_989148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989148).length < 2 ^ (prefixWord ++ tailWord_989148).sum := by decide
  have hdescent : baseEnd_989148 < baseStart_989148 := by decide
  rcases family_descends (prefixWord ++ tailWord_989148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989149 : List Nat := [1, 4, 3, 1, 3, 8]
def baseStart_989149 : Nat := 118140960795 + 989149 * 2 ^ 59
def prefixEnd_989149 : Nat := 4983230072969 + 3 ^ 40 * 989149 * 2
def baseEnd_989149 : Nat := 16721279865489899051473

theorem tailTrace_989149 : CollatzResearch.WordTrace tailWord_989149 prefixEnd_989149 16721279865489899051473 := by
  unfold tailWord_989149
  simp only [CollatzResearch.WordTrace]
  refine ⟨36077227893489581044850501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24051485262326387363233667 36077227893489581044850501)
  ·
    refine ⟨6764480230029296445909469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36077227893489581044850501 6764480230029296445909469)
    ·
      refine ⟨2536680086260986167216051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6764480230029296445909469 2536680086260986167216051)
      ·
        refine ⟨3805020129391479250824077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2536680086260986167216051 3805020129391479250824077)
        ·
          refine ⟨1426882548521804719059029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3805020129391479250824077 1426882548521804719059029)
          ·
            refine ⟨16721279865489899051473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1426882548521804719059029 16721279865489899051473)
            ·
              rfl

theorem cell20_989149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 8].length) (baseStart_989149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989149 prefixEnd_989149 := by exact prefixLift 989149
  have htrace : WordTrace (prefixWord ++ tailWord_989149) baseStart_989149 baseEnd_989149 := by
    simpa [prefixWord, tailWord_989149, baseEnd_989149] using wordTrace_append hprefix tailTrace_989149
  have hstable : (prefixWord ++ tailWord_989149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989149).length < 2 ^ (prefixWord ++ tailWord_989149).sum := by decide
  have hdescent : baseEnd_989149 < baseStart_989149 := by decide
  rcases family_descends (prefixWord ++ tailWord_989149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989166 : List Nat := [4, 1, 2, 1, 3, 3, 1, 5]
def baseStart_989166 : Nat := 118140960795 + 989166 * 2 ^ 59
def prefixEnd_989166 : Nat := 4983230072969 + 3 ^ 40 * 989166 * 2
def baseEnd_989166 : Nat := 150494105210483590274345

theorem tailTrace_989166 : CollatzResearch.WordTrace tailWord_989166 prefixEnd_989166 150494105210483590274345 := by
  unfold tailWord_989166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4509730991803499118527419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24051898622951995298812901 4509730991803499118527419)
  ·
    refine ⟨6764596487705248677791129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4509730991803499118527419 6764596487705248677791129)
    ·
      refine ⟨5073447365778936508343347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6764596487705248677791129 5073447365778936508343347)
      ·
        refine ⟨7610171048668404762515021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5073447365778936508343347 7610171048668404762515021)
        ·
          refine ⟨2853814143250651785943133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7610171048668404762515021 2853814143250651785943133)
          ·
            refine ⟨1070180303718994419728675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2853814143250651785943133 1070180303718994419728675)
            ·
              refine ⟨1605270455578491629593013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070180303718994419728675 1605270455578491629593013)
              ·
                refine ⟨150494105210483590274345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1605270455578491629593013 150494105210483590274345)
                ·
                  rfl

theorem cell20_989166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_989166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989166 prefixEnd_989166 := by exact prefixLift 989166
  have htrace : WordTrace (prefixWord ++ tailWord_989166) baseStart_989166 baseEnd_989166 := by
    simpa [prefixWord, tailWord_989166, baseEnd_989166] using wordTrace_append hprefix tailTrace_989166
  have hstable : (prefixWord ++ tailWord_989166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989166).length < 2 ^ (prefixWord ++ tailWord_989166).sum := by decide
  have hdescent : baseEnd_989166 < baseStart_989166 := by decide
  rcases family_descends (prefixWord ++ tailWord_989166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989207 : List Nat := [1, 1, 3, 5, 3, 1, 1, 2, 3]
def baseStart_989207 : Nat := 118140960795 + 989207 * 2 ^ 59
def prefixEnd_989207 : Nat := 4983230072969 + 3 ^ 40 * 989207 * 2
def baseEnd_989207 : Nat := 451501029148636850456201

theorem tailTrace_989207 : CollatzResearch.WordTrace tailWord_989207 prefixEnd_989207 451501029148636850456201 := by
  unfold tailWord_989207
  simp only [CollatzResearch.WordTrace]
  refine ⟨36079343327279456950461875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24052895551519637966974583 36079343327279456950461875)
  ·
    refine ⟨54119014990919185425692813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36079343327279456950461875 54119014990919185425692813)
    ·
      refine ⟨20294630621594694534634805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54119014990919185425692813 20294630621594694534634805)
      ·
        refine ⟨1902621620774502612622013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20294630621594694534634805 1902621620774502612622013)
        ·
          refine ⟨713483107790438479733255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1902621620774502612622013 713483107790438479733255)
          ·
            refine ⟨1070224661685657719599883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713483107790438479733255 1070224661685657719599883)
            ·
              refine ⟨1605336992528486579399825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070224661685657719599883 1605336992528486579399825)
              ·
                refine ⟨1204002744396364934549869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1605336992528486579399825 1204002744396364934549869)
                ·
                  refine ⟨451501029148636850456201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1204002744396364934549869 451501029148636850456201)
                  ·
                    rfl

theorem cell20_989207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 3].length) (baseStart_989207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989207 prefixEnd_989207 := by exact prefixLift 989207
  have htrace : WordTrace (prefixWord ++ tailWord_989207) baseStart_989207 baseEnd_989207 := by
    simpa [prefixWord, tailWord_989207, baseEnd_989207] using wordTrace_append hprefix tailTrace_989207
  have hstable : (prefixWord ++ tailWord_989207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989207).length < 2 ^ (prefixWord ++ tailWord_989207).sum := by decide
  have hdescent : baseEnd_989207 < baseStart_989207 := by decide
  rcases family_descends (prefixWord ++ tailWord_989207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989208 : List Nat := [2, 1, 2, 3, 2, 1, 9]
def baseStart_989208 : Nat := 118140960795 + 989208 * 2 ^ 59
def prefixEnd_989208 : Nat := 4983230072969 + 3 ^ 40 * 989208 * 2
def baseEnd_989208 : Nat := 50166831730653921269207

theorem tailTrace_989208 : CollatzResearch.WordTrace tailWord_989208 prefixEnd_989208 50166831730653921269207 := by
  unfold tailWord_989208
  simp only [CollatzResearch.WordTrace]
  refine ⟨18039689900137917060624139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24052919866850556080832185 18039689900137917060624139)
  ·
    refine ⟨27059534850206875590936209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18039689900137917060624139 27059534850206875590936209)
    ·
      refine ⟨20294651137655156693202157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27059534850206875590936209 20294651137655156693202157)
      ·
        refine ⟨7610494176620683759950809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20294651137655156693202157 7610494176620683759950809)
        ·
          refine ⟨5707870632465512819963107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7610494176620683759950809 5707870632465512819963107)
          ·
            refine ⟨8561805948698269229944661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5707870632465512819963107 8561805948698269229944661)
            ·
              refine ⟨50166831730653921269207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8561805948698269229944661 50166831730653921269207)
              ·
                rfl

theorem cell20_989208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 9].length) (baseStart_989208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989208 prefixEnd_989208 := by exact prefixLift 989208
  have htrace : WordTrace (prefixWord ++ tailWord_989208) baseStart_989208 baseEnd_989208 := by
    simpa [prefixWord, tailWord_989208, baseEnd_989208] using wordTrace_append hprefix tailTrace_989208
  have hstable : (prefixWord ++ tailWord_989208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989208).length < 2 ^ (prefixWord ++ tailWord_989208).sum := by decide
  have hdescent : baseEnd_989208 < baseStart_989208 := by decide
  rcases family_descends (prefixWord ++ tailWord_989208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989218 : List Nat := [3, 3, 1, 1, 1, 2, 4, 1, 4]
def baseStart_989218 : Nat := 118140960795 + 989218 * 2 ^ 59
def prefixEnd_989218 : Nat := 4983230072969 + 3 ^ 40 * 989218 * 2
def baseEnd_989218 : Nat := 451506049848369701089489

theorem tailTrace_989218 : CollatzResearch.WordTrace tailWord_989218 prefixEnd_989218 451506049848369701089489 := by
  unfold tailWord_989218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9019936132559901457278077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24053163020159737219408205 9019936132559901457278077)
  ·
    refine ⟨3382476049709963046479279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9019936132559901457278077 3382476049709963046479279)
    ·
      refine ⟨5073714074564944569718919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3382476049709963046479279 5073714074564944569718919)
      ·
        refine ⟨7610571111847416854578379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5073714074564944569718919 7610571111847416854578379)
        ·
          refine ⟨11415856667771125281867569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7610571111847416854578379 11415856667771125281867569)
          ·
            refine ⟨8561892500828343961400677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11415856667771125281867569 8561892500828343961400677)
            ·
              refine ⟨1605354843905314492762627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8561892500828343961400677 1605354843905314492762627)
              ·
                refine ⟨2408032265857971739143941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1605354843905314492762627 2408032265857971739143941)
                ·
                  refine ⟨451506049848369701089489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2408032265857971739143941 451506049848369701089489)
                  ·
                    rfl

theorem cell20_989218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_989218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989218 prefixEnd_989218 := by exact prefixLift 989218
  have htrace : WordTrace (prefixWord ++ tailWord_989218) baseStart_989218 baseEnd_989218 := by
    simpa [prefixWord, tailWord_989218, baseEnd_989218] using wordTrace_append hprefix tailTrace_989218
  have hstable : (prefixWord ++ tailWord_989218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989218).length < 2 ^ (prefixWord ++ tailWord_989218).sum := by decide
  have hdescent : baseEnd_989218 < baseStart_989218 := by decide
  rcases family_descends (prefixWord ++ tailWord_989218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989239 : List Nat := [1, 1, 3, 1, 2, 2, 4, 2, 4]
def baseStart_989239 : Nat := 118140960795 + 989239 * 2 ^ 59
def prefixEnd_989239 : Nat := 4983230072969 + 3 ^ 40 * 989239 * 2
def baseEnd_989239 : Nat := 451515634820586961389403

theorem tailTrace_989239 : CollatzResearch.WordTrace tailWord_989239 prefixEnd_989239 451515634820586961389403 := by
  unfold tailWord_989239
  simp only [CollatzResearch.WordTrace]
  refine ⟨36080510463163526415626771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24053673642109017610417847 36080510463163526415626771)
  ·
    refine ⟨54120765694745289623440157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36080510463163526415626771 54120765694745289623440157)
    ·
      refine ⟨20295287135529483608790059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54120765694745289623440157 20295287135529483608790059)
      ·
        refine ⟨30442930703294225413185089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20295287135529483608790059 30442930703294225413185089)
        ·
          refine ⟨22832198027470669059888817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30442930703294225413185089 22832198027470669059888817)
          ·
            refine ⟨17124148520603001794916613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22832198027470669059888817 17124148520603001794916613)
            ·
              refine ⟨3210777847613062836546865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17124148520603001794916613 3210777847613062836546865)
              ·
                refine ⟨2408083385709797127410149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3210777847613062836546865 2408083385709797127410149)
                ·
                  refine ⟨451515634820586961389403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2408083385709797127410149 451515634820586961389403)
                  ·
                    rfl

theorem cell20_989239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_989239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989239 prefixEnd_989239 := by exact prefixLift 989239
  have htrace : WordTrace (prefixWord ++ tailWord_989239) baseStart_989239 baseEnd_989239 := by
    simpa [prefixWord, tailWord_989239, baseEnd_989239] using wordTrace_append hprefix tailTrace_989239
  have hstable : (prefixWord ++ tailWord_989239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989239).length < 2 ^ (prefixWord ++ tailWord_989239).sum := by decide
  have hdescent : baseEnd_989239 < baseStart_989239 := by decide
  rcases family_descends (prefixWord ++ tailWord_989239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989256 : List Nat := [2, 1, 3, 1, 1, 1, 2, 7, 2]
def baseStart_989256 : Nat := 118140960795 + 989256 * 2 ^ 59
def prefixEnd_989256 : Nat := 4983230072969 + 3 ^ 40 * 989256 * 2
def baseEnd_989256 : Nat := 451523394083810457822667

theorem tailTrace_989256 : CollatzResearch.WordTrace tailWord_989256 prefixEnd_989256 451523394083810457822667 := by
  unfold tailWord_989256
  simp only [CollatzResearch.WordTrace]
  refine ⟨18040565252050969159497811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24054087002734625545997081 18040565252050969159497811)
  ·
    refine ⟨27060847878076453739246717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18040565252050969159497811 27060847878076453739246717)
    ·
      refine ⟨10147817954278670152217519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27060847878076453739246717 10147817954278670152217519)
      ·
        refine ⟨15221726931418005228326279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10147817954278670152217519 15221726931418005228326279)
        ·
          refine ⟨22832590397127007842489419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15221726931418005228326279 22832590397127007842489419)
          ·
            refine ⟨34248885595690511763734129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22832590397127007842489419 34248885595690511763734129)
            ·
              refine ⟨25686664196767883822800597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34248885595690511763734129 25686664196767883822800597)
              ·
                refine ⟨602031192111747277096889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25686664196767883822800597 602031192111747277096889)
                ·
                  refine ⟨451523394083810457822667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 602031192111747277096889 451523394083810457822667)
                  ·
                    rfl

theorem cell20_989256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 2].length) (baseStart_989256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989256 prefixEnd_989256 := by exact prefixLift 989256
  have htrace : WordTrace (prefixWord ++ tailWord_989256) baseStart_989256 baseEnd_989256 := by
    simpa [prefixWord, tailWord_989256, baseEnd_989256] using wordTrace_append hprefix tailTrace_989256
  have hstable : (prefixWord ++ tailWord_989256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989256).length < 2 ^ (prefixWord ++ tailWord_989256).sum := by decide
  have hdescent : baseEnd_989256 < baseStart_989256 := by decide
  rcases family_descends (prefixWord ++ tailWord_989256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989273 : List Nat := [1, 2, 1, 2, 2, 1, 7, 2, 2]
def baseStart_989273 : Nat := 118140960795 + 989273 * 2 ^ 59
def prefixEnd_989273 : Nat := 4983230072969 + 3 ^ 40 * 989273 * 2
def baseEnd_989273 : Nat := 451531153347033954255931

theorem tailTrace_989273 : CollatzResearch.WordTrace tailWord_989273 prefixEnd_989273 451531153347033954255931 := by
  unfold tailWord_989273
  simp only [CollatzResearch.WordTrace]
  refine ⟨36081750545040350222364473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24054500363360233481576315 36081750545040350222364473)
  ·
    refine ⟨27061312908780262666773355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36081750545040350222364473 27061312908780262666773355)
    ·
      refine ⟨40591969363170394000160033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27061312908780262666773355 40591969363170394000160033)
      ·
        refine ⟨30443977022377795500120025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40591969363170394000160033 30443977022377795500120025)
        ·
          refine ⟨22832982766783346625090019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30443977022377795500120025 22832982766783346625090019)
          ·
            refine ⟨34249474150175019937635029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22832982766783346625090019 34249474150175019937635029)
            ·
              refine ⟨802722050394727029788321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 34249474150175019937635029 802722050394727029788321)
              ·
                refine ⟨602041537796045272341241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 802722050394727029788321 602041537796045272341241)
                ·
                  refine ⟨451531153347033954255931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 602041537796045272341241 451531153347033954255931)
                  ·
                    rfl

theorem cell20_989273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 2, 2].length) (baseStart_989273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989273 prefixEnd_989273 := by exact prefixLift 989273
  have htrace : WordTrace (prefixWord ++ tailWord_989273) baseStart_989273 baseEnd_989273 := by
    simpa [prefixWord, tailWord_989273, baseEnd_989273] using wordTrace_append hprefix tailTrace_989273
  have hstable : (prefixWord ++ tailWord_989273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989273).length < 2 ^ (prefixWord ++ tailWord_989273).sum := by decide
  have hdescent : baseEnd_989273 < baseStart_989273 := by decide
  rcases family_descends (prefixWord ++ tailWord_989273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989284 : List Nat := [2, 3, 1, 1, 2, 1, 3, 7]
def baseStart_989284 : Nat := 118140960795 + 989284 * 2 ^ 59
def prefixEnd_989284 : Nat := 4983230072969 + 3 ^ 40 * 989284 * 2
def baseEnd_989284 : Nat := 150512058015588934963073

theorem tailTrace_989284 : CollatzResearch.WordTrace tailWord_989284 prefixEnd_989284 150512058015588934963073 := by
  unfold tailWord_989284
  simp only [CollatzResearch.WordTrace]
  refine ⟨18041075874000249550507453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24054767832000332734009937 18041075874000249550507453)
  ·
    refine ⟨6765403452750093581440295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18041075874000249550507453 6765403452750093581440295)
    ·
      refine ⟨10148105179125140372160443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6765403452750093581440295 10148105179125140372160443)
      ·
        refine ⟨15222157768687710558240665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10148105179125140372160443 15222157768687710558240665)
        ·
          refine ⟨11416618326515782918680499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15222157768687710558240665 11416618326515782918680499)
          ·
            refine ⟨17124927489773674378020749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11416618326515782918680499 17124927489773674378020749)
            ·
              refine ⟨6421847808665127891757781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17124927489773674378020749 6421847808665127891757781)
              ·
                refine ⟨150512058015588934963073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6421847808665127891757781 150512058015588934963073)
                ·
                  rfl

theorem cell20_989284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_989284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989284 prefixEnd_989284 := by exact prefixLift 989284
  have htrace : WordTrace (prefixWord ++ tailWord_989284) baseStart_989284 baseEnd_989284 := by
    simpa [prefixWord, tailWord_989284, baseEnd_989284] using wordTrace_append hprefix tailTrace_989284
  have hstable : (prefixWord ++ tailWord_989284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989284).length < 2 ^ (prefixWord ++ tailWord_989284).sum := by decide
  have hdescent : baseEnd_989284 < baseStart_989284 := by decide
  rcases family_descends (prefixWord ++ tailWord_989284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989322 : List Nat := [3, 1, 2, 3, 1, 10]
def baseStart_989322 : Nat := 118140960795 + 989322 * 2 ^ 59
def prefixEnd_989322 : Nat := 4983230072969 + 3 ^ 40 * 989322 * 2
def baseEnd_989322 : Nat := 16724204380822502282311

theorem tailTrace_989322 : CollatzResearch.WordTrace tailWord_989322 prefixEnd_989322 16724204380822502282311 := by
  unfold tailWord_989322
  simp only [CollatzResearch.WordTrace]
  refine ⟨9020884430465707897724555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24055691814575221060598813 9020884430465707897724555)
  ·
    refine ⟨13531326645698561846586833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9020884430465707897724555 13531326645698561846586833)
    ·
      refine ⟨10148494984273921384940125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13531326645698561846586833 10148494984273921384940125)
      ·
        refine ⟨3805685619102720519352547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10148494984273921384940125 3805685619102720519352547)
        ·
          refine ⟨5708528428654080779028821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3805685619102720519352547 5708528428654080779028821)
          ·
            refine ⟨16724204380822502282311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5708528428654080779028821 16724204380822502282311)
            ·
              rfl

theorem cell20_989322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 10].length) (baseStart_989322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989322 prefixEnd_989322 := by exact prefixLift 989322
  have htrace : WordTrace (prefixWord ++ tailWord_989322) baseStart_989322 baseEnd_989322 := by
    simpa [prefixWord, tailWord_989322, baseEnd_989322] using wordTrace_append hprefix tailTrace_989322
  have hstable : (prefixWord ++ tailWord_989322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989322).length < 2 ^ (prefixWord ++ tailWord_989322).sum := by decide
  have hdescent : baseEnd_989322 < baseStart_989322 := by decide
  rcases family_descends (prefixWord ++ tailWord_989322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989370 : List Nat := [3, 1, 1, 1, 2, 2, 3, 5, 2]
def baseStart_989370 : Nat := 118140960795 + 989370 * 2 ^ 59
def prefixEnd_989370 : Nat := 4983230072969 + 3 ^ 40 * 989370 * 2
def baseEnd_989370 : Nat := 451575426790132728022201

theorem tailTrace_989370 : CollatzResearch.WordTrace tailWord_989370 prefixEnd_989370 451575426790132728022201 := by
  unfold tailWord_989370
  simp only [CollatzResearch.WordTrace]
  refine ⟨9021322106422233947161391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24056858950459290525763709 9021322106422233947161391)
  ·
    refine ⟨13531983159633350920742087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9021322106422233947161391 13531983159633350920742087)
    ·
      refine ⟨20297974739450026381113131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13531983159633350920742087 20297974739450026381113131)
      ·
        refine ⟨30446962109175039571669697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20297974739450026381113131 30446962109175039571669697)
        ·
          refine ⟨22835221581881279678752273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30446962109175039571669697 22835221581881279678752273)
          ·
            refine ⟨17126416186410959759064205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22835221581881279678752273 17126416186410959759064205)
            ·
              refine ⟨6422406069904109909649077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17126416186410959759064205 6422406069904109909649077)
              ·
                refine ⟨602100569053510304029601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6422406069904109909649077 602100569053510304029601)
                ·
                  refine ⟨451575426790132728022201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 602100569053510304029601 451575426790132728022201)
                  ·
                    rfl

theorem cell20_989370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_989370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989370 prefixEnd_989370 := by exact prefixLift 989370
  have htrace : WordTrace (prefixWord ++ tailWord_989370) baseStart_989370 baseEnd_989370 := by
    simpa [prefixWord, tailWord_989370, baseEnd_989370] using wordTrace_append hprefix tailTrace_989370
  have hstable : (prefixWord ++ tailWord_989370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989370).length < 2 ^ (prefixWord ++ tailWord_989370).sum := by decide
  have hdescent : baseEnd_989370 < baseStart_989370 := by decide
  rcases family_descends (prefixWord ++ tailWord_989370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989380 : List Nat := [2, 3, 3, 1, 2, 3, 1, 2, 3]
def baseStart_989380 : Nat := 118140960795 + 989380 * 2 ^ 59
def prefixEnd_989380 : Nat := 4983230072969 + 3 ^ 40 * 989380 * 2
def baseEnd_989380 : Nat := 451579991062617137688827

theorem tailTrace_989380 : CollatzResearch.WordTrace tailWord_989380 prefixEnd_989380 451579991062617137688827 := by
  unfold tailWord_989380
  simp only [CollatzResearch.WordTrace]
  refine ⟨18042826577826353748254797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24057102103768471664339729 18042826577826353748254797)
  ·
    refine ⟨6766059966684882655595549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18042826577826353748254797 6766059966684882655595549)
    ·
      refine ⟨2537272487506830995848331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6766059966684882655595549 2537272487506830995848331)
      ·
        refine ⟨3805908731260246493772497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2537272487506830995848331 3805908731260246493772497)
        ·
          refine ⟨2854431548445184870329373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3805908731260246493772497 2854431548445184870329373)
          ·
            refine ⟨1070411830666944326373515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2854431548445184870329373 1070411830666944326373515)
            ·
              refine ⟨1605617746000416489560273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070411830666944326373515 1605617746000416489560273)
              ·
                refine ⟨1204213309500312367170205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1605617746000416489560273 1204213309500312367170205)
                ·
                  refine ⟨451579991062617137688827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1204213309500312367170205 451579991062617137688827)
                  ·
                    rfl

theorem cell20_989380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_989380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989380 prefixEnd_989380 := by exact prefixLift 989380
  have htrace : WordTrace (prefixWord ++ tailWord_989380) baseStart_989380 baseEnd_989380 := by
    simpa [prefixWord, tailWord_989380, baseEnd_989380] using wordTrace_append hprefix tailTrace_989380
  have hstable : (prefixWord ++ tailWord_989380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989380).length < 2 ^ (prefixWord ++ tailWord_989380).sum := by decide
  have hdescent : baseEnd_989380 < baseStart_989380 := by decide
  rcases family_descends (prefixWord ++ tailWord_989380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989391 : List Nat := [1, 1, 2, 1, 1, 3, 6, 1, 4]
def baseStart_989391 : Nat := 118140960795 + 989391 * 2 ^ 59
def prefixEnd_989391 : Nat := 4983230072969 + 3 ^ 40 * 989391 * 2
def baseEnd_989391 : Nat := 451585011762349988322115

theorem tailTrace_989391 : CollatzResearch.WordTrace tailWord_989391 prefixEnd_989391 451585011762349988322115 := by
  unfold tailWord_989391
  simp only [CollatzResearch.WordTrace]
  refine ⟨36086054358612856375160027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24057369572408570916773351 36086054358612856375160027)
  ·
    refine ⟨54129081537919284562740041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36086054358612856375160027 54129081537919284562740041)
    ·
      refine ⟨40596811153439463422055031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54129081537919284562740041 40596811153439463422055031)
      ·
        refine ⟨60895216730159195133082547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40596811153439463422055031 60895216730159195133082547)
        ·
          refine ⟨91342825095238792699623821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60895216730159195133082547 91342825095238792699623821)
          ·
            refine ⟨34253559410714547262358933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91342825095238792699623821 34253559410714547262358933)
            ·
              refine ⟨1605635597377244402923075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34253559410714547262358933 1605635597377244402923075)
              ·
                refine ⟨2408453396065866604384613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1605635597377244402923075 2408453396065866604384613)
                ·
                  refine ⟨451585011762349988322115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2408453396065866604384613 451585011762349988322115)
                  ·
                    rfl

theorem cell20_989391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 4].length) (baseStart_989391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989391 prefixEnd_989391 := by exact prefixLift 989391
  have htrace : WordTrace (prefixWord ++ tailWord_989391) baseStart_989391 baseEnd_989391 := by
    simpa [prefixWord, tailWord_989391, baseEnd_989391] using wordTrace_append hprefix tailTrace_989391
  have hstable : (prefixWord ++ tailWord_989391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989391).length < 2 ^ (prefixWord ++ tailWord_989391).sum := by decide
  have hdescent : baseEnd_989391 < baseStart_989391 := by decide
  rcases family_descends (prefixWord ++ tailWord_989391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989411 : List Nat := [1, 1, 1, 8, 1, 2, 2, 4]
def baseStart_989411 : Nat := 118140960795 + 989411 * 2 ^ 59
def prefixEnd_989411 : Nat := 4983230072969 + 3 ^ 40 * 989411 * 2
def baseEnd_989411 : Nat := 150531380102439602551789

theorem tailTrace_989411 : CollatzResearch.WordTrace tailWord_989411 prefixEnd_989411 150531380102439602551789 := by
  unfold tailWord_989411
  simp only [CollatzResearch.WordTrace]
  refine ⟨36086783818540399790888087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24057855879026933193925391 36086783818540399790888087)
  ·
    refine ⟨54130175727810599686332131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36086783818540399790888087 54130175727810599686332131)
    ·
      refine ⟨81195263591715899529498197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54130175727810599686332131 81195263591715899529498197)
      ·
        refine ⟨951506995215420697611307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 81195263591715899529498197 951506995215420697611307)
        ·
          refine ⟨1427260492823131046416961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951506995215420697611307 1427260492823131046416961)
          ·
            refine ⟨1070445369617348284812721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1427260492823131046416961 1070445369617348284812721)
            ·
              refine ⟨802834027213011213609541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070445369617348284812721 802834027213011213609541)
              ·
                refine ⟨150531380102439602551789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 802834027213011213609541 150531380102439602551789)
                ·
                  rfl

theorem cell20_989411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 4].length) (baseStart_989411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989411 prefixEnd_989411 := by exact prefixLift 989411
  have htrace : WordTrace (prefixWord ++ tailWord_989411) baseStart_989411 baseEnd_989411 := by
    simpa [prefixWord, tailWord_989411, baseEnd_989411] using wordTrace_append hprefix tailTrace_989411
  have hstable : (prefixWord ++ tailWord_989411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989411).length < 2 ^ (prefixWord ++ tailWord_989411).sum := by decide
  have hdescent : baseEnd_989411 < baseStart_989411 := by decide
  rcases family_descends (prefixWord ++ tailWord_989411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989415 : List Nat := [1, 1, 5, 3, 1, 2, 1, 6]
def baseStart_989415 : Nat := 118140960795 + 989415 * 2 ^ 59
def prefixEnd_989415 : Nat := 4983230072969 + 3 ^ 40 * 989415 * 2
def baseEnd_989415 : Nat := 150531988672104190507339

theorem tailTrace_989415 : CollatzResearch.WordTrace tailWord_989415 prefixEnd_989415 150531988672104190507339 := by
  unfold tailWord_989415
  simp only [CollatzResearch.WordTrace]
  refine ⟨36086929710525908474033699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24057953140350605649355799 36086929710525908474033699)
  ·
    refine ⟨54130394565788862711050549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36086929710525908474033699 54130394565788862711050549)
    ·
      refine ⟨5074724490542705879160989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54130394565788862711050549 5074724490542705879160989)
      ·
        refine ⟨1903021683953514704685371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5074724490542705879160989 1903021683953514704685371)
        ·
          refine ⟨2854532525930272057028057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1903021683953514704685371 2854532525930272057028057)
          ·
            refine ⟨2140899394447704042771043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2854532525930272057028057 2140899394447704042771043)
            ·
              refine ⟨3211349091671556064156565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2140899394447704042771043 3211349091671556064156565)
              ·
                refine ⟨150531988672104190507339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3211349091671556064156565 150531988672104190507339)
                ·
                  rfl

theorem cell20_989415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 6].length) (baseStart_989415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989415 prefixEnd_989415 := by exact prefixLift 989415
  have htrace : WordTrace (prefixWord ++ tailWord_989415) baseStart_989415 baseEnd_989415 := by
    simpa [prefixWord, tailWord_989415, baseEnd_989415] using wordTrace_append hprefix tailTrace_989415
  have hstable : (prefixWord ++ tailWord_989415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989415).length < 2 ^ (prefixWord ++ tailWord_989415).sum := by decide
  have hdescent : baseEnd_989415 < baseStart_989415 := by decide
  rcases family_descends (prefixWord ++ tailWord_989415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989421 : List Nat := [1, 5, 1, 2, 4, 1, 1, 3, 2]
def baseStart_989421 : Nat := 118140960795 + 989421 * 2 ^ 59
def prefixEnd_989421 : Nat := 4983230072969 + 3 ^ 40 * 989421 * 2
def baseEnd_989421 : Nat := 451598704579803217321993

theorem tailTrace_989421 : CollatzResearch.WordTrace tailWord_989421 prefixEnd_989421 451598704579803217321993 := by
  unfold tailWord_989421
  simp only [CollatzResearch.WordTrace]
  refine ⟨36087148548504171498752117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24058099032336114332501411 36087148548504171498752117)
  ·
    refine ⟨3383170176422266078008011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36087148548504171498752117 3383170176422266078008011)
    ·
      refine ⟨5074755264633399117012017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3383170176422266078008011 5074755264633399117012017)
      ·
        refine ⟨3806066448475049337759013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5074755264633399117012017 3806066448475049337759013)
        ·
          refine ⟨713637459089071750829815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3806066448475049337759013 713637459089071750829815)
          ·
            refine ⟨1070456188633607626244723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713637459089071750829815 1070456188633607626244723)
            ·
              refine ⟨1605684282950411439367085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070456188633607626244723 1605684282950411439367085)
              ·
                refine ⟨602131606106404289762657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1605684282950411439367085 602131606106404289762657)
                ·
                  refine ⟨451598704579803217321993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 602131606106404289762657 451598704579803217321993)
                  ·
                    rfl

theorem cell20_989421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_989421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989421 prefixEnd_989421 := by exact prefixLift 989421
  have htrace : WordTrace (prefixWord ++ tailWord_989421) baseStart_989421 baseEnd_989421 := by
    simpa [prefixWord, tailWord_989421, baseEnd_989421] using wordTrace_append hprefix tailTrace_989421
  have hstable : (prefixWord ++ tailWord_989421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989421).length < 2 ^ (prefixWord ++ tailWord_989421).sum := by decide
  have hdescent : baseEnd_989421 < baseStart_989421 := by decide
  rcases family_descends (prefixWord ++ tailWord_989421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989436 : List Nat := [2, 2, 2, 1, 4, 1, 8]
def baseStart_989436 : Nat := 118140960795 + 989436 * 2 ^ 59
def prefixEnd_989436 : Nat := 4983230072969 + 3 ^ 40 * 989436 * 2
def baseEnd_989436 : Nat := 50178394554281092424659

theorem tailTrace_989436 : CollatzResearch.WordTrace tailWord_989436 prefixEnd_989436 50178394554281092424659 := by
  unfold tailWord_989436
  simp only [CollatzResearch.WordTrace]
  refine ⟨18043847821724914530274081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24058463762299886040365441 18043847821724914530274081)
  ·
    refine ⟨13532885866293685897705561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18043847821724914530274081 13532885866293685897705561)
    ·
      refine ⟨10149664399720264423279171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13532885866293685897705561 10149664399720264423279171)
      ·
        refine ⟨15224496599580396634918757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10149664399720264423279171 15224496599580396634918757)
        ·
          refine ⟨2854593112421324369047267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15224496599580396634918757 2854593112421324369047267)
          ·
            refine ⟨4281889668631986553570901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854593112421324369047267 4281889668631986553570901)
            ·
              refine ⟨50178394554281092424659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4281889668631986553570901 50178394554281092424659)
              ·
                rfl

theorem cell20_989436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 8].length) (baseStart_989436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989436 prefixEnd_989436 := by exact prefixLift 989436
  have htrace : WordTrace (prefixWord ++ tailWord_989436) baseStart_989436 baseEnd_989436 := by
    simpa [prefixWord, tailWord_989436, baseEnd_989436] using wordTrace_append hprefix tailTrace_989436
  have hstable : (prefixWord ++ tailWord_989436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989436).length < 2 ^ (prefixWord ++ tailWord_989436).sum := by decide
  have hdescent : baseEnd_989436 < baseStart_989436 := by decide
  rcases family_descends (prefixWord ++ tailWord_989436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989443 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 5]
def baseStart_989443 : Nat := 118140960795 + 989443 * 2 ^ 59
def prefixEnd_989443 : Nat := 4983230072969 + 3 ^ 40 * 989443 * 2
def baseEnd_989443 : Nat := 451608745979268918588569

theorem tailTrace_989443 : CollatzResearch.WordTrace tailWord_989443 prefixEnd_989443 451608745979268918588569 := by
  unfold tailWord_989443
  simp only [CollatzResearch.WordTrace]
  refine ⟨36087950954424469256052983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24058633969616312837368655 36087950954424469256052983)
  ·
    refine ⟨54131926431636703884079475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36087950954424469256052983 54131926431636703884079475)
    ·
      refine ⟨81197889647455055826119213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54131926431636703884079475 81197889647455055826119213)
      ·
        refine ⟨30449208617795645934794705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81197889647455055826119213 30449208617795645934794705)
        ·
          refine ⟨22836906463346734451096029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30449208617795645934794705 22836906463346734451096029)
          ·
            refine ⟨8563839923755025419161011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22836906463346734451096029 8563839923755025419161011)
            ·
              refine ⟨12845759885632538128741517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8563839923755025419161011 12845759885632538128741517)
              ·
                refine ⟨4817159957112201798278069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12845759885632538128741517 4817159957112201798278069)
                ·
                  refine ⟨451608745979268918588569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4817159957112201798278069 451608745979268918588569)
                  ·
                    rfl

theorem cell20_989443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_989443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989443 prefixEnd_989443 := by exact prefixLift 989443
  have htrace : WordTrace (prefixWord ++ tailWord_989443) baseStart_989443 baseEnd_989443 := by
    simpa [prefixWord, tailWord_989443, baseEnd_989443] using wordTrace_append hprefix tailTrace_989443
  have hstable : (prefixWord ++ tailWord_989443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989443).length < 2 ^ (prefixWord ++ tailWord_989443).sum := by decide
  have hdescent : baseEnd_989443 < baseStart_989443 := by decide
  rcases family_descends (prefixWord ++ tailWord_989443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989470 : List Nat := [4, 3, 2, 1, 1, 1, 2, 6]
def baseStart_989470 : Nat := 118140960795 + 989470 * 2 ^ 59
def prefixEnd_989470 : Nat := 4983230072969 + 3 ^ 40 * 989470 * 2
def baseEnd_989470 : Nat := 150540356504992274896153

theorem tailTrace_989470 : CollatzResearch.WordTrace tailWord_989470 prefixEnd_989470 150540356504992274896153 := by
  unfold tailWord_989470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4511116965665831608410733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24059290483551101911523909 4511116965665831608410733)
  ·
    refine ⟨1691668862124686853154025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4511116965665831608410733 1691668862124686853154025)
    ·
      refine ⟨1268751646593515139865519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1691668862124686853154025 1268751646593515139865519)
      ·
        refine ⟨1903127469890272709798279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1268751646593515139865519 1903127469890272709798279)
        ·
          refine ⟨2854691204835409064697419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1903127469890272709798279 2854691204835409064697419)
          ·
            refine ⟨4282036807253113597046129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854691204835409064697419 4282036807253113597046129)
            ·
              refine ⟨3211527605439835197784597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4282036807253113597046129 3211527605439835197784597)
              ·
                refine ⟨150540356504992274896153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3211527605439835197784597 150540356504992274896153)
                ·
                  rfl

theorem cell20_989470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_989470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989470 prefixEnd_989470 := by exact prefixLift 989470
  have htrace : WordTrace (prefixWord ++ tailWord_989470) baseStart_989470 baseEnd_989470 := by
    simpa [prefixWord, tailWord_989470, baseEnd_989470] using wordTrace_append hprefix tailTrace_989470
  have hstable : (prefixWord ++ tailWord_989470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989470).length < 2 ^ (prefixWord ++ tailWord_989470).sum := by decide
  have hdescent : baseEnd_989470 < baseStart_989470 := by decide
  rcases family_descends (prefixWord ++ tailWord_989470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989488 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 8]
def baseStart_989488 : Nat := 118140960795 + 989488 * 2 ^ 59
def prefixEnd_989488 : Nat := 4983230072969 + 3 ^ 40 * 989488 * 2
def baseEnd_989488 : Nat := 451629285205448762088385

theorem tailTrace_989488 : CollatzResearch.WordTrace tailWord_989488 prefixEnd_989488 451629285205448762088385 := by
  unfold tailWord_989488
  simp only [CollatzResearch.WordTrace]
  refine ⟨18044796119630720970720559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24059728159507627960960745 18044796119630720970720559)
  ·
    refine ⟨27067194179446081456080839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18044796119630720970720559 27067194179446081456080839)
    ·
      refine ⟨40600791269169122184121259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27067194179446081456080839 40600791269169122184121259)
      ·
        refine ⟨60901186903753683276181889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40600791269169122184121259 60901186903753683276181889)
        ·
          refine ⟨45675890177815262457136417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60901186903753683276181889 45675890177815262457136417)
          ·
            refine ⟨34256917633361446842852313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45675890177815262457136417 34256917633361446842852313)
            ·
              refine ⟨25692688225021085132139235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34256917633361446842852313 25692688225021085132139235)
              ·
                refine ⟨38539032337531627698208853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25692688225021085132139235 38539032337531627698208853)
                ·
                  refine ⟨451629285205448762088385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38539032337531627698208853 451629285205448762088385)
                  ·
                    rfl

theorem cell20_989488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_989488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989488 prefixEnd_989488 := by exact prefixLift 989488
  have htrace : WordTrace (prefixWord ++ tailWord_989488) baseStart_989488 baseEnd_989488 := by
    simpa [prefixWord, tailWord_989488, baseEnd_989488] using wordTrace_append hprefix tailTrace_989488
  have hstable : (prefixWord ++ tailWord_989488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989488).length < 2 ^ (prefixWord ++ tailWord_989488).sum := by decide
  have hdescent : baseEnd_989488 < baseStart_989488 := by decide
  rcases family_descends (prefixWord ++ tailWord_989488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989498 : List Nat := [3, 1, 1, 1, 4, 2, 1, 4, 3]
def baseStart_989498 : Nat := 118140960795 + 989498 * 2 ^ 59
def prefixEnd_989498 : Nat := 4983230072969 + 3 ^ 40 * 989498 * 2
def baseEnd_989498 : Nat := 451633849477933171755011

theorem tailTrace_989498 : CollatzResearch.WordTrace tailWord_989498 prefixEnd_989498 451633849477933171755011 := by
  unfold tailWord_989498
  simp only [CollatzResearch.WordTrace]
  refine ⟨9022489242306303412326287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24059971312816809099536765 9022489242306303412326287)
  ·
    refine ⟨13533733863459455118489431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9022489242306303412326287 13533733863459455118489431)
    ·
      refine ⟨20300600795189182677734147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13533733863459455118489431 20300600795189182677734147)
      ·
        refine ⟨30450901192783774016601221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20300600795189182677734147 30450901192783774016601221)
        ·
          refine ⟨5709543973646957628112729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30450901192783774016601221 5709543973646957628112729)
          ·
            refine ⟨4282157980235218221084547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5709543973646957628112729 4282157980235218221084547)
            ·
              refine ⟨6423236970352827331626821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4282157980235218221084547 6423236970352827331626821)
              ·
                refine ⟨1204356931941155124680029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6423236970352827331626821 1204356931941155124680029)
                ·
                  refine ⟨451633849477933171755011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1204356931941155124680029 451633849477933171755011)
                  ·
                    rfl

theorem cell20_989498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_989498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989498 prefixEnd_989498 := by exact prefixLift 989498
  have htrace : WordTrace (prefixWord ++ tailWord_989498) baseStart_989498 baseEnd_989498 := by
    simpa [prefixWord, tailWord_989498, baseEnd_989498] using wordTrace_append hprefix tailTrace_989498
  have hstable : (prefixWord ++ tailWord_989498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989498).length < 2 ^ (prefixWord ++ tailWord_989498).sum := by decide
  have hdescent : baseEnd_989498 < baseStart_989498 := by decide
  rcases family_descends (prefixWord ++ tailWord_989498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989512 : List Nat := [2, 1, 3, 1, 1, 2, 5, 5]
def baseStart_989512 : Nat := 118140960795 + 989512 * 2 ^ 59
def prefixEnd_989512 : Nat := 4983230072969 + 3 ^ 40 * 989512 * 2
def baseEnd_989512 : Nat := 150546746486470448429429

theorem tailTrace_989512 : CollatzResearch.WordTrace tailWord_989512 prefixEnd_989512 150546746486470448429429 := by
  unfold tailWord_989512
  simp only [CollatzResearch.WordTrace]
  refine ⟨18045233795587247020157395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24060311727449662693543193 18045233795587247020157395)
  ·
    refine ⟨27067850693380870530236093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18045233795587247020157395 27067850693380870530236093)
    ·
      refine ⟨10150444010017826448838535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27067850693380870530236093 10150444010017826448838535)
      ·
        refine ⟨15225666015026739673257803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10150444010017826448838535 15225666015026739673257803)
        ·
          refine ⟨22838499022540109509886705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15225666015026739673257803 22838499022540109509886705)
          ·
            refine ⟨17128874266905082132415029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22838499022540109509886705 17128874266905082132415029)
            ·
              refine ⟨1605831962522351449913909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17128874266905082132415029 1605831962522351449913909)
              ·
                refine ⟨150546746486470448429429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1605831962522351449913909 150546746486470448429429)
                ·
                  rfl

theorem cell20_989512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_989512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989512 prefixEnd_989512 := by exact prefixLift 989512
  have htrace : WordTrace (prefixWord ++ tailWord_989512) baseStart_989512 baseEnd_989512 := by
    simpa [prefixWord, tailWord_989512, baseEnd_989512] using wordTrace_append hprefix tailTrace_989512
  have hstable : (prefixWord ++ tailWord_989512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989512).length < 2 ^ (prefixWord ++ tailWord_989512).sum := by decide
  have hdescent : baseEnd_989512 < baseStart_989512 := by decide
  rcases family_descends (prefixWord ++ tailWord_989512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989629 : List Nat := [1, 4, 1, 2, 2, 2, 4, 1, 3]
def baseStart_989629 : Nat := 118140960795 + 989629 * 2 ^ 59
def prefixEnd_989629 : Nat := 4983230072969 + 3 ^ 40 * 989629 * 2
def baseEnd_989629 : Nat := 451693641447478938387809

theorem tailTrace_989629 : CollatzResearch.WordTrace tailWord_989629 prefixEnd_989629 451693641447478938387809 := by
  unfold tailWord_989629
  simp only [CollatzResearch.WordTrace]
  refine ⟨36094734931750623022323941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24063156621167082014882627 36094734931750623022323941)
  ·
    refine ⟨6767762799703241816685739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36094734931750623022323941 6767762799703241816685739)
    ·
      refine ⟨10151644199554862725028609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6767762799703241816685739 10151644199554862725028609)
      ·
        refine ⟨7613733149666147043771457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10151644199554862725028609 7613733149666147043771457)
        ·
          refine ⟨5710299862249610282828593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7613733149666147043771457 5710299862249610282828593)
          ·
            refine ⟨4282724896687207712121445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5710299862249610282828593 4282724896687207712121445)
            ·
              refine ⟨803010918128851446022771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4282724896687207712121445 803010918128851446022771)
              ·
                refine ⟨1204516377193277169034157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803010918128851446022771 1204516377193277169034157)
                ·
                  refine ⟨451693641447478938387809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1204516377193277169034157 451693641447478938387809)
                  ·
                    rfl

theorem cell20_989629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_989629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989629 prefixEnd_989629 := by exact prefixLift 989629
  have htrace : WordTrace (prefixWord ++ tailWord_989629) baseStart_989629 baseEnd_989629 := by
    simpa [prefixWord, tailWord_989629, baseEnd_989629] using wordTrace_append hprefix tailTrace_989629
  have hstable : (prefixWord ++ tailWord_989629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989629).length < 2 ^ (prefixWord ++ tailWord_989629).sum := by decide
  have hdescent : baseEnd_989629 < baseStart_989629 := by decide
  rcases family_descends (prefixWord ++ tailWord_989629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989666 : List Nat := [3, 3, 3, 2, 1, 2, 2, 2, 2]
def baseStart_989666 : Nat := 118140960795 + 989666 * 2 ^ 59
def prefixEnd_989666 : Nat := 4983230072969 + 3 ^ 40 * 989666 * 2
def baseEnd_989666 : Nat := 451710529255671254154325

theorem tailTrace_989666 : CollatzResearch.WordTrace tailWord_989666 prefixEnd_989666 451710529255671254154325 := by
  unfold tailWord_989666
  simp only [CollatzResearch.WordTrace]
  refine ⟨9024021108154144585355213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24064056288411052227613901 9024021108154144585355213)
  ·
    refine ⟨3384007915557804219508205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9024021108154144585355213 3384007915557804219508205)
    ·
      refine ⟨1269002968334176582315577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3384007915557804219508205 1269002968334176582315577)
      ·
        refine ⟨951752226250632436736683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1269002968334176582315577 951752226250632436736683)
        ·
          refine ⟨1427628339375948655105025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951752226250632436736683 1427628339375948655105025)
          ·
            refine ⟨1070721254531961491328769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1427628339375948655105025 1070721254531961491328769)
            ·
              refine ⟨803040940898971118496577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070721254531961491328769 803040940898971118496577)
              ·
                refine ⟨602280705674228338872433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 803040940898971118496577 602280705674228338872433)
                ·
                  refine ⟨451710529255671254154325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 602280705674228338872433 451710529255671254154325)
                  ·
                    rfl

theorem cell20_989666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_989666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989666 prefixEnd_989666 := by exact prefixLift 989666
  have htrace : WordTrace (prefixWord ++ tailWord_989666) baseStart_989666 baseEnd_989666 := by
    simpa [prefixWord, tailWord_989666, baseEnd_989666] using wordTrace_append hprefix tailTrace_989666
  have hstable : (prefixWord ++ tailWord_989666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989666).length < 2 ^ (prefixWord ++ tailWord_989666).sum := by decide
  have hdescent : baseEnd_989666 < baseStart_989666 := by decide
  rcases family_descends (prefixWord ++ tailWord_989666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989667 : List Nat := [1, 1, 1, 6, 3, 1, 2, 2, 3]
def baseStart_989667 : Nat := 118140960795 + 989667 * 2 ^ 59
def prefixEnd_989667 : Nat := 4983230072969 + 3 ^ 40 * 989667 * 2
def baseEnd_989667 : Nat := 451710985682919695120987

theorem tailTrace_989667 : CollatzResearch.WordTrace tailWord_989667 prefixEnd_989667 451710985682919695120987 := by
  unfold tailWord_989667
  simp only [CollatzResearch.WordTrace]
  refine ⟨36096120905612955512207255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24064080603741970341471503 36096120905612955512207255)
  ·
    refine ⟨54144181358419433268310883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36096120905612955512207255 54144181358419433268310883)
    ·
      refine ⟨81216272037629149902466325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54144181358419433268310883 81216272037629149902466325)
      ·
        refine ⟨3807012751763866401678109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81216272037629149902466325 3807012751763866401678109)
        ·
          refine ⟨1427629781911449900629291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3807012751763866401678109 1427629781911449900629291)
          ·
            refine ⟨2141444672867174850943937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427629781911449900629291 2141444672867174850943937)
            ·
              refine ⟨1606083504650381138207953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2141444672867174850943937 1606083504650381138207953)
              ·
                refine ⟨1204562628487785853655965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1606083504650381138207953 1204562628487785853655965)
                ·
                  refine ⟨451710985682919695120987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1204562628487785853655965 451710985682919695120987)
                  ·
                    rfl

theorem cell20_989667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 3].length) (baseStart_989667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989667 prefixEnd_989667 := by exact prefixLift 989667
  have htrace : WordTrace (prefixWord ++ tailWord_989667) baseStart_989667 baseEnd_989667 := by
    simpa [prefixWord, tailWord_989667, baseEnd_989667] using wordTrace_append hprefix tailTrace_989667
  have hstable : (prefixWord ++ tailWord_989667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989667).length < 2 ^ (prefixWord ++ tailWord_989667).sum := by decide
  have hdescent : baseEnd_989667 < baseStart_989667 := by decide
  rcases family_descends (prefixWord ++ tailWord_989667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989719 : List Nat := [1, 1, 3, 6, 1, 1, 7]
def baseStart_989719 : Nat := 118140960795 + 989719 * 2 ^ 59
def prefixEnd_989719 : Nat := 4983230072969 + 3 ^ 40 * 989719 * 2
def baseEnd_989719 : Nat := 50192746655537625043049

theorem tailTrace_989719 : CollatzResearch.WordTrace tailWord_989719 prefixEnd_989719 50192746655537625043049 := by
  unfold tailWord_989719
  simp only [CollatzResearch.WordTrace]
  refine ⟨36098017501424568393100211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24065345000949712262066807 36098017501424568393100211)
  ·
    refine ⟨54147026252136852589650317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36098017501424568393100211 54147026252136852589650317)
    ·
      refine ⟨20305134844551319721118869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54147026252136852589650317 20305134844551319721118869)
      ·
        refine ⟨951803195838343111927447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20305134844551319721118869 951803195838343111927447)
        ·
          refine ⟨1427704793757514667891171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951803195838343111927447 1427704793757514667891171)
          ·
            refine ⟨2141557190636272001836757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427704793757514667891171 2141557190636272001836757)
            ·
              refine ⟨50192746655537625043049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2141557190636272001836757 50192746655537625043049)
              ·
                rfl

theorem cell20_989719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 7].length) (baseStart_989719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989719 prefixEnd_989719 := by exact prefixLift 989719
  have htrace : WordTrace (prefixWord ++ tailWord_989719) baseStart_989719 baseEnd_989719 := by
    simpa [prefixWord, tailWord_989719, baseEnd_989719] using wordTrace_append hprefix tailTrace_989719
  have hstable : (prefixWord ++ tailWord_989719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989719).length < 2 ^ (prefixWord ++ tailWord_989719).sum := by decide
  have hdescent : baseEnd_989719 < baseStart_989719 := by decide
  rcases family_descends (prefixWord ++ tailWord_989719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989750 : List Nat := [5, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_989750 : Nat := 118140960795 + 989750 * 2 ^ 59
def prefixEnd_989750 : Nat := 4983230072969 + 3 ^ 40 * 989750 * 2
def baseEnd_989750 : Nat := 451748869144540295353981

theorem tailTrace_989750 : CollatzResearch.WordTrace tailWord_989750 prefixEnd_989750 451748869144540295353981 := by
  unfold tailWord_989750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2256196760269516292967419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24066098776208173791652469 2256196760269516292967419)
  ·
    refine ⟨3384295140404274439451129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2256196760269516292967419 3384295140404274439451129)
    ·
      refine ⟨2538221355303205829588347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3384295140404274439451129 2538221355303205829588347)
      ·
        refine ⟨3807332032954808744382521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2538221355303205829588347 3807332032954808744382521)
        ·
          refine ⟨2855499024716106558286891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3807332032954808744382521 2855499024716106558286891)
          ·
            refine ⟨4283248537074159837430337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2855499024716106558286891 4283248537074159837430337)
            ·
              refine ⟨3212436402805619878072753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4283248537074159837430337 3212436402805619878072753)
              ·
                refine ⟨2409327302104214908554565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3212436402805619878072753 2409327302104214908554565)
                ·
                  refine ⟨451748869144540295353981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2409327302104214908554565 451748869144540295353981)
                  ·
                    rfl

theorem cell20_989750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_989750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989750 prefixEnd_989750 := by exact prefixLift 989750
  have htrace : WordTrace (prefixWord ++ tailWord_989750) baseStart_989750 baseEnd_989750 := by
    simpa [prefixWord, tailWord_989750, baseEnd_989750] using wordTrace_append hprefix tailTrace_989750
  have hstable : (prefixWord ++ tailWord_989750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989750).length < 2 ^ (prefixWord ++ tailWord_989750).sum := by decide
  have hdescent : baseEnd_989750 < baseStart_989750 := by decide
  rcases family_descends (prefixWord ++ tailWord_989750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989757 : List Nat := [1, 4, 1, 3, 2, 1, 4, 4]
def baseStart_989757 : Nat := 118140960795 + 989757 * 2 ^ 59
def prefixEnd_989757 : Nat := 4983230072969 + 3 ^ 40 * 989757 * 2
def baseEnd_989757 : Nat := 150584021378426460706873

theorem tailTrace_989757 : CollatzResearch.WordTrace tailWord_989757 prefixEnd_989757 150584021378426460706873 := by
  unfold tailWord_989757
  simp only [CollatzResearch.WordTrace]
  refine ⟨36099403475286900882983525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24066268983524600588655683 36099403475286900882983525)
  ·
    refine ⟨6768638151616293915559411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36099403475286900882983525 6768638151616293915559411)
    ·
      refine ⟨10152957227424440873339117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6768638151616293915559411 10152957227424440873339117)
      ·
        refine ⟨3807358960284165327502169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10152957227424440873339117 3807358960284165327502169)
        ·
          refine ⟨2855519220213123995626627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3807358960284165327502169 2855519220213123995626627)
          ·
            refine ⟨4283278830319685993439941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2855519220213123995626627 4283278830319685993439941)
            ·
              refine ⟨803114780684941123769989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4283278830319685993439941 803114780684941123769989)
              ·
                refine ⟨150584021378426460706873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 803114780684941123769989 150584021378426460706873)
                ·
                  rfl

theorem cell20_989757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 4].length) (baseStart_989757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989757 prefixEnd_989757 := by exact prefixLift 989757
  have htrace : WordTrace (prefixWord ++ tailWord_989757) baseStart_989757 baseEnd_989757 := by
    simpa [prefixWord, tailWord_989757, baseEnd_989757] using wordTrace_append hprefix tailTrace_989757
  have hstable : (prefixWord ++ tailWord_989757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989757).length < 2 ^ (prefixWord ++ tailWord_989757).sum := by decide
  have hdescent : baseEnd_989757 < baseStart_989757 := by decide
  rcases family_descends (prefixWord ++ tailWord_989757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989767 : List Nat := [1, 1, 4, 1, 4, 3, 1, 3, 2]
def baseStart_989767 : Nat := 118140960795 + 989767 * 2 ^ 59
def prefixEnd_989767 : Nat := 4983230072969 + 3 ^ 40 * 989767 * 2
def baseEnd_989767 : Nat := 451756628407763791787245

theorem tailTrace_989767 : CollatzResearch.WordTrace tailWord_989767 prefixEnd_989767 451756628407763791787245 := by
  unfold tailWord_989767
  simp only [CollatzResearch.WordTrace]
  refine ⟨36099768205250672590847555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24066512136833781727231703 36099768205250672590847555)
  ·
    refine ⟨54149652307876008886271333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36099768205250672590847555 54149652307876008886271333)
    ·
      refine ⟨10153059807726751666175875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54149652307876008886271333 10153059807726751666175875)
      ·
        refine ⟨15229589711590127499263813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10153059807726751666175875 15229589711590127499263813)
        ·
          refine ⟨2855548070923148906111965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15229589711590127499263813 2855548070923148906111965)
          ·
            refine ⟨1070830526596180839791987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2855548070923148906111965 1070830526596180839791987)
            ·
              refine ⟨1606245789894271259687981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070830526596180839791987 1606245789894271259687981)
              ·
                refine ⟨602342171210351722382993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1606245789894271259687981 602342171210351722382993)
                ·
                  refine ⟨451756628407763791787245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 602342171210351722382993 451756628407763791787245)
                  ·
                    rfl

theorem cell20_989767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 2].length) (baseStart_989767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989767 prefixEnd_989767 := by exact prefixLift 989767
  have htrace : WordTrace (prefixWord ++ tailWord_989767) baseStart_989767 baseEnd_989767 := by
    simpa [prefixWord, tailWord_989767, baseEnd_989767] using wordTrace_append hprefix tailTrace_989767
  have hstable : (prefixWord ++ tailWord_989767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989767).length < 2 ^ (prefixWord ++ tailWord_989767).sum := by decide
  have hdescent : baseEnd_989767 < baseStart_989767 := by decide
  rcases family_descends (prefixWord ++ tailWord_989767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989794 : List Nat := [3, 3, 2, 3, 2, 1, 2, 1, 3]
def baseStart_989794 : Nat := 118140960795 + 989794 * 2 ^ 59
def prefixEnd_989794 : Nat := 4983230072969 + 3 ^ 40 * 989794 * 2
def baseEnd_989794 : Nat := 451768951943471697887135

theorem tailTrace_989794 : CollatzResearch.WordTrace tailWord_989794 prefixEnd_989794 451768951943471697887135 := by
  unfold tailWord_989794
  simp only [CollatzResearch.WordTrace]
  refine ⟨9025188244038214050520109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24067168650768570801386957 9025188244038214050520109)
  ·
    refine ⟨3384445591514330268945041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9025188244038214050520109 3384445591514330268945041)
    ·
      refine ⟨2538334193635747701708781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3384445591514330268945041 2538334193635747701708781)
      ·
        refine ⟨951875322613405388140793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2538334193635747701708781 951875322613405388140793)
        ·
          refine ⟨713906491960054041105595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 951875322613405388140793 713906491960054041105595)
          ·
            refine ⟨1070859737940081061658393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713906491960054041105595 1070859737940081061658393)
            ·
              refine ⟨803144803455060796243795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070859737940081061658393 803144803455060796243795)
              ·
                refine ⟨1204717205182591194365693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803144803455060796243795 1204717205182591194365693)
                ·
                  refine ⟨451768951943471697887135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1204717205182591194365693 451768951943471697887135)
                  ·
                    rfl

theorem cell20_989794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_989794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989794 prefixEnd_989794 := by exact prefixLift 989794
  have htrace : WordTrace (prefixWord ++ tailWord_989794) baseStart_989794 baseEnd_989794 := by
    simpa [prefixWord, tailWord_989794, baseEnd_989794] using wordTrace_append hprefix tailTrace_989794
  have hstable : (prefixWord ++ tailWord_989794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989794).length < 2 ^ (prefixWord ++ tailWord_989794).sum := by decide
  have hdescent : baseEnd_989794 < baseStart_989794 := by decide
  rcases family_descends (prefixWord ++ tailWord_989794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989802 : List Nat := [3, 1, 3, 2, 1, 1, 3, 3, 3]
def baseStart_989802 : Nat := 118140960795 + 989802 * 2 ^ 59
def prefixEnd_989802 : Nat := 4983230072969 + 3 ^ 40 * 989802 * 2
def baseEnd_989802 : Nat := 451772603361459225620435

theorem tailTrace_989802 : CollatzResearch.WordTrace tailWord_989802 prefixEnd_989802 451772603361459225620435 := by
  unfold tailWord_989802
  simp only [CollatzResearch.WordTrace]
  refine ⟨9025261190030968392092915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24067363173415915712247773 9025261190030968392092915)
  ·
    refine ⟨13537891785046452588139373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9025261190030968392092915 13537891785046452588139373)
    ·
      refine ⟨5076709419392419720552265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13537891785046452588139373 5076709419392419720552265)
      ·
        refine ⟨3807532064544314790414199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5076709419392419720552265 3807532064544314790414199)
        ·
          refine ⟨5711298096816472185621299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3807532064544314790414199 5711298096816472185621299)
          ·
            refine ⟨8566947145224708278431949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5711298096816472185621299 8566947145224708278431949)
            ·
              refine ⟨3212605179459265604411981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8566947145224708278431949 3212605179459265604411981)
              ·
                refine ⟨1204726942297224601654493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3212605179459265604411981 1204726942297224601654493)
                ·
                  refine ⟨451772603361459225620435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1204726942297224601654493 451772603361459225620435)
                  ·
                    rfl

theorem cell20_989802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_989802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989802 prefixEnd_989802 := by exact prefixLift 989802
  have htrace : WordTrace (prefixWord ++ tailWord_989802) baseStart_989802 baseEnd_989802 := by
    simpa [prefixWord, tailWord_989802, baseEnd_989802] using wordTrace_append hprefix tailTrace_989802
  have hstable : (prefixWord ++ tailWord_989802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989802).length < 2 ^ (prefixWord ++ tailWord_989802).sum := by decide
  have hdescent : baseEnd_989802 < baseStart_989802 := by decide
  rcases family_descends (prefixWord ++ tailWord_989802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989850 : List Nat := [3, 1, 1, 6, 1, 2, 1, 5]
def baseStart_989850 : Nat := 118140960795 + 989850 * 2 ^ 59
def prefixEnd_989850 : Nat := 4983230072969 + 3 ^ 40 * 989850 * 2
def baseEnd_989850 : Nat := 150598170623128130673413

theorem tailTrace_989850 : CollatzResearch.WordTrace tailWord_989850 prefixEnd_989850 150598170623128130673413 := by
  unfold tailWord_989850
  simp only [CollatzResearch.WordTrace]
  refine ⟨9025698865987494441529751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24068530309299985177412669 9025698865987494441529751)
  ·
    refine ⟨13538548298981241662294627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9025698865987494441529751 13538548298981241662294627)
    ·
      refine ⟨20307822448471862493441941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13538548298981241662294627 20307822448471862493441941)
      ·
        refine ⟨951929177272118554380091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20307822448471862493441941 951929177272118554380091)
        ·
          refine ⟨1427893765908177831570137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951929177272118554380091 1427893765908177831570137)
          ·
            refine ⟨1070920324431133373677603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1427893765908177831570137 1070920324431133373677603)
            ·
              refine ⟨1606380486646700060516405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070920324431133373677603 1606380486646700060516405)
              ·
                refine ⟨150598170623128130673413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1606380486646700060516405 150598170623128130673413)
                ·
                  rfl

theorem cell20_989850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_989850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989850 prefixEnd_989850 := by exact prefixLift 989850
  have htrace : WordTrace (prefixWord ++ tailWord_989850) baseStart_989850 baseEnd_989850 := by
    simpa [prefixWord, tailWord_989850, baseEnd_989850] using wordTrace_append hprefix tailTrace_989850
  have hstable : (prefixWord ++ tailWord_989850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989850).length < 2 ^ (prefixWord ++ tailWord_989850).sum := by decide
  have hdescent : baseEnd_989850 < baseStart_989850 := by decide
  rcases family_descends (prefixWord ++ tailWord_989850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989892 : List Nat := [2, 3, 3, 1, 1, 3, 7]
def baseStart_989892 : Nat := 118140960795 + 989892 * 2 ^ 59
def prefixEnd_989892 : Nat := 4983230072969 + 3 ^ 40 * 989892 * 2
def baseEnd_989892 : Nat := 50201520201535434735563

theorem tailTrace_989892 : CollatzResearch.WordTrace tailWord_989892 prefixEnd_989892 50201520201535434735563 := by
  unfold tailWord_989892
  simp only [CollatzResearch.WordTrace]
  refine ⟨18052163664898909469573965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24069551553198545959431953 18052163664898909469573965)
  ·
    refine ⟨6769561374337091051090237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18052163664898909469573965 6769561374337091051090237)
    ·
      refine ⟨2538585515376409144158839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6769561374337091051090237 2538585515376409144158839)
      ·
        refine ⟨3807878273064613716238259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2538585515376409144158839 3807878273064613716238259)
        ·
          refine ⟨5711817409596920574357389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3807878273064613716238259 5711817409596920574357389)
          ·
            refine ⟨2141931528598845215384021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5711817409596920574357389 2141931528598845215384021)
            ·
              refine ⟨50201520201535434735563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2141931528598845215384021 50201520201535434735563)
              ·
                rfl

theorem cell20_989892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 7].length) (baseStart_989892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989892 prefixEnd_989892 := by exact prefixLift 989892
  have htrace : WordTrace (prefixWord ++ tailWord_989892) baseStart_989892 baseEnd_989892 := by
    simpa [prefixWord, tailWord_989892, baseEnd_989892] using wordTrace_append hprefix tailTrace_989892
  have hstable : (prefixWord ++ tailWord_989892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989892).length < 2 ^ (prefixWord ++ tailWord_989892).sum := by decide
  have hdescent : baseEnd_989892 < baseStart_989892 := by decide
  rcases family_descends (prefixWord ++ tailWord_989892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989902 : List Nat := [4, 1, 1, 1, 3, 2, 2, 4, 2]
def baseStart_989902 : Nat := 118140960795 + 989902 * 2 ^ 59
def prefixEnd_989902 : Nat := 4983230072969 + 3 ^ 40 * 989902 * 2
def baseEnd_989902 : Nat := 451818246086303322286693

theorem tailTrace_989902 : CollatzResearch.WordTrace tailWord_989902 prefixEnd_989902 451818246086303322286693 := by
  unfold tailWord_989902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4513086507470198830876495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24069794706507727098007973 4513086507470198830876495)
  ·
    refine ⟨6769629761205298246314743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4513086507470198830876495 6769629761205298246314743)
    ·
      refine ⟨10154444641807947369472115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6769629761205298246314743 10154444641807947369472115)
      ·
        refine ⟨15231666962711921054208173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10154444641807947369472115 15231666962711921054208173)
        ·
          refine ⟨5711875111016970395328065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15231666962711921054208173 5711875111016970395328065)
          ·
            refine ⟨4283906333262727796496049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5711875111016970395328065 4283906333262727796496049)
            ·
              refine ⟨3212929749947045847372037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4283906333262727796496049 3212929749947045847372037)
              ·
                refine ⟨602424328115071096382257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3212929749947045847372037 602424328115071096382257)
                ·
                  refine ⟨451818246086303322286693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 602424328115071096382257 451818246086303322286693)
                  ·
                    rfl

theorem cell20_989902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_989902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989902 prefixEnd_989902 := by exact prefixLift 989902
  have htrace : WordTrace (prefixWord ++ tailWord_989902) baseStart_989902 baseEnd_989902 := by
    simpa [prefixWord, tailWord_989902, baseEnd_989902] using wordTrace_append hprefix tailTrace_989902
  have hstable : (prefixWord ++ tailWord_989902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989902).length < 2 ^ (prefixWord ++ tailWord_989902).sum := by decide
  have hdescent : baseEnd_989902 < baseStart_989902 := by decide
  rcases family_descends (prefixWord ++ tailWord_989902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989913 : List Nat := [1, 2, 1, 2, 3, 2, 2, 7]
def baseStart_989913 : Nat := 118140960795 + 989913 * 2 ^ 59
def prefixEnd_989913 : Nat := 4983230072969 + 3 ^ 40 * 989913 * 2
def baseEnd_989913 : Nat := 150607755595345390973327

theorem tailTrace_989913 : CollatzResearch.WordTrace tailWord_989913 prefixEnd_989913 150607755595345390973327 := by
  unfold tailWord_989913
  simp only [CollatzResearch.WordTrace]
  refine ⟨36105093262721739525662393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24070062175147826350441595 36105093262721739525662393)
  ·
    refine ⟨27078819947041304644246795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36105093262721739525662393 27078819947041304644246795)
    ·
      refine ⟨40618229920561956966370193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27078819947041304644246795 40618229920561956966370193)
      ·
        refine ⟨30463672440421467724777645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40618229920561956966370193 30463672440421467724777645)
        ·
          refine ⟨11423877165158050396791617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30463672440421467724777645 11423877165158050396791617)
          ·
            refine ⟨8567907873868537797593713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11423877165158050396791617 8567907873868537797593713)
            ·
              refine ⟨6425930905401403348195285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8567907873868537797593713 6425930905401403348195285)
              ·
                refine ⟨150607755595345390973327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6425930905401403348195285 150607755595345390973327)
                ·
                  rfl

theorem cell20_989913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 7].length) (baseStart_989913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989913 prefixEnd_989913 := by exact prefixLift 989913
  have htrace : WordTrace (prefixWord ++ tailWord_989913) baseStart_989913 baseEnd_989913 := by
    simpa [prefixWord, tailWord_989913, baseEnd_989913] using wordTrace_append hprefix tailTrace_989913
  have hstable : (prefixWord ++ tailWord_989913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989913).length < 2 ^ (prefixWord ++ tailWord_989913).sum := by decide
  have hdescent : baseEnd_989913 < baseStart_989913 := by decide
  rcases family_descends (prefixWord ++ tailWord_989913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989923 : List Nat := [1, 1, 1, 7, 1, 1, 2, 2, 4]
def baseStart_989923 : Nat := 118140960795 + 989923 * 2 ^ 59
def prefixEnd_989923 : Nat := 4983230072969 + 3 ^ 40 * 989923 * 2
def baseEnd_989923 : Nat := 451827831058520582586607

theorem tailTrace_989923 : CollatzResearch.WordTrace tailWord_989923 prefixEnd_989923 451827831058520582586607 := by
  unfold tailWord_989923
  simp only [CollatzResearch.WordTrace]
  refine ⟨36105457992685511233526423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24070305328457007489017615 36105457992685511233526423)
  ·
    refine ⟨54158186989028266850289635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36105457992685511233526423 54158186989028266850289635)
    ·
      refine ⟨81237280483542400275434453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54158186989028266850289635 81237280483542400275434453)
      ·
        refine ⟨1903998761333025006455495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 81237280483542400275434453 1903998761333025006455495)
        ·
          refine ⟨2855998141999537509683243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1903998761333025006455495 2855998141999537509683243)
          ·
            refine ⟨4283997212999306264524865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2855998141999537509683243 4283997212999306264524865)
            ·
              refine ⟨3212997909749479698393649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4283997212999306264524865 3212997909749479698393649)
              ·
                refine ⟨2409748432312109773795237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3212997909749479698393649 2409748432312109773795237)
                ·
                  refine ⟨451827831058520582586607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2409748432312109773795237 451827831058520582586607)
                  ·
                    rfl

theorem cell20_989923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 4].length) (baseStart_989923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989923 prefixEnd_989923 := by exact prefixLift 989923
  have htrace : WordTrace (prefixWord ++ tailWord_989923) baseStart_989923 baseEnd_989923 := by
    simpa [prefixWord, tailWord_989923, baseEnd_989923] using wordTrace_append hprefix tailTrace_989923
  have hstable : (prefixWord ++ tailWord_989923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989923).length < 2 ^ (prefixWord ++ tailWord_989923).sum := by decide
  have hdescent : baseEnd_989923 < baseStart_989923 := by decide
  rcases family_descends (prefixWord ++ tailWord_989923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989954 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_989954 : Nat := 118140960795 + 989954 * 2 ^ 59
def prefixEnd_989954 : Nat := 4983230072969 + 3 ^ 40 * 989954 * 2
def baseEnd_989954 : Nat := 451841980303222252553147

theorem tailTrace_989954 : CollatzResearch.WordTrace tailWord_989954 prefixEnd_989954 451841980303222252553147 := by
  unfold tailWord_989954
  simp only [CollatzResearch.WordTrace]
  refine ⟨9026647163893300881976229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24071059103715469018603277 9026647163893300881976229)
  ·
    refine ⟨1692496343229993915370543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9026647163893300881976229 1692496343229993915370543)
    ·
      refine ⟨2538744514844990873055815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1692496343229993915370543 2538744514844990873055815)
      ·
        refine ⟨3808116772267486309583723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2538744514844990873055815 3808116772267486309583723)
        ·
          refine ⟨5712175158401229464375585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3808116772267486309583723 5712175158401229464375585)
          ·
            refine ⟨4284131368800922098281689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5712175158401229464375585 4284131368800922098281689)
            ·
              refine ⟨3213098526600691573711267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4284131368800922098281689 3213098526600691573711267)
              ·
                refine ⟨4819647789901037360566901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3213098526600691573711267 4819647789901037360566901)
                ·
                  refine ⟨451841980303222252553147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4819647789901037360566901 451841980303222252553147)
                  ·
                    rfl

theorem cell20_989954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_989954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989954 prefixEnd_989954 := by exact prefixLift 989954
  have htrace : WordTrace (prefixWord ++ tailWord_989954) baseStart_989954 baseEnd_989954 := by
    simpa [prefixWord, tailWord_989954, baseEnd_989954] using wordTrace_append hprefix tailTrace_989954
  have hstable : (prefixWord ++ tailWord_989954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989954).length < 2 ^ (prefixWord ++ tailWord_989954).sum := by decide
  have hdescent : baseEnd_989954 < baseStart_989954 := by decide
  rcases family_descends (prefixWord ++ tailWord_989954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989961 : List Nat := [1, 2, 1, 1, 3, 2, 2, 6, 2]
def baseStart_989961 : Nat := 118140960795 + 989961 * 2 ^ 59
def prefixEnd_989961 : Nat := 4983230072969 + 3 ^ 40 * 989961 * 2
def baseEnd_989961 : Nat := 451845175293961339319785

theorem tailTrace_989961 : CollatzResearch.WordTrace tailWord_989961 prefixEnd_989961 451845175293961339319785 := by
  unfold tailWord_989961
  simp only [CollatzResearch.WordTrace]
  refine ⟨36106843966547843723409737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24071229311031895815606491 36106843966547843723409737)
  ·
    refine ⟨27080132974910882792557303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36106843966547843723409737 27080132974910882792557303)
    ·
      refine ⟨40620199462366324188835955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27080132974910882792557303 40620199462366324188835955)
      ·
        refine ⟨60930299193549486283253933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40620199462366324188835955 60930299193549486283253933)
        ·
          refine ⟨22848862197581057356220225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60930299193549486283253933 22848862197581057356220225)
          ·
            refine ⟨17136646648185793017165169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22848862197581057356220225 17136646648185793017165169)
            ·
              refine ⟨12852484986139344762873877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17136646648185793017165169 12852484986139344762873877)
              ·
                refine ⟨602460233725281785759713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12852484986139344762873877 602460233725281785759713)
                ·
                  refine ⟨451845175293961339319785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 602460233725281785759713 451845175293961339319785)
                  ·
                    rfl

theorem cell20_989961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 2].length) (baseStart_989961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989961 prefixEnd_989961 := by exact prefixLift 989961
  have htrace : WordTrace (prefixWord ++ tailWord_989961) baseStart_989961 baseEnd_989961 := by
    simpa [prefixWord, tailWord_989961, baseEnd_989961] using wordTrace_append hprefix tailTrace_989961
  have hstable : (prefixWord ++ tailWord_989961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989961).length < 2 ^ (prefixWord ++ tailWord_989961).sum := by decide
  have hdescent : baseEnd_989961 < baseStart_989961 := by decide
  rcases family_descends (prefixWord ++ tailWord_989961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_989989 : List Nat := [1, 3, 1, 2, 3, 1, 1, 8]
def baseStart_989989 : Nat := 118140960795 + 989989 * 2 ^ 59
def prefixEnd_989989 : Nat := 4983230072969 + 3 ^ 40 * 989989 * 2
def baseEnd_989989 : Nat := 150619318418972562128779

theorem tailTrace_989989 : CollatzResearch.WordTrace tailWord_989989 prefixEnd_989989 150619318418972562128779 := by
  unfold tailWord_989989
  simp only [CollatzResearch.WordTrace]
  refine ⟨36107865210446404505429021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24071910140297603003619347 36107865210446404505429021)
  ·
    refine ⟨13540449453917401689535883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36107865210446404505429021 13540449453917401689535883)
    ·
      refine ⟨20310674180876102534303825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13540449453917401689535883 20310674180876102534303825)
      ·
        refine ⟨15233005635657076900727869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20310674180876102534303825 15233005635657076900727869)
        ·
          refine ⟨5712377113371403837772951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15233005635657076900727869 5712377113371403837772951)
          ·
            refine ⟨8568565670057105756659427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5712377113371403837772951 8568565670057105756659427)
            ·
              refine ⟨12852848505085658634989141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8568565670057105756659427 12852848505085658634989141)
              ·
                refine ⟨150619318418972562128779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12852848505085658634989141 150619318418972562128779)
                ·
                  rfl

theorem cell20_989989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 8].length) (baseStart_989989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_989989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_989989 prefixEnd_989989 := by exact prefixLift 989989
  have htrace : WordTrace (prefixWord ++ tailWord_989989) baseStart_989989 baseEnd_989989 := by
    simpa [prefixWord, tailWord_989989, baseEnd_989989] using wordTrace_append hprefix tailTrace_989989
  have hstable : (prefixWord ++ tailWord_989989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_989989).length < 2 ^ (prefixWord ++ tailWord_989989).sum := by decide
  have hdescent : baseEnd_989989 < baseStart_989989 := by decide
  rcases family_descends (prefixWord ++ tailWord_989989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990006 : List Nat := [5, 1, 2, 2, 10]
def baseStart_990006 : Nat := 118140960795 + 990006 * 2 ^ 59
def prefixEnd_990006 : Nat := 4983230072969 + 3 ^ 40 * 990006 * 2
def baseEnd_990006 : Nat := 5578589068149891145921

theorem tailTrace_990006 : CollatzResearch.WordTrace tailWord_990006 prefixEnd_990006 5578589068149891145921 := by
  unfold tailWord_990006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2256780328211551025549867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24072323500923210939198581 2256780328211551025549867)
  ·
    refine ⟨3385170492317326538324801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2256780328211551025549867 3385170492317326538324801)
    ·
      refine ⟨2538877869237994903743601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3385170492317326538324801 2538877869237994903743601)
      ·
        refine ⟨1904158401928496177807701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2538877869237994903743601 1904158401928496177807701)
        ·
          refine ⟨5578589068149891145921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1904158401928496177807701 5578589068149891145921)
          ·
            rfl

theorem cell20_990006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 10].length) (baseStart_990006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990006 prefixEnd_990006 := by exact prefixLift 990006
  have htrace : WordTrace (prefixWord ++ tailWord_990006) baseStart_990006 baseEnd_990006 := by
    simpa [prefixWord, tailWord_990006, baseEnd_990006] using wordTrace_append hprefix tailTrace_990006
  have hstable : (prefixWord ++ tailWord_990006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990006).length < 2 ^ (prefixWord ++ tailWord_990006).sum := by decide
  have hdescent : baseEnd_990006 < baseStart_990006 := by decide
  rcases family_descends (prefixWord ++ tailWord_990006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990065 : List Nat := [1, 2, 2, 2, 1, 5, 7]
def baseStart_990065 : Nat := 118140960795 + 990065 * 2 ^ 59
def prefixEnd_990065 : Nat := 4983230072969 + 3 ^ 40 * 990065 * 2
def baseEnd_990065 : Nat := 50210293747533244428077

theorem tailTrace_990065 : CollatzResearch.WordTrace tailWord_990065 prefixEnd_990065 50210293747533244428077 := by
  unfold tailWord_990065
  simp only [CollatzResearch.WordTrace]
  refine ⟨36110637158171069485195649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24073758105447379656797099 36110637158171069485195649)
  ·
    refine ⟨27082977868628302113896737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36110637158171069485195649 27082977868628302113896737)
    ·
      refine ⟨20312233401471226585422553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27082977868628302113896737 20312233401471226585422553)
      ·
        refine ⟨15234175051103419939066915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20312233401471226585422553 15234175051103419939066915)
        ·
          refine ⟨22851262576655129908600373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15234175051103419939066915 22851262576655129908600373)
          ·
            refine ⟨2142305866561418428931285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22851262576655129908600373 2142305866561418428931285)
            ·
              refine ⟨50210293747533244428077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2142305866561418428931285 50210293747533244428077)
              ·
                rfl

theorem cell20_990065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 7].length) (baseStart_990065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990065 prefixEnd_990065 := by exact prefixLift 990065
  have htrace : WordTrace (prefixWord ++ tailWord_990065) baseStart_990065 baseEnd_990065 := by
    simpa [prefixWord, tailWord_990065, baseEnd_990065] using wordTrace_append hprefix tailTrace_990065
  have hstable : (prefixWord ++ tailWord_990065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990065).length < 2 ^ (prefixWord ++ tailWord_990065).sum := by decide
  have hdescent : baseEnd_990065 < baseStart_990065 := by decide
  rcases family_descends (prefixWord ++ tailWord_990065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990075 : List Nat := [1, 1, 1, 1, 1, 5, 4, 4, 2]
def baseStart_990075 : Nat := 118140960795 + 990075 * 2 ^ 59
def prefixEnd_990075 : Nat := 4983230072969 + 3 ^ 40 * 990075 * 2
def baseEnd_990075 : Nat := 451897208000283609519319

theorem tailTrace_990075 : CollatzResearch.WordTrace tailWord_990075 prefixEnd_990075 451897208000283609519319 := by
  unfold tailWord_990075
  simp only [CollatzResearch.WordTrace]
  refine ⟨36111001888134841193059679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24074001258756560795373119 36111001888134841193059679)
  ·
    refine ⟨54166502832202261789589519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36111001888134841193059679 54166502832202261789589519)
    ·
      refine ⟨81249754248303392684384279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54166502832202261789589519 81249754248303392684384279)
      ·
        refine ⟨121874631372455089026576419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81249754248303392684384279 121874631372455089026576419)
        ·
          refine ⟨182811947058682633539864629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121874631372455089026576419 182811947058682633539864629)
          ·
            refine ⟨17138620036751496894362309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 182811947058682633539864629 17138620036751496894362309)
            ·
              refine ⟨3213491256890905667692933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17138620036751496894362309 3213491256890905667692933)
              ·
                refine ⟨602529610667044812692425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3213491256890905667692933 602529610667044812692425)
                ·
                  refine ⟨451897208000283609519319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 602529610667044812692425 451897208000283609519319)
                  ·
                    rfl

theorem cell20_990075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 2].length) (baseStart_990075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990075 prefixEnd_990075 := by exact prefixLift 990075
  have htrace : WordTrace (prefixWord ++ tailWord_990075) baseStart_990075 baseEnd_990075 := by
    simpa [prefixWord, tailWord_990075, baseEnd_990075] using wordTrace_append hprefix tailTrace_990075
  have hstable : (prefixWord ++ tailWord_990075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990075).length < 2 ^ (prefixWord ++ tailWord_990075).sum := by decide
  have hdescent : baseEnd_990075 < baseStart_990075 := by decide
  rcases family_descends (prefixWord ++ tailWord_990075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990103 : List Nat := [1, 1, 3, 3, 1, 2, 3, 6]
def baseStart_990103 : Nat := 118140960795 + 990103 * 2 ^ 59
def prefixEnd_990103 : Nat := 4983230072969 + 3 ^ 40 * 990103 * 2
def baseEnd_990103 : Nat := 150636662654413318861957

theorem tailTrace_990103 : CollatzResearch.WordTrace tailWord_990103 prefixEnd_990103 150636662654413318861957 := by
  unfold tailWord_990103
  simp only [CollatzResearch.WordTrace]
  refine ⟨36112023132033401975078963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24074682088022267983385975 36112023132033401975078963)
  ·
    refine ⟨54168034698050102962618445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36112023132033401975078963 54168034698050102962618445)
    ·
      refine ⟨20313013011768788610981917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54168034698050102962618445 20313013011768788610981917)
      ·
        refine ⟨7617379879413295729118219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20313013011768788610981917 7617379879413295729118219)
        ·
          refine ⟨11426069819119943593677329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7617379879413295729118219 11426069819119943593677329)
          ·
            refine ⟨8569552364339957695257997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11426069819119943593677329 8569552364339957695257997)
            ·
              refine ⟨3213582136627484135721749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8569552364339957695257997 3213582136627484135721749)
              ·
                refine ⟨150636662654413318861957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3213582136627484135721749 150636662654413318861957)
                ·
                  rfl

theorem cell20_990103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 6].length) (baseStart_990103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990103 prefixEnd_990103 := by exact prefixLift 990103
  have htrace : WordTrace (prefixWord ++ tailWord_990103) baseStart_990103 baseEnd_990103 := by
    simpa [prefixWord, tailWord_990103, baseEnd_990103] using wordTrace_append hprefix tailTrace_990103
  have hstable : (prefixWord ++ tailWord_990103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990103).length < 2 ^ (prefixWord ++ tailWord_990103).sum := by decide
  have hdescent : baseEnd_990103 < baseStart_990103 := by decide
  rcases family_descends (prefixWord ++ tailWord_990103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990144 : List Nat := [2, 1, 1, 2, 3, 3, 4, 1, 3]
def baseStart_990144 : Nat := 118140960795 + 990144 * 2 ^ 59
def prefixEnd_990144 : Nat := 4983230072969 + 3 ^ 40 * 990144 * 2
def baseEnd_990144 : Nat := 451928701480426036219037

theorem tailTrace_990144 : CollatzResearch.WordTrace tailWord_990144 prefixEnd_990144 451928701480426036219037 := by
  unfold tailWord_990144
  simp only [CollatzResearch.WordTrace]
  refine ⟨18056759262442432988660743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24075679016589910651547657 18056759262442432988660743)
  ·
    refine ⟨27085138893663649482991115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18056759262442432988660743 27085138893663649482991115)
    ·
      refine ⟨40627708340495474224486673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27085138893663649482991115 40627708340495474224486673)
      ·
        refine ⟨30470781255371605668365005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40627708340495474224486673 30470781255371605668365005)
        ·
          refine ⟨11426542970764352125636877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30470781255371605668365005 11426542970764352125636877)
          ·
            refine ⟨4284953614036632047113829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11426542970764352125636877 4284953614036632047113829)
            ·
              refine ⟨803428802631868508833843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4284953614036632047113829 803428802631868508833843)
              ·
                refine ⟨1205143203947802763250765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803428802631868508833843 1205143203947802763250765)
                ·
                  refine ⟨451928701480426036219037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1205143203947802763250765 451928701480426036219037)
                  ·
                    rfl

theorem cell20_990144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 3].length) (baseStart_990144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990144 prefixEnd_990144 := by exact prefixLift 990144
  have htrace : WordTrace (prefixWord ++ tailWord_990144) baseStart_990144 baseEnd_990144 := by
    simpa [prefixWord, tailWord_990144, baseEnd_990144] using wordTrace_append hprefix tailTrace_990144
  have hstable : (prefixWord ++ tailWord_990144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990144).length < 2 ^ (prefixWord ++ tailWord_990144).sum := by decide
  have hdescent : baseEnd_990144 < baseStart_990144 := by decide
  rcases family_descends (prefixWord ++ tailWord_990144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990181 : List Nat := [1, 3, 1, 6, 2, 1, 2, 2, 2]
def baseStart_990181 : Nat := 118140960795 + 990181 * 2 ^ 59
def prefixEnd_990181 : Nat := 4983230072969 + 3 ^ 40 * 990181 * 2
def baseEnd_990181 : Nat := 451945589288618351985553

theorem tailTrace_990181 : CollatzResearch.WordTrace tailWord_990181 prefixEnd_990181 451945589288618351985553 := by
  unfold tailWord_990181
  simp only [CollatzResearch.WordTrace]
  refine ⟨36114868025750821296418397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24076578683833880864278931 36114868025750821296418397)
  ·
    refine ⟨13543075509656557986156899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36114868025750821296418397 13543075509656557986156899)
    ·
      refine ⟨20314613264484836979235349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13543075509656557986156899 20314613264484836979235349)
      ·
        refine ⟨952247496772726733401657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20314613264484836979235349 952247496772726733401657)
        ·
          refine ⟨714185622579545050051243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 952247496772726733401657 714185622579545050051243)
          ·
            refine ⟨1071278433869317575076865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714185622579545050051243 1071278433869317575076865)
            ·
              refine ⟨803458825401988181307649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1071278433869317575076865 803458825401988181307649)
              ·
                refine ⟨602594119051491135980737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 803458825401988181307649 602594119051491135980737)
                ·
                  refine ⟨451945589288618351985553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 602594119051491135980737 451945589288618351985553)
                  ·
                    rfl

theorem cell20_990181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_990181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990181 prefixEnd_990181 := by exact prefixLift 990181
  have htrace : WordTrace (prefixWord ++ tailWord_990181) baseStart_990181 baseEnd_990181 := by
    simpa [prefixWord, tailWord_990181, baseEnd_990181] using wordTrace_append hprefix tailTrace_990181
  have hstable : (prefixWord ++ tailWord_990181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990181).length < 2 ^ (prefixWord ++ tailWord_990181).sum := by decide
  have hdescent : baseEnd_990181 < baseStart_990181 := by decide
  rcases family_descends (prefixWord ++ tailWord_990181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990206 : List Nat := [4, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_990206 : Nat := 118140960795 + 990206 * 2 ^ 59
def prefixEnd_990206 : Nat := 4983230072969 + 3 ^ 40 * 990206 * 2
def baseEnd_990206 : Nat := 451956999969829376152117

theorem tailTrace_990206 : CollatzResearch.WordTrace tailWord_990206 prefixEnd_990206 451956999969829376152117 := by
  unfold tailWord_990206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4514472481332531320759809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24077186567106833710718981 4514472481332531320759809)
  ·
    refine ⟨3385854360999398490569857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4514472481332531320759809 3385854360999398490569857)
    ·
      refine ⟨2539390770749548867927393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3385854360999398490569857 2539390770749548867927393)
      ·
        refine ⟨1904543078062161650945545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2539390770749548867927393 1904543078062161650945545)
        ·
          refine ⟨1428407308546621238209159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1904543078062161650945545 1428407308546621238209159)
          ·
            refine ⟨2142610962819931857313739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1428407308546621238209159 2142610962819931857313739)
            ·
              refine ⟨3213916444229897785970609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2142610962819931857313739 3213916444229897785970609)
              ·
                refine ⟨2410437333172423339477957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3213916444229897785970609 2410437333172423339477957)
                ·
                  refine ⟨451956999969829376152117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2410437333172423339477957 451956999969829376152117)
                  ·
                    rfl

theorem cell20_990206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_990206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990206 prefixEnd_990206 := by exact prefixLift 990206
  have htrace : WordTrace (prefixWord ++ tailWord_990206) baseStart_990206 baseEnd_990206 := by
    simpa [prefixWord, tailWord_990206, baseEnd_990206] using wordTrace_append hprefix tailTrace_990206
  have hstable : (prefixWord ++ tailWord_990206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990206).length < 2 ^ (prefixWord ++ tailWord_990206).sum := by decide
  have hdescent : baseEnd_990206 < baseStart_990206 := by decide
  rcases family_descends (prefixWord ++ tailWord_990206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990237 : List Nat := [1, 4, 2, 2, 3, 2, 1, 2, 3]
def baseStart_990237 : Nat := 118140960795 + 990237 * 2 ^ 59
def prefixEnd_990237 : Nat := 4983230072969 + 3 ^ 40 * 990237 * 2
def baseEnd_990237 : Nat := 451971149214531046118657

theorem tailTrace_990237 : CollatzResearch.WordTrace tailWord_990237 prefixEnd_990237 451971149214531046118657 := by
  unfold tailWord_990237
  simp only [CollatzResearch.WordTrace]
  refine ⟨36116910513547942860456965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24077940342365295240304643 36116910513547942860456965)
  ·
    refine ⟨6771920721290239286335681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36116910513547942860456965 6771920721290239286335681)
    ·
      refine ⟨5078940540967679464751761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6771920721290239286335681 5078940540967679464751761)
      ·
        refine ⟨3809205405725759598563821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5078940540967679464751761 3809205405725759598563821)
        ·
          refine ⟨1428452027147159849461433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3809205405725759598563821 1428452027147159849461433)
          ·
            refine ⟨1071339020360369887096075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1428452027147159849461433 1071339020360369887096075)
            ·
              refine ⟨1607008530540554830644113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071339020360369887096075 1607008530540554830644113)
              ·
                refine ⟨1205256397905416122983085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1607008530540554830644113 1205256397905416122983085)
                ·
                  refine ⟨451971149214531046118657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1205256397905416122983085 451971149214531046118657)
                  ·
                    rfl

theorem cell20_990237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_990237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990237 prefixEnd_990237 := by exact prefixLift 990237
  have htrace : WordTrace (prefixWord ++ tailWord_990237) baseStart_990237 baseEnd_990237 := by
    simpa [prefixWord, tailWord_990237, baseEnd_990237] using wordTrace_append hprefix tailTrace_990237
  have hstable : (prefixWord ++ tailWord_990237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990237).length < 2 ^ (prefixWord ++ tailWord_990237).sum := by decide
  have hdescent : baseEnd_990237 < baseStart_990237 := by decide
  rcases family_descends (prefixWord ++ tailWord_990237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990241 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 5]
def baseStart_990241 : Nat := 118140960795 + 990241 * 2 ^ 59
def prefixEnd_990241 : Nat := 4983230072969 + 3 ^ 40 * 990241 * 2
def baseEnd_990241 : Nat := 451972974923524809985307

theorem tailTrace_990241 : CollatzResearch.WordTrace tailWord_990241 prefixEnd_990241 451972974923524809985307 := by
  unfold tailWord_990241
  simp only [CollatzResearch.WordTrace]
  refine ⟨36117056405533451543602577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24078037603688967695735051 36117056405533451543602577)
  ·
    refine ⟨27087792304150088657701933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36117056405533451543602577 27087792304150088657701933)
    ·
      refine ⟨10157922114056283246638225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27087792304150088657701933 10157922114056283246638225)
      ·
        refine ⟨7618441585542212434978669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10157922114056283246638225 7618441585542212434978669)
        ·
          refine ⟨2856915594578329663117001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7618441585542212434978669 2856915594578329663117001)
          ·
            refine ⟨2142686695933747247337751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2856915594578329663117001 2142686695933747247337751)
            ·
              refine ⟨3214030043900620871006627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2142686695933747247337751 3214030043900620871006627)
              ·
                refine ⟨4821045065850931306509941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3214030043900620871006627 4821045065850931306509941)
                ·
                  refine ⟨451972974923524809985307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4821045065850931306509941 451972974923524809985307)
                  ·
                    rfl

theorem cell20_990241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_990241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990241 prefixEnd_990241 := by exact prefixLift 990241
  have htrace : WordTrace (prefixWord ++ tailWord_990241) baseStart_990241 baseEnd_990241 := by
    simpa [prefixWord, tailWord_990241, baseEnd_990241] using wordTrace_append hprefix tailTrace_990241
  have hstable : (prefixWord ++ tailWord_990241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990241).length < 2 ^ (prefixWord ++ tailWord_990241).sum := by decide
  have hdescent : baseEnd_990241 < baseStart_990241 := by decide
  rcases family_descends (prefixWord ++ tailWord_990241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990244 : List Nat := [2, 3, 1, 4, 1, 1, 2, 4, 2]
def baseStart_990244 : Nat := 118140960795 + 990244 * 2 ^ 59
def prefixEnd_990244 : Nat := 4983230072969 + 3 ^ 40 * 990244 * 2
def baseEnd_990244 : Nat := 451974344205270132885295

theorem tailTrace_990244 : CollatzResearch.WordTrace tailWord_990244 prefixEnd_990244 451974344205270132885295 := by
  unfold tailWord_990244
  simp only [CollatzResearch.WordTrace]
  refine ⟨18058582912261291527980893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24078110549681722037307857 18058582912261291527980893)
  ·
    refine ⟨6771968592097984322992835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18058582912261291527980893 6771968592097984322992835)
    ·
      refine ⟨10157952888146976484489253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6771968592097984322992835 10157952888146976484489253)
      ·
        refine ⟨1904616166527558090841735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10157952888146976484489253 1904616166527558090841735)
        ·
          refine ⟨2856924249791337136262603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1904616166527558090841735 2856924249791337136262603)
          ·
            refine ⟨4285386374687005704393905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2856924249791337136262603 4285386374687005704393905)
            ·
              refine ⟨3214039781015254278295429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4285386374687005704393905 3214039781015254278295429)
              ·
                refine ⟨602632458940360177180393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3214039781015254278295429 602632458940360177180393)
                ·
                  refine ⟨451974344205270132885295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 602632458940360177180393 451974344205270132885295)
                  ·
                    rfl

theorem cell20_990244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_990244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990244 prefixEnd_990244 := by exact prefixLift 990244
  have htrace : WordTrace (prefixWord ++ tailWord_990244) baseStart_990244 baseEnd_990244 := by
    simpa [prefixWord, tailWord_990244, baseEnd_990244] using wordTrace_append hprefix tailTrace_990244
  have hstable : (prefixWord ++ tailWord_990244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990244).length < 2 ^ (prefixWord ++ tailWord_990244).sum := by decide
  have hdescent : baseEnd_990244 < baseStart_990244 := by decide
  rcases family_descends (prefixWord ++ tailWord_990244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990258 : List Nat := [3, 2, 1, 1, 2, 2, 5, 1, 3]
def baseStart_990258 : Nat := 118140960795 + 990258 * 2 ^ 59
def prefixEnd_990258 : Nat := 4983230072969 + 3 ^ 40 * 990258 * 2
def baseEnd_990258 : Nat := 451980734186748306418571

theorem tailTrace_990258 : CollatzResearch.WordTrace tailWord_990258 prefixEnd_990258 451980734186748306418571 := by
  unfold tailWord_990258
  simp only [CollatzResearch.WordTrace]
  refine ⟨9029419111617965861742857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24078450964314575631314285 9029419111617965861742857)
  ·
    refine ⟨6772064333713474396307143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9029419111617965861742857 6772064333713474396307143)
    ·
      refine ⟨10158096500570211594460715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6772064333713474396307143 10158096500570211594460715)
      ·
        refine ⟨15237144750855317391691073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10158096500570211594460715 15237144750855317391691073)
        ·
          refine ⟨11427858563141488043768305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15237144750855317391691073 11427858563141488043768305)
          ·
            refine ⟨8570893922356116032826229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11427858563141488043768305 8570893922356116032826229)
            ·
              refine ⟨803521305220885878077459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8570893922356116032826229 803521305220885878077459)
              ·
                refine ⟨1205281957831328817116189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803521305220885878077459 1205281957831328817116189)
                ·
                  refine ⟨451980734186748306418571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1205281957831328817116189 451980734186748306418571)
                  ·
                    rfl

theorem cell20_990258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_990258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990258 prefixEnd_990258 := by exact prefixLift 990258
  have htrace : WordTrace (prefixWord ++ tailWord_990258) baseStart_990258 baseEnd_990258 := by
    simpa [prefixWord, tailWord_990258, baseEnd_990258] using wordTrace_append hprefix tailTrace_990258
  have hstable : (prefixWord ++ tailWord_990258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990258).length < 2 ^ (prefixWord ++ tailWord_990258).sum := by decide
  have hdescent : baseEnd_990258 < baseStart_990258 := by decide
  rcases family_descends (prefixWord ++ tailWord_990258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990278 : List Nat := [6, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_990278 : Nat := 118140960795 + 990278 * 2 ^ 59
def prefixEnd_990278 : Nat := 4983230072969 + 3 ^ 40 * 990278 * 2
def baseEnd_990278 : Nat := 451989862731717125751823

theorem tailTrace_990278 : CollatzResearch.WordTrace tailWord_990278 prefixEnd_990278 451989862731717125751823 := by
  unfold tailWord_990278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1128700184574981464459359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24078937270932937908466325 1128700184574981464459359)
  ·
    refine ⟨1693050276862472196689039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1128700184574981464459359 1693050276862472196689039)
    ·
      refine ⟨2539575415293708295033559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1693050276862472196689039 2539575415293708295033559)
      ·
        refine ⟨3809363122940562442550339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2539575415293708295033559 3809363122940562442550339)
        ·
          refine ⟨5714044684410843663825509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3809363122940562442550339 5714044684410843663825509)
          ·
            refine ⟨1071383378327033186967283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5714044684410843663825509 1071383378327033186967283)
            ·
              refine ⟨1607075067490549780450925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071383378327033186967283 1607075067490549780450925)
              ·
                refine ⟨602653150308956167669097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1607075067490549780450925 602653150308956167669097)
                ·
                  refine ⟨451989862731717125751823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 602653150308956167669097 451989862731717125751823)
                  ·
                    rfl

theorem cell20_990278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_990278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990278 prefixEnd_990278 := by exact prefixLift 990278
  have htrace : WordTrace (prefixWord ++ tailWord_990278) baseStart_990278 baseEnd_990278 := by
    simpa [prefixWord, tailWord_990278, baseEnd_990278] using wordTrace_append hprefix tailTrace_990278
  have hstable : (prefixWord ++ tailWord_990278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990278).length < 2 ^ (prefixWord ++ tailWord_990278).sum := by decide
  have hdescent : baseEnd_990278 < baseStart_990278 := by decide
  rcases family_descends (prefixWord ++ tailWord_990278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990383 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 6]
def baseStart_990383 : Nat := 118140960795 + 990383 * 2 ^ 59
def prefixEnd_990383 : Nat := 4983230072969 + 3 ^ 40 * 990383 * 2
def baseEnd_990383 : Nat := 452037787592803427251393

theorem tailTrace_990383 : CollatzResearch.WordTrace tailWord_990383 prefixEnd_990383 452037787592803427251393 := by
  unfold tailWord_990383
  simp only [CollatzResearch.WordTrace]
  refine ⟨36122235571019009795271803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24081490380679339863514535 36122235571019009795271803)
  ·
    refine ⟨54183353356528514692907705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36122235571019009795271803 54183353356528514692907705)
    ·
      refine ⟨40637515017396386019680779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54183353356528514692907705 40637515017396386019680779)
      ·
        refine ⟨60956272526094579029521169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40637515017396386019680779 60956272526094579029521169)
        ·
          refine ⟨45717204394570934272140877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60956272526094579029521169 45717204394570934272140877)
          ·
            refine ⟨17143951647964100352052829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45717204394570934272140877 17143951647964100352052829)
            ·
              refine ⟨6428981867986537632019811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17143951647964100352052829 6428981867986537632019811)
              ·
                refine ⟨9643472801979806448029717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6428981867986537632019811 9643472801979806448029717)
                ·
                  refine ⟨452037787592803427251393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9643472801979806448029717 452037787592803427251393)
                  ·
                    rfl

theorem cell20_990383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_990383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990383 prefixEnd_990383 := by exact prefixLift 990383
  have htrace : WordTrace (prefixWord ++ tailWord_990383) baseStart_990383 baseEnd_990383 := by
    simpa [prefixWord, tailWord_990383, baseEnd_990383] using wordTrace_append hprefix tailTrace_990383
  have hstable : (prefixWord ++ tailWord_990383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990383).length < 2 ^ (prefixWord ++ tailWord_990383).sum := by decide
  have hdescent : baseEnd_990383 < baseStart_990383 := by decide
  rcases family_descends (prefixWord ++ tailWord_990383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990386 : List Nat := [3, 2, 1, 1, 1, 5, 3, 4]
def baseStart_990386 : Nat := 118140960795 + 990386 * 2 ^ 59
def prefixEnd_990386 : Nat := 4983230072969 + 3 ^ 40 * 990386 * 2
def baseEnd_990386 : Nat := 150679718958182916717127

theorem tailTrace_990386 : CollatzResearch.WordTrace tailWord_990386 prefixEnd_990386 150679718958182916717127 := by
  unfold tailWord_990386
  simp only [CollatzResearch.WordTrace]
  refine ⟨9030586247502035326907753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24081563326672094205087341 9030586247502035326907753)
  ·
    refine ⟨6772939685626526495180815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9030586247502035326907753 6772939685626526495180815)
    ·
      refine ⟨10159409528439789742771223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6772939685626526495180815 10159409528439789742771223)
      ·
        refine ⟨15239114292659684614156835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10159409528439789742771223 15239114292659684614156835)
        ·
          refine ⟨22858671438989526921235253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15239114292659684614156835 22858671438989526921235253)
          ·
            refine ⟨2143000447405268148865805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22858671438989526921235253 2143000447405268148865805)
            ·
              refine ⟨803625167776975555824677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2143000447405268148865805 803625167776975555824677)
              ·
                refine ⟨150679718958182916717127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 803625167776975555824677 150679718958182916717127)
                ·
                  rfl

theorem cell20_990386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_990386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990386 prefixEnd_990386 := by exact prefixLift 990386
  have htrace : WordTrace (prefixWord ++ tailWord_990386) baseStart_990386 baseEnd_990386 := by
    simpa [prefixWord, tailWord_990386, baseEnd_990386] using wordTrace_append hprefix tailTrace_990386
  have hstable : (prefixWord ++ tailWord_990386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990386).length < 2 ^ (prefixWord ++ tailWord_990386).sum := by decide
  have hdescent : baseEnd_990386 < baseStart_990386 := by decide
  rcases family_descends (prefixWord ++ tailWord_990386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990396 : List Nat := [2, 2, 2, 3, 2, 2, 2, 3, 2]
def baseStart_990396 : Nat := 118140960795 + 990396 * 2 ^ 59
def prefixEnd_990396 : Nat := 4983230072969 + 3 ^ 40 * 990396 * 2
def baseEnd_990396 : Nat := 452043721147033159818007

theorem tailTrace_990396 : CollatzResearch.WordTrace tailWord_990396 prefixEnd_990396 452043721147033159818007 := by
  unfold tailWord_990396
  simp only [CollatzResearch.WordTrace]
  refine ⟨18061354859985956507747521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24081806479981275343663361 18061354859985956507747521)
  ·
    refine ⟨13546016144989467380810641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18061354859985956507747521 13546016144989467380810641)
    ·
      refine ⟨10159512108742100535607981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13546016144989467380810641 10159512108742100535607981)
      ·
        refine ⟨3809817040778287700852993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10159512108742100535607981 3809817040778287700852993)
        ·
          refine ⟨2857362780583715775639745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3809817040778287700852993 2857362780583715775639745)
          ·
            refine ⟨2143022085437786831729809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2857362780583715775639745 2143022085437786831729809)
            ·
              refine ⟨1607266564078340123797357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2143022085437786831729809 1607266564078340123797357)
              ·
                refine ⟨602724961529377546424009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1607266564078340123797357 602724961529377546424009)
                ·
                  refine ⟨452043721147033159818007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 602724961529377546424009 452043721147033159818007)
                  ·
                    rfl

theorem cell20_990396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_990396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990396 prefixEnd_990396 := by exact prefixLift 990396
  have htrace : WordTrace (prefixWord ++ tailWord_990396) baseStart_990396 baseEnd_990396 := by
    simpa [prefixWord, tailWord_990396, baseEnd_990396] using wordTrace_append hprefix tailTrace_990396
  have hstable : (prefixWord ++ tailWord_990396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990396).length < 2 ^ (prefixWord ++ tailWord_990396).sum := by decide
  have hdescent : baseEnd_990396 < baseStart_990396 := by decide
  rcases family_descends (prefixWord ++ tailWord_990396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990406 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_990406 : Nat := 118140960795 + 990406 * 2 ^ 59
def prefixEnd_990406 : Nat := 4983230072969 + 3 ^ 40 * 990406 * 2
def baseEnd_990406 : Nat := 452048285419517569484633

theorem tailTrace_990406 : CollatzResearch.WordTrace tailWord_990406 prefixEnd_990406 452048285419517569484633 := by
  unfold tailWord_990406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1128846076560490147604971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24082049633290456482239381 1128846076560490147604971)
  ·
    refine ⟨1693269114840735221407457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1128846076560490147604971 1693269114840735221407457)
    ·
      refine ⟨1269951836130551416055593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1693269114840735221407457 1269951836130551416055593)
      ·
        refine ⟨952463877097913562041695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1269951836130551416055593 952463877097913562041695)
        ·
          refine ⟨1428695815646870343062543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952463877097913562041695 1428695815646870343062543)
          ·
            refine ⟨2143043723470305514593815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1428695815646870343062543 2143043723470305514593815)
            ·
              refine ⟨3214565585205458271890723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2143043723470305514593815 3214565585205458271890723)
              ·
                refine ⟨4821848377808187407836085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3214565585205458271890723 4821848377808187407836085)
                ·
                  refine ⟨452048285419517569484633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4821848377808187407836085 452048285419517569484633)
                  ·
                    rfl

theorem cell20_990406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_990406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990406 prefixEnd_990406 := by exact prefixLift 990406
  have htrace : WordTrace (prefixWord ++ tailWord_990406) baseStart_990406 baseEnd_990406 := by
    simpa [prefixWord, tailWord_990406, baseEnd_990406] using wordTrace_append hprefix tailTrace_990406
  have hstable : (prefixWord ++ tailWord_990406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990406).length < 2 ^ (prefixWord ++ tailWord_990406).sum := by decide
  have hdescent : baseEnd_990406 < baseStart_990406 := by decide
  rcases family_descends (prefixWord ++ tailWord_990406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990410 : List Nat := [3, 1, 2, 1, 3, 4, 1, 2, 3]
def baseStart_990410 : Nat := 118140960795 + 990410 * 2 ^ 59
def prefixEnd_990410 : Nat := 4983230072969 + 3 ^ 40 * 990410 * 2
def baseEnd_990410 : Nat := 452050111128511333351283

theorem tailTrace_990410 : CollatzResearch.WordTrace tailWord_990410 prefixEnd_990410 452050111128511333351283 := by
  unfold tailWord_990410
  simp only [CollatzResearch.WordTrace]
  refine ⟨9030805085480298351626171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24082146894614128937669789 9030805085480298351626171)
  ·
    refine ⟨13546207628220447527439257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9030805085480298351626171 13546207628220447527439257)
    ·
      refine ⟨10159655721165335645579443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13546207628220447527439257 10159655721165335645579443)
      ·
        refine ⟨15239483581748003468369165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10159655721165335645579443 15239483581748003468369165)
        ·
          refine ⟨5714806343155501300638437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15239483581748003468369165 5714806343155501300638437)
          ·
            refine ⟨1071526189341656493869707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5714806343155501300638437 1071526189341656493869707)
            ·
              refine ⟨1607289284012484740804561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071526189341656493869707 1607289284012484740804561)
              ·
                refine ⟨1205466963009363555603421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1607289284012484740804561 1205466963009363555603421)
                ·
                  refine ⟨452050111128511333351283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1205466963009363555603421 452050111128511333351283)
                  ·
                    rfl

theorem cell20_990410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_990410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990410 prefixEnd_990410 := by exact prefixLift 990410
  have htrace : WordTrace (prefixWord ++ tailWord_990410) baseStart_990410 baseEnd_990410 := by
    simpa [prefixWord, tailWord_990410, baseEnd_990410] using wordTrace_append hprefix tailTrace_990410
  have hstable : (prefixWord ++ tailWord_990410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990410).length < 2 ^ (prefixWord ++ tailWord_990410).sum := by decide
  have hdescent : baseEnd_990410 < baseStart_990410 := by decide
  rcases family_descends (prefixWord ++ tailWord_990410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990413 : List Nat := [1, 6, 2, 2, 1, 1, 2, 1, 4]
def baseStart_990413 : Nat := 118140960795 + 990413 * 2 ^ 59
def prefixEnd_990413 : Nat := 4983230072969 + 3 ^ 40 * 990413 * 2
def baseEnd_990413 : Nat := 452051480410256656251271

theorem tailTrace_990413 : CollatzResearch.WordTrace tailWord_990413 prefixEnd_990413 452051480410256656251271 := by
  unfold tailWord_990413
  simp only [CollatzResearch.WordTrace]
  refine ⟨36123329760910324918863893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24082219840606883279242595 36123329760910324918863893)
  ·
    refine ⟨1693281082542671480571745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36123329760910324918863893 1693281082542671480571745)
    ·
      refine ⟨1269960811907003610428809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1693281082542671480571745 1269960811907003610428809)
      ·
        refine ⟨952470608930252707821607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1269960811907003610428809 952470608930252707821607)
        ·
          refine ⟨1428705913395379061732411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952470608930252707821607 1428705913395379061732411)
          ·
            refine ⟨2143058870093068592598617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1428705913395379061732411 2143058870093068592598617)
            ·
              refine ⟨1607294152569801444448963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2143058870093068592598617 1607294152569801444448963)
              ·
                refine ⟨2410941228854702166673445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1607294152569801444448963 2410941228854702166673445)
                ·
                  refine ⟨452051480410256656251271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2410941228854702166673445 452051480410256656251271)
                  ·
                    rfl

theorem cell20_990413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_990413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990413 prefixEnd_990413 := by exact prefixLift 990413
  have htrace : WordTrace (prefixWord ++ tailWord_990413) baseStart_990413 baseEnd_990413 := by
    simpa [prefixWord, tailWord_990413, baseEnd_990413] using wordTrace_append hprefix tailTrace_990413
  have hstable : (prefixWord ++ tailWord_990413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990413).length < 2 ^ (prefixWord ++ tailWord_990413).sum := by decide
  have hdescent : baseEnd_990413 < baseStart_990413 := by decide
  rcases family_descends (prefixWord ++ tailWord_990413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990462 : List Nat := [4, 2, 2, 1, 1, 4, 6]
def baseStart_990462 : Nat := 118140960795 + 990462 * 2 ^ 59
def prefixEnd_990462 : Nat := 4983230072969 + 3 ^ 40 * 990462 * 2
def baseEnd_990462 : Nat := 50230427260603362624193

theorem tailTrace_990462 : CollatzResearch.WordTrace tailWord_990462 prefixEnd_990462 50230427260603362624193 := by
  unfold tailWord_990462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4515639617216600785924705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24083411291821870858265093 4515639617216600785924705)
  ·
    refine ⟨3386729712912450589443529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4515639617216600785924705 3386729712912450589443529)
    ·
      refine ⟨2540047284684337942082647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3386729712912450589443529 2540047284684337942082647)
      ·
        refine ⟨3810070927026506913123971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2540047284684337942082647 3810070927026506913123971)
        ·
          refine ⟨5715106390539760369685957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3810070927026506913123971 5715106390539760369685957)
          ·
            refine ⟨1071582448226205069316117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5715106390539760369685957 1071582448226205069316117)
            ·
              refine ⟨50230427260603362624193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1071582448226205069316117 50230427260603362624193)
              ·
                rfl

theorem cell20_990462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 6].length) (baseStart_990462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990462 prefixEnd_990462 := by exact prefixLift 990462
  have htrace : WordTrace (prefixWord ++ tailWord_990462) baseStart_990462 baseEnd_990462 := by
    simpa [prefixWord, tailWord_990462, baseEnd_990462] using wordTrace_append hprefix tailTrace_990462
  have hstable : (prefixWord ++ tailWord_990462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990462).length < 2 ^ (prefixWord ++ tailWord_990462).sum := by decide
  have hdescent : baseEnd_990462 < baseStart_990462 := by decide
  rcases family_descends (prefixWord ++ tailWord_990462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990472 : List Nat := [2, 1, 3, 2, 5, 1, 1, 1, 4]
def baseStart_990472 : Nat := 118140960795 + 990472 * 2 ^ 59
def prefixEnd_990472 : Nat := 4983230072969 + 3 ^ 40 * 990472 * 2
def baseEnd_990472 : Nat := 452078409617914673284363

theorem tailTrace_990472 : CollatzResearch.WordTrace tailWord_990472 prefixEnd_990472 452078409617914673284363 := by
  unfold tailWord_990472
  simp only [CollatzResearch.WordTrace]
  refine ⟨18062740833848288997630835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24083654445131051996841113 18062740833848288997630835)
  ·
    refine ⟨27094111250772433496446253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18062740833848288997630835 27094111250772433496446253)
    ·
      refine ⟨10160291719039662561167345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27094111250772433496446253 10160291719039662561167345)
      ·
        refine ⟨7620218789279746920875509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10160291719039662561167345 7620218789279746920875509)
        ·
          refine ⟨714395511494976273832079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7620218789279746920875509 714395511494976273832079)
          ·
            refine ⟨1071593267242464410748119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714395511494976273832079 1071593267242464410748119)
            ·
              refine ⟨1607389900863696616122179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071593267242464410748119 1607389900863696616122179)
              ·
                refine ⟨2411084851295544924183269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1607389900863696616122179 2411084851295544924183269)
                ·
                  refine ⟨452078409617914673284363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2411084851295544924183269 452078409617914673284363)
                  ·
                    rfl

theorem cell20_990472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 4].length) (baseStart_990472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990472 prefixEnd_990472 := by exact prefixLift 990472
  have htrace : WordTrace (prefixWord ++ tailWord_990472) baseStart_990472 baseEnd_990472 := by
    simpa [prefixWord, tailWord_990472, baseEnd_990472] using wordTrace_append hprefix tailTrace_990472
  have hstable : (prefixWord ++ tailWord_990472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990472).length < 2 ^ (prefixWord ++ tailWord_990472).sum := by decide
  have hdescent : baseEnd_990472 < baseStart_990472 := by decide
  rcases family_descends (prefixWord ++ tailWord_990472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990476 : List Nat := [2, 2, 1, 2, 2, 3, 3, 1, 4]
def baseStart_990476 : Nat := 118140960795 + 990476 * 2 ^ 59
def prefixEnd_990476 : Nat := 4983230072969 + 3 ^ 40 * 990476 * 2
def baseEnd_990476 : Nat := 452080235326908437151013

theorem tailTrace_990476 : CollatzResearch.WordTrace tailWord_990476 prefixEnd_990476 452080235326908437151013 := by
  unfold tailWord_990476
  simp only [CollatzResearch.WordTrace]
  refine ⟨18062813779841043339203641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24083751706454724452271521 18062813779841043339203641)
  ·
    refine ⟨13547110334880782504402731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18062813779841043339203641 13547110334880782504402731)
    ·
      refine ⟨20320665502321173756604097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13547110334880782504402731 20320665502321173756604097)
      ·
        refine ⟨15240499126740880317453073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20320665502321173756604097 15240499126740880317453073)
        ·
          refine ⟨11430374345055660238089805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15240499126740880317453073 11430374345055660238089805)
          ·
            refine ⟨4286390379395872589283677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11430374345055660238089805 4286390379395872589283677)
            ·
              refine ⟨1607396392273452220981379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4286390379395872589283677 1607396392273452220981379)
              ·
                refine ⟨2411094588410178331472069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1607396392273452220981379 2411094588410178331472069)
                ·
                  refine ⟨452080235326908437151013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2411094588410178331472069 452080235326908437151013)
                  ·
                    rfl

theorem cell20_990476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_990476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990476 prefixEnd_990476 := by exact prefixLift 990476
  have htrace : WordTrace (prefixWord ++ tailWord_990476) baseStart_990476 baseEnd_990476 := by
    simpa [prefixWord, tailWord_990476, baseEnd_990476] using wordTrace_append hprefix tailTrace_990476
  have hstable : (prefixWord ++ tailWord_990476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990476).length < 2 ^ (prefixWord ++ tailWord_990476).sum := by decide
  have hdescent : baseEnd_990476 < baseStart_990476 := by decide
  rcases family_descends (prefixWord ++ tailWord_990476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990497 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 6]
def baseStart_990497 : Nat := 118140960795 + 990497 * 2 ^ 59
def prefixEnd_990497 : Nat := 4983230072969 + 3 ^ 40 * 990497 * 2
def baseEnd_990497 : Nat := 452089820299125697450927

theorem tailTrace_990497 : CollatzResearch.WordTrace tailWord_990497 prefixEnd_990497 452089820299125697450927 := by
  unfold tailWord_990497
  simp only [CollatzResearch.WordTrace]
  refine ⟨36126393492606007264921745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24084262328404004843281163 36126393492606007264921745)
  ·
    refine ⟨27094795119454505448691309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36126393492606007264921745 27094795119454505448691309)
    ·
      refine ⟨10160548169795439543259241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27094795119454505448691309 10160548169795439543259241)
      ·
        refine ⟨7620411127346579657444431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10160548169795439543259241 7620411127346579657444431)
        ·
          refine ⟨11430616691019869486166647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7620411127346579657444431 11430616691019869486166647)
          ·
            refine ⟨17145925036529804229249971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11430616691019869486166647 17145925036529804229249971)
            ·
              refine ⟨25718887554794706343874957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17145925036529804229249971 25718887554794706343874957)
              ·
                refine ⟨9644582833048014878953109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25718887554794706343874957 9644582833048014878953109)
                ·
                  refine ⟨452089820299125697450927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9644582833048014878953109 452089820299125697450927)
                  ·
                    rfl

theorem cell20_990497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_990497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990497 prefixEnd_990497 := by exact prefixLift 990497
  have htrace : WordTrace (prefixWord ++ tailWord_990497) baseStart_990497 baseEnd_990497 := by
    simpa [prefixWord, tailWord_990497, baseEnd_990497] using wordTrace_append hprefix tailTrace_990497
  have hstable : (prefixWord ++ tailWord_990497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990497).length < 2 ^ (prefixWord ++ tailWord_990497).sum := by decide
  have hdescent : baseEnd_990497 < baseStart_990497 := by decide
  rcases family_descends (prefixWord ++ tailWord_990497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990521 : List Nat := [1, 2, 1, 6, 2, 8]
def baseStart_990521 : Nat := 118140960795 + 990521 * 2 ^ 59
def prefixEnd_990521 : Nat := 4983230072969 + 3 ^ 40 * 990521 * 2
def baseEnd_990521 : Nat := 16744473131595862246327

theorem tailTrace_990521 : CollatzResearch.WordTrace tailWord_990521 prefixEnd_990521 16744473131595862246327 := by
  unfold tailWord_990521
  simp only [CollatzResearch.WordTrace]
  refine ⟨36127268844519059363795417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24084845896346039575863611 36127268844519059363795417)
  ·
    refine ⟨27095451633389294522846563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36127268844519059363795417 27095451633389294522846563)
    ·
      refine ⟨40643177450083941784269845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27095451633389294522846563 40643177450083941784269845)
      ·
        refine ⟨1905148942972684771137649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40643177450083941784269845 1905148942972684771137649)
        ·
          refine ⟨1428861707229513578353237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1905148942972684771137649 1428861707229513578353237)
          ·
            refine ⟨16744473131595862246327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1428861707229513578353237 16744473131595862246327)
            ·
              rfl

theorem cell20_990521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 8].length) (baseStart_990521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990521 prefixEnd_990521 := by exact prefixLift 990521
  have htrace : WordTrace (prefixWord ++ tailWord_990521) baseStart_990521 baseEnd_990521 := by
    simpa [prefixWord, tailWord_990521, baseEnd_990521] using wordTrace_append hprefix tailTrace_990521
  have hstable : (prefixWord ++ tailWord_990521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990521).length < 2 ^ (prefixWord ++ tailWord_990521).sum := by decide
  have hdescent : baseEnd_990521 < baseStart_990521 := by decide
  rcases family_descends (prefixWord ++ tailWord_990521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990600 : List Nat := [2, 1, 3, 3, 1, 3, 3, 1, 3]
def baseStart_990600 : Nat := 118140960795 + 990600 * 2 ^ 59
def prefixEnd_990600 : Nat := 4983230072969 + 3 ^ 40 * 990600 * 2
def baseEnd_990600 : Nat := 452136832305715117017173

theorem tailTrace_990600 : CollatzResearch.WordTrace tailWord_990600 prefixEnd_990600 452136832305715117017173 := by
  unfold tailWord_990600
  simp only [CollatzResearch.WordTrace]
  refine ⟨18065075105616427927960627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24086766807488570570614169 18065075105616427927960627)
  ·
    refine ⟨27097612658424641891940941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18065075105616427927960627 27097612658424641891940941)
    ·
      refine ⟨10161604746909240709477853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27097612658424641891940941 10161604746909240709477853)
      ·
        refine ⟨3810601780090965266054195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10161604746909240709477853 3810601780090965266054195)
        ·
          refine ⟨5715902670136447899081293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3810601780090965266054195 5715902670136447899081293)
          ·
            refine ⟨2143463501301167962155485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5715902670136447899081293 2143463501301167962155485)
            ·
              refine ⟨803798812987937985808307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2143463501301167962155485 803798812987937985808307)
              ·
                refine ⟨1205698219481906978712461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803798812987937985808307 1205698219481906978712461)
                ·
                  refine ⟨452136832305715117017173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1205698219481906978712461 452136832305715117017173)
                  ·
                    rfl

theorem cell20_990600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 3].length) (baseStart_990600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990600 prefixEnd_990600 := by exact prefixLift 990600
  have htrace : WordTrace (prefixWord ++ tailWord_990600) baseStart_990600 baseEnd_990600 := by
    simpa [prefixWord, tailWord_990600, baseEnd_990600] using wordTrace_append hprefix tailTrace_990600
  have hstable : (prefixWord ++ tailWord_990600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990600).length < 2 ^ (prefixWord ++ tailWord_990600).sum := by decide
  have hdescent : baseEnd_990600 < baseStart_990600 := by decide
  rcases family_descends (prefixWord ++ tailWord_990600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990610 : List Nat := [3, 2, 3, 3, 1, 2, 2, 4]
def baseStart_990610 : Nat := 118140960795 + 990610 * 2 ^ 59
def prefixEnd_990610 : Nat := 4983230072969 + 3 ^ 40 * 990610 * 2
def baseEnd_990610 : Nat := 150713798859399842227933

theorem tailTrace_990610 : CollatzResearch.WordTrace tailWord_990610 prefixEnd_990610 150713798859399842227933 := by
  unfold tailWord_990610
  simp only [CollatzResearch.WordTrace]
  refine ⟨9032628735299156890946321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24087009960797751709190189 9032628735299156890946321)
  ·
    refine ⟨6774471551474367668209741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9032628735299156890946321 6774471551474367668209741)
    ·
      refine ⟨2540426831802887875578653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6774471551474367668209741 2540426831802887875578653)
      ·
        refine ⟨952660061926082953341995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2540426831802887875578653 952660061926082953341995)
        ·
          refine ⟨1428990092889124430012993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952660061926082953341995 1428990092889124430012993)
          ·
            refine ⟨1071742569666843322509745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1428990092889124430012993 1071742569666843322509745)
            ·
              refine ⟨803806927250132491882309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1071742569666843322509745 803806927250132491882309)
              ·
                refine ⟨150713798859399842227933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 803806927250132491882309 150713798859399842227933)
                ·
                  rfl

theorem cell20_990610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_990610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990610 prefixEnd_990610 := by exact prefixLift 990610
  have htrace : WordTrace (prefixWord ++ tailWord_990610) baseStart_990610 baseEnd_990610 := by
    simpa [prefixWord, tailWord_990610, baseEnd_990610] using wordTrace_append hprefix tailTrace_990610
  have hstable : (prefixWord ++ tailWord_990610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990610).length < 2 ^ (prefixWord ++ tailWord_990610).sum := by decide
  have hdescent : baseEnd_990610 < baseStart_990610 := by decide
  rcases family_descends (prefixWord ++ tailWord_990610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990620 : List Nat := [2, 2, 3, 4, 2, 1, 1, 3, 2]
def baseStart_990620 : Nat := 118140960795 + 990620 * 2 ^ 59
def prefixEnd_990620 : Nat := 4983230072969 + 3 ^ 40 * 990620 * 2
def baseEnd_990620 : Nat := 452145960850683936350425

theorem tailTrace_990620 : CollatzResearch.WordTrace tailWord_990620 prefixEnd_990620 452145960850683936350425 := by
  unfold tailWord_990620
  simp only [CollatzResearch.WordTrace]
  refine ⟨18065439835580199635824657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24087253114106932847766209 18065439835580199635824657)
  ·
    refine ⟨13549079876685149726868493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18065439835580199635824657 13549079876685149726868493)
    ·
      refine ⟨5080904953756931147575685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13549079876685149726868493 5080904953756931147575685)
      ·
        refine ⟨952669678829424590170441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5080904953756931147575685 952669678829424590170441)
        ·
          refine ⟨714502259122068442627831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 952669678829424590170441 714502259122068442627831)
          ·
            refine ⟨1071753388683102663941747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714502259122068442627831 1071753388683102663941747)
            ·
              refine ⟨1607630083024653995912621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071753388683102663941747 1607630083024653995912621)
              ·
                refine ⟨602861281134245248467233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1607630083024653995912621 602861281134245248467233)
                ·
                  refine ⟨452145960850683936350425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 602861281134245248467233 452145960850683936350425)
                  ·
                    rfl

theorem cell20_990620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_990620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990620 prefixEnd_990620 := by exact prefixLift 990620
  have htrace : WordTrace (prefixWord ++ tailWord_990620) baseStart_990620 baseEnd_990620 := by
    simpa [prefixWord, tailWord_990620, baseEnd_990620] using wordTrace_append hprefix tailTrace_990620
  have hstable : (prefixWord ++ tailWord_990620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990620).length < 2 ^ (prefixWord ++ tailWord_990620).sum := by decide
  have hdescent : baseEnd_990620 < baseStart_990620 := by decide
  rcases family_descends (prefixWord ++ tailWord_990620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990645 : List Nat := [1, 3, 3, 2, 2, 3, 1, 1, 4]
def baseStart_990645 : Nat := 118140960795 + 990645 * 2 ^ 59
def prefixEnd_990645 : Nat := 4983230072969 + 3 ^ 40 * 990645 * 2
def baseEnd_990645 : Nat := 452157371531894960516989

theorem tailTrace_990645 : CollatzResearch.WordTrace tailWord_990645 prefixEnd_990645 452157371531894960516989 := by
  unfold tailWord_990645
  simp only [CollatzResearch.WordTrace]
  refine ⟨36131791496069828541309389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24087860997379885694206259 36131791496069828541309389)
  ·
    refine ⟨13549421811026185702991021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36131791496069828541309389 13549421811026185702991021)
    ·
      refine ⟨5081033179134819638621633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13549421811026185702991021 5081033179134819638621633)
      ·
        refine ⟨3810774884351114728966225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5081033179134819638621633 3810774884351114728966225)
        ·
          refine ⟨2858081163263336046724669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3810774884351114728966225 2858081163263336046724669)
          ·
            refine ⟨1071780436223751017521751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2858081163263336046724669 1071780436223751017521751)
            ·
              refine ⟨1607670654335626526282627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071780436223751017521751 1607670654335626526282627)
              ·
                refine ⟨2411505981503439789423941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1607670654335626526282627 2411505981503439789423941)
                ·
                  refine ⟨452157371531894960516989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2411505981503439789423941 452157371531894960516989)
                  ·
                    rfl

theorem cell20_990645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_990645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990645 prefixEnd_990645 := by exact prefixLift 990645
  have htrace : WordTrace (prefixWord ++ tailWord_990645) baseStart_990645 baseEnd_990645 := by
    simpa [prefixWord, tailWord_990645, baseEnd_990645] using wordTrace_append hprefix tailTrace_990645
  have hstable : (prefixWord ++ tailWord_990645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990645).length < 2 ^ (prefixWord ++ tailWord_990645).sum := by decide
  have hdescent : baseEnd_990645 < baseStart_990645 := by decide
  rcases family_descends (prefixWord ++ tailWord_990645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990652 : List Nat := [2, 2, 2, 4, 2, 1, 2, 5]
def baseStart_990652 : Nat := 118140960795 + 990652 * 2 ^ 59
def prefixEnd_990652 : Nat := 4983230072969 + 3 ^ 40 * 990652 * 2
def baseEnd_990652 : Nat := 150720188840878015761209

theorem tailTrace_990652 : CollatzResearch.WordTrace tailWord_990652 prefixEnd_990652 150720188840878015761209 := by
  unfold tailWord_990652
  simp only [CollatzResearch.WordTrace]
  refine ⟨18066023403522234368407105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24088031204696312491209473 18066023403522234368407105)
  ·
    refine ⟨13549517552641675776305329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18066023403522234368407105 13549517552641675776305329)
    ·
      refine ⟨10162138164481256832228997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13549517552641675776305329 10162138164481256832228997)
      ·
        refine ⟨1905400905840235656042937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10162138164481256832228997 1905400905840235656042937)
        ·
          refine ⟨1429050679380176742032203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1905400905840235656042937 1429050679380176742032203)
          ·
            refine ⟨2143576019070265113048305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429050679380176742032203 2143576019070265113048305)
            ·
              refine ⟨1607682014302698834786229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2143576019070265113048305 1607682014302698834786229)
              ·
                refine ⟨150720188840878015761209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1607682014302698834786229 150720188840878015761209)
                ·
                  rfl

theorem cell20_990652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_990652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990652 prefixEnd_990652 := by exact prefixLift 990652
  have htrace : WordTrace (prefixWord ++ tailWord_990652) baseStart_990652 baseEnd_990652 := by
    simpa [prefixWord, tailWord_990652, baseEnd_990652] using wordTrace_append hprefix tailTrace_990652
  have hstable : (prefixWord ++ tailWord_990652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990652).length < 2 ^ (prefixWord ++ tailWord_990652).sum := by decide
  have hdescent : baseEnd_990652 < baseStart_990652 := by decide
  rcases family_descends (prefixWord ++ tailWord_990652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990656 : List Nat := [2, 1, 1, 2, 3, 1, 3, 7]
def baseStart_990656 : Nat := 118140960795 + 990656 * 2 ^ 59
def prefixEnd_990656 : Nat := 4983230072969 + 3 ^ 40 * 990656 * 2
def baseEnd_990656 : Nat := 150720797410542603716759

theorem tailTrace_990656 : CollatzResearch.WordTrace tailWord_990656 prefixEnd_990656 150720797410542603716759 := by
  unfold tailWord_990656
  simp only [CollatzResearch.WordTrace]
  refine ⟨18066096349514988709979911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24088128466019984946639881 18066096349514988709979911)
  ·
    refine ⟨27099144524272483064969867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18066096349514988709979911 27099144524272483064969867)
    ·
      refine ⟨40648716786408724597454801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27099144524272483064969867 40648716786408724597454801)
      ·
        refine ⟨30486537589806543448091101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40648716786408724597454801 30486537589806543448091101)
        ·
          refine ⟨11432451596177453793034163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30486537589806543448091101 11432451596177453793034163)
          ·
            refine ⟨17148677394266180689551245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11432451596177453793034163 17148677394266180689551245)
            ·
              refine ⟨6430754022849817758581717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17148677394266180689551245 6430754022849817758581717)
              ·
                refine ⟨150720797410542603716759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6430754022849817758581717 150720797410542603716759)
                ·
                  rfl

theorem cell20_990656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_990656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990656 prefixEnd_990656 := by exact prefixLift 990656
  have htrace : WordTrace (prefixWord ++ tailWord_990656) baseStart_990656 baseEnd_990656 := by
    simpa [prefixWord, tailWord_990656, baseEnd_990656] using wordTrace_append hprefix tailTrace_990656
  have hstable : (prefixWord ++ tailWord_990656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990656).length < 2 ^ (prefixWord ++ tailWord_990656).sum := by decide
  have hdescent : baseEnd_990656 < baseStart_990656 := by decide
  rcases family_descends (prefixWord ++ tailWord_990656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990659 : List Nat := [1, 1, 1, 3, 1, 1, 8, 1, 3]
def baseStart_990659 : Nat := 118140960795 + 990659 * 2 ^ 59
def prefixEnd_990659 : Nat := 4983230072969 + 3 ^ 40 * 990659 * 2
def baseEnd_990659 : Nat := 452163761513373134050265

theorem tailTrace_990659 : CollatzResearch.WordTrace tailWord_990659 prefixEnd_990659 452163761513373134050265 := by
  unfold tailWord_990659
  simp only [CollatzResearch.WordTrace]
  refine ⟨36132302118019108932319031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24088201412012739288212687 36132302118019108932319031)
  ·
    refine ⟨54198453177028663398478547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36132302118019108932319031 54198453177028663398478547)
    ·
      refine ⟨81297679765542995097717821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54198453177028663398478547 81297679765542995097717821)
      ·
        refine ⟨30486629912078623161644183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81297679765542995097717821 30486629912078623161644183)
        ·
          refine ⟨45729944868117934742466275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30486629912078623161644183 45729944868117934742466275)
          ·
            refine ⟨68594917302176902113699413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45729944868117934742466275 68594917302176902113699413)
            ·
              refine ⟨803846687134885571644915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 68594917302176902113699413 803846687134885571644915)
              ·
                refine ⟨1205770030702328357467373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803846687134885571644915 1205770030702328357467373)
                ·
                  refine ⟨452163761513373134050265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1205770030702328357467373 452163761513373134050265)
                  ·
                    rfl

theorem cell20_990659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 3].length) (baseStart_990659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990659 prefixEnd_990659 := by exact prefixLift 990659
  have htrace : WordTrace (prefixWord ++ tailWord_990659) baseStart_990659 baseEnd_990659 := by
    simpa [prefixWord, tailWord_990659, baseEnd_990659] using wordTrace_append hprefix tailTrace_990659
  have hstable : (prefixWord ++ tailWord_990659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990659).length < 2 ^ (prefixWord ++ tailWord_990659).sum := by decide
  have hdescent : baseEnd_990659 < baseStart_990659 := by decide
  rcases family_descends (prefixWord ++ tailWord_990659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990752 : List Nat := [2, 1, 1, 6, 1, 3, 1, 2, 3]
def baseStart_990752 : Nat := 118140960795 + 990752 * 2 ^ 59
def prefixEnd_990752 : Nat := 4983230072969 + 3 ^ 40 * 990752 * 2
def baseEnd_990752 : Nat := 452206209247478143949885

theorem tailTrace_990752 : CollatzResearch.WordTrace tailWord_990752 prefixEnd_990752 452206209247478143949885 := by
  unfold tailWord_990752
  simp only [CollatzResearch.WordTrace]
  refine ⟨18067847053341092907727255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24090462737788123876969673 18067847053341092907727255)
  ·
    refine ⟨27101770580011639361590883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18067847053341092907727255 27101770580011639361590883)
    ·
      refine ⟨40652655870017459042386325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27101770580011639361590883 40652655870017459042386325)
      ·
        refine ⟨1905593243907068392611859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40652655870017459042386325 1905593243907068392611859)
        ·
          refine ⟨2858389865860602588917789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1905593243907068392611859 2858389865860602588917789)
          ·
            refine ⟨1071896199697725970844171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2858389865860602588917789 1071896199697725970844171)
            ·
              refine ⟨1607844299546588956266257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071896199697725970844171 1607844299546588956266257)
              ·
                refine ⟨1205883224659941717199693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1607844299546588956266257 1205883224659941717199693)
                ·
                  refine ⟨452206209247478143949885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1205883224659941717199693 452206209247478143949885)
                  ·
                    rfl

theorem cell20_990752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 3].length) (baseStart_990752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990752 prefixEnd_990752 := by exact prefixLift 990752
  have htrace : WordTrace (prefixWord ++ tailWord_990752) baseStart_990752 baseEnd_990752 := by
    simpa [prefixWord, tailWord_990752, baseEnd_990752] using wordTrace_append hprefix tailTrace_990752
  have hstable : (prefixWord ++ tailWord_990752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990752).length < 2 ^ (prefixWord ++ tailWord_990752).sum := by decide
  have hdescent : baseEnd_990752 < baseStart_990752 := by decide
  rcases family_descends (prefixWord ++ tailWord_990752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990770 : List Nat := [3, 2, 1, 1, 2, 1, 1, 9]
def baseStart_990770 : Nat := 118140960795 + 990770 * 2 ^ 59
def prefixEnd_990770 : Nat := 4983230072969 + 3 ^ 40 * 990770 * 2
def baseEnd_990770 : Nat := 150738141645983360449937

theorem tailTrace_990770 : CollatzResearch.WordTrace tailWord_990770 prefixEnd_990770 150738141645983360449937 := by
  unfold tailWord_990770
  simp only [CollatzResearch.WordTrace]
  refine ⟨9034087655154243722402441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24090900413744649926406509 9034087655154243722402441)
  ·
    refine ⟨6775565741365682791801831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9034087655154243722402441 6775565741365682791801831)
    ·
      refine ⟨10163348612048524187702747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6775565741365682791801831 10163348612048524187702747)
      ·
        refine ⟨15245022918072786281554121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10163348612048524187702747 15245022918072786281554121)
        ·
          refine ⟨11433767188554589711165591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15245022918072786281554121 11433767188554589711165591)
          ·
            refine ⟨17150650782831884566748387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11433767188554589711165591 17150650782831884566748387)
            ·
              refine ⟨25725976174247826850122581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17150650782831884566748387 25725976174247826850122581)
              ·
                refine ⟨150738141645983360449937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25725976174247826850122581 150738141645983360449937)
                ·
                  rfl

theorem cell20_990770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_990770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990770 prefixEnd_990770 := by exact prefixLift 990770
  have htrace : WordTrace (prefixWord ++ tailWord_990770) baseStart_990770 baseEnd_990770 := by
    simpa [prefixWord, tailWord_990770, baseEnd_990770] using wordTrace_append hprefix tailTrace_990770
  have hstable : (prefixWord ++ tailWord_990770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990770).length < 2 ^ (prefixWord ++ tailWord_990770).sum := by decide
  have hdescent : baseEnd_990770 < baseStart_990770 := by decide
  rcases family_descends (prefixWord ++ tailWord_990770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990866 : List Nat := [3, 2, 3, 1, 3, 1, 2, 2, 3]
def baseStart_990866 : Nat := 118140960795 + 990866 * 2 ^ 59
def prefixEnd_990866 : Nat := 4983230072969 + 3 ^ 40 * 990866 * 2
def baseEnd_990866 : Nat := 452258241953800414149419

theorem tailTrace_990866 : CollatzResearch.WordTrace tailWord_990866 prefixEnd_990866 452258241953800414149419 := by
  unfold tailWord_990866
  simp only [CollatzResearch.WordTrace]
  refine ⟨9034963007067295821276113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24093234685512788856736301 9034963007067295821276113)
  ·
    refine ⟨6776222255300471865957085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9034963007067295821276113 6776222255300471865957085)
    ·
      refine ⟨2541083345737676949733907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6776222255300471865957085 2541083345737676949733907)
      ·
        refine ⟨3811625018606515424600861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2541083345737676949733907 3811625018606515424600861)
        ·
          refine ⟨1429359381977443284225323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3811625018606515424600861 1429359381977443284225323)
          ·
            refine ⟨2144039072966164926337985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429359381977443284225323 2144039072966164926337985)
            ·
              refine ⟨1608029304724623694753489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2144039072966164926337985 1608029304724623694753489)
              ·
                refine ⟨1206021978543467771065117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1608029304724623694753489 1206021978543467771065117)
                ·
                  refine ⟨452258241953800414149419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1206021978543467771065117 452258241953800414149419)
                  ·
                    rfl

theorem cell20_990866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_990866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990866 prefixEnd_990866 := by exact prefixLift 990866
  have htrace : WordTrace (prefixWord ++ tailWord_990866) baseStart_990866 baseEnd_990866 := by
    simpa [prefixWord, tailWord_990866, baseEnd_990866] using wordTrace_append hprefix tailTrace_990866
  have hstable : (prefixWord ++ tailWord_990866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990866).length < 2 ^ (prefixWord ++ tailWord_990866).sum := by decide
  have hdescent : baseEnd_990866 < baseStart_990866 := by decide
  rcases family_descends (prefixWord ++ tailWord_990866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990877 : List Nat := [1, 4, 2, 1, 1, 1, 1, 5, 4]
def baseStart_990877 : Nat := 118140960795 + 990877 * 2 ^ 59
def prefixEnd_990877 : Nat := 4983230072969 + 3 ^ 40 * 990877 * 2
def baseEnd_990877 : Nat := 452263262653533264782707

theorem tailTrace_990877 : CollatzResearch.WordTrace tailWord_990877 prefixEnd_990877 452263262653533264782707 := by
  unfold tailWord_990877
  simp only [CollatzResearch.WordTrace]
  refine ⟨36140253231229332163754885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24093502154152888109169923 36140253231229332163754885)
  ·
    refine ⟨6776297480855499780704041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36140253231229332163754885 6776297480855499780704041)
    ·
      refine ⟨5082223110641624835528031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6776297480855499780704041 5082223110641624835528031)
      ·
        refine ⟨7623334665962437253292047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5082223110641624835528031 7623334665962437253292047)
        ·
          refine ⟨11435001998943655879938071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7623334665962437253292047 11435001998943655879938071)
          ·
            refine ⟨17152502998415483819907107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11435001998943655879938071 17152502998415483819907107)
            ·
              refine ⟨25728754497623225729860661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17152502998415483819907107 25728754497623225729860661)
              ·
                refine ⟨2412070734152177412174437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25728754497623225729860661 2412070734152177412174437)
                ·
                  refine ⟨452263262653533264782707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2412070734152177412174437 452263262653533264782707)
                  ·
                    rfl

theorem cell20_990877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_990877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990877 prefixEnd_990877 := by exact prefixLift 990877
  have htrace : WordTrace (prefixWord ++ tailWord_990877) baseStart_990877 baseEnd_990877 := by
    simpa [prefixWord, tailWord_990877, baseEnd_990877] using wordTrace_append hprefix tailTrace_990877
  have hstable : (prefixWord ++ tailWord_990877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990877).length < 2 ^ (prefixWord ++ tailWord_990877).sum := by decide
  have hdescent : baseEnd_990877 < baseStart_990877 := by decide
  rcases family_descends (prefixWord ++ tailWord_990877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990932 : List Nat := [2, 4, 1, 3, 1, 1, 1, 3, 4]
def baseStart_990932 : Nat := 118140960795 + 990932 * 2 ^ 59
def prefixEnd_990932 : Nat := 4983230072969 + 3 ^ 40 * 990932 * 2
def baseEnd_990932 : Nat := 452288366152197517949149

theorem tailTrace_990932 : CollatzResearch.WordTrace tailWord_990932 prefixEnd_990932 452288366152197517949149 := by
  unfold tailWord_990932
  simp only [CollatzResearch.WordTrace]
  refine ⟨18071129623015038278503525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24094839497353384371338033 18071129623015038278503525)
  ·
    refine ⟨3388336804315319677219411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18071129623015038278503525 3388336804315319677219411)
    ·
      refine ⟨5082505206472979515829117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3388336804315319677219411 5082505206472979515829117)
      ·
        refine ⟨1905939452427367318435919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5082505206472979515829117 1905939452427367318435919)
        ·
          refine ⟨2858909178641050977653879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1905939452427367318435919 2858909178641050977653879)
          ·
            refine ⟨4288363767961576466480819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858909178641050977653879 4288363767961576466480819)
            ·
              refine ⟨6432545651942364699721229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4288363767961576466480819 6432545651942364699721229)
              ·
                refine ⟨2412204619478386762395461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6432545651942364699721229 2412204619478386762395461)
                ·
                  refine ⟨452288366152197517949149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2412204619478386762395461 452288366152197517949149)
                  ·
                    rfl

theorem cell20_990932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_990932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990932 prefixEnd_990932 := by exact prefixLift 990932
  have htrace : WordTrace (prefixWord ++ tailWord_990932) baseStart_990932 baseEnd_990932 := by
    simpa [prefixWord, tailWord_990932, baseEnd_990932] using wordTrace_append hprefix tailTrace_990932
  have hstable : (prefixWord ++ tailWord_990932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990932).length < 2 ^ (prefixWord ++ tailWord_990932).sum := by decide
  have hdescent : baseEnd_990932 < baseStart_990932 := by decide
  rcases family_descends (prefixWord ++ tailWord_990932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990966 : List Nat := [5, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_990966 : Nat := 118140960795 + 990966 * 2 ^ 59
def prefixEnd_990966 : Nat := 4983230072969 + 3 ^ 40 * 990966 * 2
def baseEnd_990966 : Nat := 452303884678644510815677

theorem tailTrace_990966 : CollatzResearch.WordTrace tailWord_990966 prefixEnd_990966 452303884678644510815677 := by
  unfold tailWord_990966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2258968707994181272734047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24095666218604600242496501 2258968707994181272734047)
  ·
    refine ⟨3388453061991271909101071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2258968707994181272734047 3388453061991271909101071)
    ·
      refine ⟨5082679592986907863651607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3388453061991271909101071 5082679592986907863651607)
      ·
        refine ⟨7624019389480361795477411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5082679592986907863651607 7624019389480361795477411)
        ·
          refine ⟨11436029084220542693216117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7624019389480361795477411 11436029084220542693216117)
          ·
            refine ⟨1072127726645675877489011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11436029084220542693216117 1072127726645675877489011)
            ·
              refine ⟨1608191589968513816233517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1072127726645675877489011 1608191589968513816233517)
              ·
                refine ⟨603071846238192681087569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1608191589968513816233517 603071846238192681087569)
                ·
                  refine ⟨452303884678644510815677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603071846238192681087569 452303884678644510815677)
                  ·
                    rfl

theorem cell20_990966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_990966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990966 prefixEnd_990966 := by exact prefixLift 990966
  have htrace : WordTrace (prefixWord ++ tailWord_990966) baseStart_990966 baseEnd_990966 := by
    simpa [prefixWord, tailWord_990966, baseEnd_990966] using wordTrace_append hprefix tailTrace_990966
  have hstable : (prefixWord ++ tailWord_990966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990966).length < 2 ^ (prefixWord ++ tailWord_990966).sum := by decide
  have hdescent : baseEnd_990966 < baseStart_990966 := by decide
  rcases family_descends (prefixWord ++ tailWord_990966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990967 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 5]
def baseStart_990967 : Nat := 118140960795 + 990967 * 2 ^ 59
def prefixEnd_990967 : Nat := 4983230072969 + 3 ^ 40 * 990967 * 2
def baseEnd_990967 : Nat := 452304341105892951782339

theorem tailTrace_990967 : CollatzResearch.WordTrace tailWord_990967 prefixEnd_990967 452304341105892951782339 := by
  unfold tailWord_990967
  simp only [CollatzResearch.WordTrace]
  refine ⟨36143535800903277534531155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24095690533935518356354103 36143535800903277534531155)
  ·
    refine ⟨54215303701354916301796733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36143535800903277534531155 54215303701354916301796733)
    ·
      refine ⟨20330738888008093613173775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54215303701354916301796733 20330738888008093613173775)
      ·
        refine ⟨30496108332012140419760663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20330738888008093613173775 30496108332012140419760663)
        ·
          refine ⟨45744162498018210629640995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30496108332012140419760663 45744162498018210629640995)
          ·
            refine ⟨68616243747027315944461493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45744162498018210629640995 68616243747027315944461493)
            ·
              refine ⟨6432772851283810869793265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68616243747027315944461493 6432772851283810869793265)
              ·
                refine ⟨4824579638462858152344949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6432772851283810869793265 4824579638462858152344949)
                ·
                  refine ⟨452304341105892951782339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4824579638462858152344949 452304341105892951782339)
                  ·
                    rfl

theorem cell20_990967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_990967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990967 prefixEnd_990967 := by exact prefixLift 990967
  have htrace : WordTrace (prefixWord ++ tailWord_990967) baseStart_990967 baseEnd_990967 := by
    simpa [prefixWord, tailWord_990967, baseEnd_990967] using wordTrace_append hprefix tailTrace_990967
  have hstable : (prefixWord ++ tailWord_990967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990967).length < 2 ^ (prefixWord ++ tailWord_990967).sum := by decide
  have hdescent : baseEnd_990967 < baseStart_990967 := by decide
  rcases family_descends (prefixWord ++ tailWord_990967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990984 : List Nat := [2, 1, 3, 2, 2, 1, 2, 4, 3]
def baseStart_990984 : Nat := 118140960795 + 990984 * 2 ^ 59
def prefixEnd_990984 : Nat := 4983230072969 + 3 ^ 40 * 990984 * 2
def baseEnd_990984 : Nat := 452312100369116448215603

theorem tailTrace_990984 : CollatzResearch.WordTrace tailWord_990984 prefixEnd_990984 452312100369116448215603 := by
  unfold tailWord_990984
  simp only [CollatzResearch.WordTrace]
  refine ⟨18072077920920844718950003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24096103894561126291933337 18072077920920844718950003)
  ·
    refine ⟨27108116881381267078425005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18072077920920844718950003 27108116881381267078425005)
    ·
      refine ⟨10165543830517975154409377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27108116881381267078425005 10165543830517975154409377)
      ·
        refine ⟨7624157872888481365807033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10165543830517975154409377 7624157872888481365807033)
        ·
          refine ⟨5718118404666361024355275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7624157872888481365807033 5718118404666361024355275)
          ·
            refine ⟨8577177606999541536532913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5718118404666361024355275 8577177606999541536532913)
            ·
              refine ⟨6432883205249656152399685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8577177606999541536532913 6432883205249656152399685)
              ·
                refine ⟨1206165600984310528574941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6432883205249656152399685 1206165600984310528574941)
                ·
                  refine ⟨452312100369116448215603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1206165600984310528574941 452312100369116448215603)
                  ·
                    rfl

theorem cell20_990984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_990984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990984 prefixEnd_990984 := by exact prefixLift 990984
  have htrace : WordTrace (prefixWord ++ tailWord_990984) baseStart_990984 baseEnd_990984 := by
    simpa [prefixWord, tailWord_990984, baseEnd_990984] using wordTrace_append hprefix tailTrace_990984
  have hstable : (prefixWord ++ tailWord_990984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990984).length < 2 ^ (prefixWord ++ tailWord_990984).sum := by decide
  have hdescent : baseEnd_990984 < baseStart_990984 := by decide
  rcases family_descends (prefixWord ++ tailWord_990984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_990994 : List Nat := [3, 2, 4, 1, 1, 2, 2, 5]
def baseStart_990994 : Nat := 118140960795 + 990994 * 2 ^ 59
def prefixEnd_990994 : Nat := 4983230072969 + 3 ^ 40 * 990994 * 2
def baseEnd_990994 : Nat := 150772221547200285960743

theorem tailTrace_990994 : CollatzResearch.WordTrace tailWord_990994 prefixEnd_990994 150772221547200285960743 := by
  unfold tailWord_990994
  simp only [CollatzResearch.WordTrace]
  refine ⟨9036130142951365286441009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24096347047870307430509357 9036130142951365286441009)
  ·
    refine ⟨6777097607213523964830757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9036130142951365286441009 6777097607213523964830757)
    ·
      refine ⟨1270705801352535743405767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6777097607213523964830757 1270705801352535743405767)
      ·
        refine ⟨1906058702028803615108651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1270705801352535743405767 1906058702028803615108651)
        ·
          refine ⟨2859088053043205422662977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1906058702028803615108651 2859088053043205422662977)
          ·
            refine ⟨2144316039782404066997233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2859088053043205422662977 2144316039782404066997233)
            ·
              refine ⟨1608237029836803050247925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2144316039782404066997233 1608237029836803050247925)
              ·
                refine ⟨150772221547200285960743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1608237029836803050247925 150772221547200285960743)
                ·
                  rfl

theorem cell20_990994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_990994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_990994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_990994 prefixEnd_990994 := by exact prefixLift 990994
  have htrace : WordTrace (prefixWord ++ tailWord_990994) baseStart_990994 baseEnd_990994 := by
    simpa [prefixWord, tailWord_990994, baseEnd_990994] using wordTrace_append hprefix tailTrace_990994
  have hstable : (prefixWord ++ tailWord_990994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_990994).length < 2 ^ (prefixWord ++ tailWord_990994).sum := by decide
  have hdescent : baseEnd_990994 < baseStart_990994 := by decide
  rcases family_descends (prefixWord ++ tailWord_990994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991039 : List Nat := [1, 1, 2, 2, 6, 1, 2, 2, 3]
def baseStart_991039 : Nat := 118140960795 + 991039 * 2 ^ 59
def prefixEnd_991039 : Nat := 4983230072969 + 3 ^ 40 * 991039 * 2
def baseEnd_991039 : Nat := 452337203867780701382045

theorem tailTrace_991039 : CollatzResearch.WordTrace tailWord_991039 prefixEnd_991039 452337203867780701382045 := by
  unfold tailWord_991039
  simp only [CollatzResearch.WordTrace]
  refine ⟨36146161856642433831152171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24097441237761622554101447 36146161856642433831152171)
  ·
    refine ⟨54219242784963650746728257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36146161856642433831152171 54219242784963650746728257)
    ·
      refine ⟨40664432088722738060046193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54219242784963650746728257 40664432088722738060046193)
      ·
        refine ⟨30498324066542053545034645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40664432088722738060046193 30498324066542053545034645)
        ·
          refine ⟨1429608940619158759923499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30498324066542053545034645 1429608940619158759923499)
          ·
            refine ⟨2144413410928738139885249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429608940619158759923499 2144413410928738139885249)
            ·
              refine ⟨1608310058196553604913937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2144413410928738139885249 1608310058196553604913937)
              ·
                refine ⟨1206232543647415203685453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1608310058196553604913937 1206232543647415203685453)
                ·
                  refine ⟨452337203867780701382045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1206232543647415203685453 452337203867780701382045)
                  ·
                    rfl

theorem cell20_991039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 3].length) (baseStart_991039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991039 prefixEnd_991039 := by exact prefixLift 991039
  have htrace : WordTrace (prefixWord ++ tailWord_991039) baseStart_991039 baseEnd_991039 := by
    simpa [prefixWord, tailWord_991039, baseEnd_991039] using wordTrace_append hprefix tailTrace_991039
  have hstable : (prefixWord ++ tailWord_991039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991039).length < 2 ^ (prefixWord ++ tailWord_991039).sum := by decide
  have hdescent : baseEnd_991039 < baseStart_991039 := by decide
  rcases family_descends (prefixWord ++ tailWord_991039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991084 : List Nat := [2, 2, 1, 1, 4, 2, 1, 5, 2]
def baseStart_991084 : Nat := 118140960795 + 991084 * 2 ^ 59
def prefixEnd_991084 : Nat := 4983230072969 + 3 ^ 40 * 991084 * 2
def baseEnd_991084 : Nat := 452357743093960544881861

theorem tailTrace_991084 : CollatzResearch.WordTrace tailWord_991084 prefixEnd_991084 452357743093960544881861 := by
  unfold tailWord_991084
  simp only [CollatzResearch.WordTrace]
  refine ⟨18073901570739703258270153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24098535427652937677693537 18073901570739703258270153)
  ·
    refine ⟨13555426178054777443702615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18073901570739703258270153 13555426178054777443702615)
    ·
      refine ⟨20333139267082166165553923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13555426178054777443702615 20333139267082166165553923)
      ·
        refine ⟨30499708900623249248330885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20333139267082166165553923 30499708900623249248330885)
        ·
          refine ⟨5718695418866859234062041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30499708900623249248330885 5718695418866859234062041)
          ·
            refine ⟨4289021564150144425546531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5718695418866859234062041 4289021564150144425546531)
            ·
              refine ⟨6433532346225216638319797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4289021564150144425546531 6433532346225216638319797)
              ·
                refine ⟨603143657458614059842481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6433532346225216638319797 603143657458614059842481)
                ·
                  refine ⟨452357743093960544881861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603143657458614059842481 452357743093960544881861)
                  ·
                    rfl

theorem cell20_991084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_991084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991084 prefixEnd_991084 := by exact prefixLift 991084
  have htrace : WordTrace (prefixWord ++ tailWord_991084) baseStart_991084 baseEnd_991084 := by
    simpa [prefixWord, tailWord_991084, baseEnd_991084] using wordTrace_append hprefix tailTrace_991084
  have hstable : (prefixWord ++ tailWord_991084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991084).length < 2 ^ (prefixWord ++ tailWord_991084).sum := by decide
  have hdescent : baseEnd_991084 < baseStart_991084 := by decide
  rcases family_descends (prefixWord ++ tailWord_991084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991088 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 8]
def baseStart_991088 : Nat := 118140960795 + 991088 * 2 ^ 59
def prefixEnd_991088 : Nat := 4983230072969 + 3 ^ 40 * 991088 * 2
def baseEnd_991088 : Nat := 452359568802954308748511

theorem tailTrace_991088 : CollatzResearch.WordTrace tailWord_991088 prefixEnd_991088 452359568802954308748511 := by
  unfold tailWord_991088
  simp only [CollatzResearch.WordTrace]
  refine ⟨18073974516732457599842959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24098632688976610133123945 18073974516732457599842959)
  ·
    refine ⟨27110961775098686399764439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18073974516732457599842959 27110961775098686399764439)
    ·
      refine ⟨40666442662648029599646659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27110961775098686399764439 40666442662648029599646659)
      ·
        refine ⟨60999663993972044399469989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40666442662648029599646659 60999663993972044399469989)
        ·
          refine ⟨11437436998869758324900623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60999663993972044399469989 11437436998869758324900623)
          ·
            refine ⟨17156155498304637487350935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11437436998869758324900623 17156155498304637487350935)
            ·
              refine ⟨25734233247456956231026403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17156155498304637487350935 25734233247456956231026403)
              ·
                refine ⟨38601349871185434346539605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25734233247456956231026403 38601349871185434346539605)
                ·
                  refine ⟨452359568802954308748511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38601349871185434346539605 452359568802954308748511)
                  ·
                    rfl

theorem cell20_991088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_991088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991088 prefixEnd_991088 := by exact prefixLift 991088
  have htrace : WordTrace (prefixWord ++ tailWord_991088) baseStart_991088 baseEnd_991088 := by
    simpa [prefixWord, tailWord_991088, baseEnd_991088] using wordTrace_append hprefix tailTrace_991088
  have hstable : (prefixWord ++ tailWord_991088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991088).length < 2 ^ (prefixWord ++ tailWord_991088).sum := by decide
  have hdescent : baseEnd_991088 < baseStart_991088 := by decide
  rcases family_descends (prefixWord ++ tailWord_991088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991098 : List Nat := [3, 1, 1, 1, 1, 1, 7, 2, 3]
def baseStart_991098 : Nat := 118140960795 + 991098 * 2 ^ 59
def prefixEnd_991098 : Nat := 4983230072969 + 3 ^ 40 * 991098 * 2
def baseEnd_991098 : Nat := 452364133075438718415137

theorem tailTrace_991098 : CollatzResearch.WordTrace tailWord_991098 prefixEnd_991098 452364133075438718415137 := by
  unfold tailWord_991098
  simp only [CollatzResearch.WordTrace]
  refine ⟨9037078440857171726887487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24098875842285791271699965 9037078440857171726887487)
  ·
    refine ⟨13555617661285757590331231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9037078440857171726887487 13555617661285757590331231)
    ·
      refine ⟨20333426491928636385496847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13555617661285757590331231 20333426491928636385496847)
      ·
        refine ⟨30500139737892954578245271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20333426491928636385496847 30500139737892954578245271)
        ·
          refine ⟨45750209606839431867367907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30500139737892954578245271 45750209606839431867367907)
          ·
            refine ⟨68625314410259147801051861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45750209606839431867367907 68625314410259147801051861)
            ·
              refine ⟨1608405806490448776587153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 68625314410259147801051861 1608405806490448776587153)
              ·
                refine ⟨1206304354867836582440365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1608405806490448776587153 1206304354867836582440365)
                ·
                  refine ⟨452364133075438718415137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1206304354867836582440365 452364133075438718415137)
                  ·
                    rfl

theorem cell20_991098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_991098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991098 prefixEnd_991098 := by exact prefixLift 991098
  have htrace : WordTrace (prefixWord ++ tailWord_991098) baseStart_991098 baseEnd_991098 := by
    simpa [prefixWord, tailWord_991098, baseEnd_991098] using wordTrace_append hprefix tailTrace_991098
  have hstable : (prefixWord ++ tailWord_991098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991098).length < 2 ^ (prefixWord ++ tailWord_991098).sum := by decide
  have hdescent : baseEnd_991098 < baseStart_991098 := by decide
  rcases family_descends (prefixWord ++ tailWord_991098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991122 : List Nat := [3, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_991122 : Nat := 118140960795 + 991122 * 2 ^ 59
def prefixEnd_991122 : Nat := 4983230072969 + 3 ^ 40 * 991122 * 2
def baseEnd_991122 : Nat := 452375087329401301615039

theorem tailTrace_991122 : CollatzResearch.WordTrace tailWord_991122 prefixEnd_991122 452375087329401301615039 := by
  unfold tailWord_991122
  simp only [CollatzResearch.WordTrace]
  refine ⟨9037297278835434751605905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24099459410227826004282413 9037297278835434751605905)
  ·
    refine ⟨6777972959126576063704429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9037297278835434751605905 6777972959126576063704429)
    ·
      refine ⟨2541739859672466023889161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6777972959126576063704429 2541739859672466023889161)
      ·
        refine ⟨1906304894754349517916871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2541739859672466023889161 1906304894754349517916871)
        ·
          refine ⟨2859457342131524276875307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1906304894754349517916871 2859457342131524276875307)
          ·
            refine ⟨4289186013197286415312961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2859457342131524276875307 4289186013197286415312961)
            ·
              refine ⟨3216889509897964811484721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4289186013197286415312961 3216889509897964811484721)
              ·
                refine ⟨2412667132423473608613541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3216889509897964811484721 2412667132423473608613541)
                ·
                  refine ⟨452375087329401301615039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2412667132423473608613541 452375087329401301615039)
                  ·
                    rfl

theorem cell20_991122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_991122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991122 prefixEnd_991122 := by exact prefixLift 991122
  have htrace : WordTrace (prefixWord ++ tailWord_991122) baseStart_991122 baseEnd_991122 := by
    simpa [prefixWord, tailWord_991122, baseEnd_991122] using wordTrace_append hprefix tailTrace_991122
  have hstable : (prefixWord ++ tailWord_991122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991122).length < 2 ^ (prefixWord ++ tailWord_991122).sum := by decide
  have hdescent : baseEnd_991122 < baseStart_991122 := by decide
  rcases family_descends (prefixWord ++ tailWord_991122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991156 : List Nat := [2, 5, 2, 1, 2, 2, 1, 1, 4]
def baseStart_991156 : Nat := 118140960795 + 991156 * 2 ^ 59
def prefixEnd_991156 : Nat := 4983230072969 + 3 ^ 40 * 991156 * 2
def baseEnd_991156 : Nat := 452390605855848294481567

theorem tailTrace_991156 : CollatzResearch.WordTrace tailWord_991156 prefixEnd_991156 452390605855848294481567 := by
  unfold tailWord_991156
  simp only [CollatzResearch.WordTrace]
  refine ⟨18075214598609281406580661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24100286131479041875440881 18075214598609281406580661)
  ·
    refine ⟨1694551368619620131866937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18075214598609281406580661 1694551368619620131866937)
    ·
      refine ⟨1270913526464715098900203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1694551368619620131866937 1270913526464715098900203)
      ·
        refine ⟨1906370289697072648350305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1270913526464715098900203 1906370289697072648350305)
        ·
          refine ⟨1429777717272804486262729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1906370289697072648350305 1429777717272804486262729)
          ·
            refine ⟨1072333287954603364697047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1429777717272804486262729 1072333287954603364697047)
            ·
              refine ⟨1608499931931905047045571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1072333287954603364697047 1608499931931905047045571)
              ·
                refine ⟨2412749897897857570568357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1608499931931905047045571 2412749897897857570568357)
                ·
                  refine ⟨452390605855848294481567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2412749897897857570568357 452390605855848294481567)
                  ·
                    rfl

theorem cell20_991156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_991156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991156 prefixEnd_991156 := by exact prefixLift 991156
  have htrace : WordTrace (prefixWord ++ tailWord_991156) baseStart_991156 baseEnd_991156 := by
    simpa [prefixWord, tailWord_991156, baseEnd_991156] using wordTrace_append hprefix tailTrace_991156
  have hstable : (prefixWord ++ tailWord_991156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991156).length < 2 ^ (prefixWord ++ tailWord_991156).sum := by decide
  have hdescent : baseEnd_991156 < baseStart_991156 := by decide
  rcases family_descends (prefixWord ++ tailWord_991156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991188 : List Nat := [2, 4, 1, 2, 1, 1, 1, 8]
def baseStart_991188 : Nat := 118140960795 + 991188 * 2 ^ 59
def prefixEnd_991188 : Nat := 4983230072969 + 3 ^ 40 * 991188 * 2
def baseEnd_991188 : Nat := 150801737175932801804923

theorem tailTrace_991188 : CollatzResearch.WordTrace tailWord_991188 prefixEnd_991188 150801737175932801804923 := by
  unfold tailWord_991188
  simp only [CollatzResearch.WordTrace]
  refine ⟨18075798166551316139163109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24101064222068421518884145 18075798166551316139163109)
  ·
    refine ⟨3389212156228371776093083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18075798166551316139163109 3389212156228371776093083)
    ·
      refine ⟨5083818234342557664139625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3389212156228371776093083 5083818234342557664139625)
      ·
        refine ⟨3812863675756918248104719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5083818234342557664139625 3812863675756918248104719)
        ·
          refine ⟨5719295513635377372157079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3812863675756918248104719 5719295513635377372157079)
          ·
            refine ⟨8578943270453066058235619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5719295513635377372157079 8578943270453066058235619)
            ·
              refine ⟨12868414905679599087353429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8578943270453066058235619 12868414905679599087353429)
              ·
                refine ⟨150801737175932801804923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12868414905679599087353429 150801737175932801804923)
                ·
                  rfl

theorem cell20_991188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_991188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991188 prefixEnd_991188 := by exact prefixLift 991188
  have htrace : WordTrace (prefixWord ++ tailWord_991188) baseStart_991188 baseEnd_991188 := by
    simpa [prefixWord, tailWord_991188, baseEnd_991188] using wordTrace_append hprefix tailTrace_991188
  have hstable : (prefixWord ++ tailWord_991188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991188).length < 2 ^ (prefixWord ++ tailWord_991188).sum := by decide
  have hdescent : baseEnd_991188 < baseStart_991188 := by decide
  rcases family_descends (prefixWord ++ tailWord_991188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991222 : List Nat := [5, 1, 1, 1, 4, 2, 1, 5]
def baseStart_991222 : Nat := 118140960795 + 991222 * 2 ^ 59
def prefixEnd_991222 : Nat := 4983230072969 + 3 ^ 40 * 991222 * 2
def baseEnd_991222 : Nat := 150806910018081799427099

theorem tailTrace_991222 : CollatzResearch.WordTrace tailWord_991222 prefixEnd_991222 150806910018081799427099 := by
  unfold tailWord_991222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2259552275936216005316495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24101890943319637390042613 2259552275936216005316495)
  ·
    refine ⟨3389328413904324007974743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2259552275936216005316495 3389328413904324007974743)
    ·
      refine ⟨5083992620856486011962115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3389328413904324007974743 5083992620856486011962115)
      ·
        refine ⟨7625988931284729017943173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5083992620856486011962115 7625988931284729017943173)
        ·
          refine ⟨1429872924615886690864345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7625988931284729017943173 1429872924615886690864345)
          ·
            refine ⟨1072404693461915018148259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1429872924615886690864345 1072404693461915018148259)
            ·
              refine ⟨1608607040192872527222389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1072404693461915018148259 1608607040192872527222389)
              ·
                refine ⟨150806910018081799427099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1608607040192872527222389 150806910018081799427099)
                ·
                  rfl

theorem cell20_991222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_991222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991222 prefixEnd_991222 := by exact prefixLift 991222
  have htrace : WordTrace (prefixWord ++ tailWord_991222) baseStart_991222 baseEnd_991222 := by
    simpa [prefixWord, tailWord_991222, baseEnd_991222] using wordTrace_append hprefix tailTrace_991222
  have hstable : (prefixWord ++ tailWord_991222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991222).length < 2 ^ (prefixWord ++ tailWord_991222).sum := by decide
  have hdescent : baseEnd_991222 < baseStart_991222 := by decide
  rcases family_descends (prefixWord ++ tailWord_991222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991253 : List Nat := [1, 3, 2, 1, 5, 1, 2, 3, 2]
def baseStart_991253 : Nat := 118140960795 + 991253 * 2 ^ 59
def prefixEnd_991253 : Nat := 4983230072969 + 3 ^ 40 * 991253 * 2
def baseEnd_991253 : Nat := 452434879298947068247837

theorem tailTrace_991253 : CollatzResearch.WordTrace tailWord_991253 prefixEnd_991253 452434879298947068247837 := by
  unfold tailWord_991253
  simp only [CollatzResearch.WordTrace]
  refine ⟨36153967077867148379442413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24102644718578098919628275 36153967077867148379442413)
  ·
    refine ⟨13557737654200180642290905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36153967077867148379442413 13557737654200180642290905)
    ·
      refine ⟨10168303240650135481718179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13557737654200180642290905 10168303240650135481718179)
      ·
        refine ⟨15252454860975203222577269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10168303240650135481718179 15252454860975203222577269)
        ·
          refine ⟨1429917643216425302116619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15252454860975203222577269 1429917643216425302116619)
          ·
            refine ⟨2144876464824637953174929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429917643216425302116619 2144876464824637953174929)
            ·
              refine ⟨1608657348618478464881197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2144876464824637953174929 1608657348618478464881197)
              ·
                refine ⟨603246505731929424330449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1608657348618478464881197 603246505731929424330449)
                ·
                  refine ⟨452434879298947068247837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603246505731929424330449 452434879298947068247837)
                  ·
                    rfl

theorem cell20_991253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_991253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991253 prefixEnd_991253 := by exact prefixLift 991253
  have htrace : WordTrace (prefixWord ++ tailWord_991253) baseStart_991253 baseEnd_991253 := by
    simpa [prefixWord, tailWord_991253, baseEnd_991253] using wordTrace_append hprefix tailTrace_991253
  have hstable : (prefixWord ++ tailWord_991253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991253).length < 2 ^ (prefixWord ++ tailWord_991253).sum := by decide
  have hdescent : baseEnd_991253 < baseStart_991253 := by decide
  rcases family_descends (prefixWord ++ tailWord_991253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991274 : List Nat := [3, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_991274 : Nat := 118140960795 + 991274 * 2 ^ 59
def prefixEnd_991274 : Nat := 4983230072969 + 3 ^ 40 * 991274 * 2
def baseEnd_991274 : Nat := 452444464271164328547751

theorem tailTrace_991274 : CollatzResearch.WordTrace tailWord_991274 prefixEnd_991274 452444464271164328547751 := by
  unfold tailWord_991274
  simp only [CollatzResearch.WordTrace]
  refine ⟨9038683252697767241489219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24103155340527379310637917 9038683252697767241489219)
  ·
    refine ⟨13558024879046650862233829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9038683252697767241489219 13558024879046650862233829)
    ·
      refine ⟨2542129664821247036668843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13558024879046650862233829 2542129664821247036668843)
      ·
        refine ⟨3813194497231870555003265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2542129664821247036668843 3813194497231870555003265)
        ·
          refine ⟨2859895872923902916252449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3813194497231870555003265 2859895872923902916252449)
          ·
            refine ⟨2144921904692927187189337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2859895872923902916252449 2144921904692927187189337)
            ·
              refine ⟨1608691428519695390392003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2144921904692927187189337 1608691428519695390392003)
              ·
                refine ⟨2413037142779543085588005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1608691428519695390392003 2413037142779543085588005)
                ·
                  refine ⟨452444464271164328547751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2413037142779543085588005 452444464271164328547751)
                  ·
                    rfl

theorem cell20_991274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_991274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991274 prefixEnd_991274 := by exact prefixLift 991274
  have htrace : WordTrace (prefixWord ++ tailWord_991274) baseStart_991274 baseEnd_991274 := by
    simpa [prefixWord, tailWord_991274, baseEnd_991274] using wordTrace_append hprefix tailTrace_991274
  have hstable : (prefixWord ++ tailWord_991274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991274).length < 2 ^ (prefixWord ++ tailWord_991274).sum := by decide
  have hdescent : baseEnd_991274 < baseStart_991274 := by decide
  rcases family_descends (prefixWord ++ tailWord_991274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991333 : List Nat := [1, 3, 1, 3, 2, 2, 3, 1, 4]
def baseStart_991333 : Nat := 118140960795 + 991333 * 2 ^ 59
def prefixEnd_991333 : Nat := 4983230072969 + 3 ^ 40 * 991333 * 2
def baseEnd_991333 : Nat := 452471393478822345580843

theorem tailTrace_991333 : CollatzResearch.WordTrace tailWord_991333 prefixEnd_991333 452471393478822345580843 := by
  unfold tailWord_991333
  simp only [CollatzResearch.WordTrace]
  refine ⟨36156884917577322042354653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24104589945051548028236435 36156884917577322042354653)
  ·
    refine ⟨13558831844091495765882995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36156884917577322042354653 13558831844091495765882995)
    ·
      refine ⟨20338247766137243648824493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13558831844091495765882995 20338247766137243648824493)
      ·
        refine ⟨7626842912301466368309185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20338247766137243648824493 7626842912301466368309185)
        ·
          refine ⟨5720132184226099776231889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7626842912301466368309185 5720132184226099776231889)
          ·
            refine ⟨4290099138169574832173917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5720132184226099776231889 4290099138169574832173917)
            ·
              refine ⟨1608787176813590562065219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4290099138169574832173917 1608787176813590562065219)
              ·
                refine ⟨2413180765220385843097829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1608787176813590562065219 2413180765220385843097829)
                ·
                  refine ⟨452471393478822345580843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2413180765220385843097829 452471393478822345580843)
                  ·
                    rfl

theorem cell20_991333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_991333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991333 prefixEnd_991333 := by exact prefixLift 991333
  have htrace : WordTrace (prefixWord ++ tailWord_991333) baseStart_991333 baseEnd_991333 := by
    simpa [prefixWord, tailWord_991333, baseEnd_991333] using wordTrace_append hprefix tailTrace_991333
  have hstable : (prefixWord ++ tailWord_991333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991333).length < 2 ^ (prefixWord ++ tailWord_991333).sum := by decide
  have hdescent : baseEnd_991333 < baseStart_991333 := by decide
  rcases family_descends (prefixWord ++ tailWord_991333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991340 : List Nat := [2, 2, 1, 1, 3, 4, 2, 5]
def baseStart_991340 : Nat := 118140960795 + 991340 * 2 ^ 59
def prefixEnd_991340 : Nat := 4983230072969 + 3 ^ 40 * 991340 * 2
def baseEnd_991340 : Nat := 150824862823187144115827

theorem tailTrace_991340 : CollatzResearch.WordTrace tailWord_991340 prefixEnd_991340 150824862823187144115827 := by
  unfold tailWord_991340
  simp only [CollatzResearch.WordTrace]
  refine ⟨18078570114275981118929737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24104760152367974825239649 18078570114275981118929737)
  ·
    refine ⟨13558927585706985839197303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18078570114275981118929737 13558927585706985839197303)
    ·
      refine ⟨20338391378560478758795955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13558927585706985839197303 20338391378560478758795955)
      ·
        refine ⟨30507587067840718138193933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20338391378560478758795955 30507587067840718138193933)
        ·
          refine ⟨11440345150440269301822725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30507587067840718138193933 11440345150440269301822725)
          ·
            refine ⟨2145064715707550494091761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11440345150440269301822725 2145064715707550494091761)
            ·
              refine ⟨1608798536780662870568821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2145064715707550494091761 1608798536780662870568821)
              ·
                refine ⟨150824862823187144115827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1608798536780662870568821 150824862823187144115827)
                ·
                  rfl

theorem cell20_991340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_991340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991340 prefixEnd_991340 := by exact prefixLift 991340
  have htrace : WordTrace (prefixWord ++ tailWord_991340) baseStart_991340 baseEnd_991340 := by
    simpa [prefixWord, tailWord_991340, baseEnd_991340] using wordTrace_append hprefix tailTrace_991340
  have hstable : (prefixWord ++ tailWord_991340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991340).length < 2 ^ (prefixWord ++ tailWord_991340).sum := by decide
  have hdescent : baseEnd_991340 < baseStart_991340 := by decide
  rcases family_descends (prefixWord ++ tailWord_991340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991343 : List Nat := [1, 1, 2, 1, 3, 6, 2, 1, 3]
def baseStart_991343 : Nat := 118140960795 + 991343 * 2 ^ 59
def prefixEnd_991343 : Nat := 4983230072969 + 3 ^ 40 * 991343 * 2
def baseEnd_991343 : Nat := 452475957751306755247469

theorem tailTrace_991343 : CollatzResearch.WordTrace tailWord_991343 prefixEnd_991343 452475957751306755247469 := by
  unfold tailWord_991343
  simp only [CollatzResearch.WordTrace]
  refine ⟨36157249647541093750218683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24104833098360729166812455 36157249647541093750218683)
  ·
    refine ⟨54235874471311640625328025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36157249647541093750218683 54235874471311640625328025)
    ·
      refine ⟨40676905853483730468996019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54235874471311640625328025 40676905853483730468996019)
      ·
        refine ⟨61015358780225595703494029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40676905853483730468996019 61015358780225595703494029)
        ·
          refine ⟨22880759542584598388810261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61015358780225595703494029 22880759542584598388810261)
          ·
            refine ⟨1072535603558653049475481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22880759542584598388810261 1072535603558653049475481)
            ·
              refine ⟨804401702668989787106611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072535603558653049475481 804401702668989787106611)
              ·
                refine ⟨1206602554003484680659917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804401702668989787106611 1206602554003484680659917)
                ·
                  refine ⟨452475957751306755247469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1206602554003484680659917 452475957751306755247469)
                  ·
                    rfl

theorem cell20_991343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 3].length) (baseStart_991343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991343 prefixEnd_991343 := by exact prefixLift 991343
  have htrace : WordTrace (prefixWord ++ tailWord_991343) baseStart_991343 baseEnd_991343 := by
    simpa [prefixWord, tailWord_991343, baseEnd_991343] using wordTrace_append hprefix tailTrace_991343
  have hstable : (prefixWord ++ tailWord_991343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991343).length < 2 ^ (prefixWord ++ tailWord_991343).sum := by decide
  have hdescent : baseEnd_991343 < baseStart_991343 := by decide
  rcases family_descends (prefixWord ++ tailWord_991343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991380 : List Nat := [2, 4, 2, 3, 2, 1, 2, 2, 2]
def baseStart_991380 : Nat := 118140960795 + 991380 * 2 ^ 59
def prefixEnd_991380 : Nat := 4983230072969 + 3 ^ 40 * 991380 * 2
def baseEnd_991380 : Nat := 452492845559499071013985

theorem tailTrace_991380 : CollatzResearch.WordTrace tailWord_991380 prefixEnd_991380 452492845559499071013985 := by
  unfold tailWord_991380
  simp only [CollatzResearch.WordTrace]
  refine ⟨18079299574203524534657797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24105732765604699379543729 18079299574203524534657797)
  ·
    refine ⟨3389868670163160850248337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18079299574203524534657797 3389868670163160850248337)
    ·
      refine ⟨2542401502622370637686253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3389868670163160850248337 2542401502622370637686253)
      ·
        refine ⟨953400563483388989132345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2542401502622370637686253 953400563483388989132345)
        ·
          refine ⟨715050422612541741849259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 953400563483388989132345 715050422612541741849259)
          ·
            refine ⟨1072575633918812612773889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715050422612541741849259 1072575633918812612773889)
            ·
              refine ⟨804431725439109459580417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072575633918812612773889 804431725439109459580417)
              ·
                refine ⟨603323794079332094685313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 804431725439109459580417 603323794079332094685313)
                ·
                  refine ⟨452492845559499071013985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603323794079332094685313 452492845559499071013985)
                  ·
                    rfl

theorem cell20_991380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_991380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991380 prefixEnd_991380 := by exact prefixLift 991380
  have htrace : WordTrace (prefixWord ++ tailWord_991380) baseStart_991380 baseEnd_991380 := by
    simpa [prefixWord, tailWord_991380, baseEnd_991380] using wordTrace_append hprefix tailTrace_991380
  have hstable : (prefixWord ++ tailWord_991380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991380).length < 2 ^ (prefixWord ++ tailWord_991380).sum := by decide
  have hdescent : baseEnd_991380 < baseStart_991380 := by decide
  rcases family_descends (prefixWord ++ tailWord_991380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991384 : List Nat := [2, 1, 2, 4, 3, 2, 2, 2, 2]
def baseStart_991384 : Nat := 118140960795 + 991384 * 2 ^ 59
def prefixEnd_991384 : Nat := 4983230072969 + 3 ^ 40 * 991384 * 2
def baseEnd_991384 : Nat := 452494671268492834880635

theorem tailTrace_991384 : CollatzResearch.WordTrace tailWord_991384 prefixEnd_991384 452494671268492834880635 := by
  unfold tailWord_991384
  simp only [CollatzResearch.WordTrace]
  refine ⟨18079372520196278876230603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24105830026928371834974137 18079372520196278876230603)
  ·
    refine ⟨27119058780294418314345905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18079372520196278876230603 27119058780294418314345905)
    ·
      refine ⟨20339294085220813735759429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27119058780294418314345905 20339294085220813735759429)
      ·
        refine ⟨3813617640978902575454893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20339294085220813735759429 3813617640978902575454893)
        ·
          refine ⟨1430106615367088465795585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3813617640978902575454893 1430106615367088465795585)
          ·
            refine ⟨1072579961525316349346689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1430106615367088465795585 1072579961525316349346689)
            ·
              refine ⟨804434971143987262010017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072579961525316349346689 804434971143987262010017)
              ·
                refine ⟨603326228357990446507513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 804434971143987262010017 603326228357990446507513)
                ·
                  refine ⟨452494671268492834880635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603326228357990446507513 452494671268492834880635)
                  ·
                    rfl

theorem cell20_991384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 2].length) (baseStart_991384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991384 prefixEnd_991384 := by exact prefixLift 991384
  have htrace : WordTrace (prefixWord ++ tailWord_991384) baseStart_991384 baseEnd_991384 := by
    simpa [prefixWord, tailWord_991384, baseEnd_991384] using wordTrace_append hprefix tailTrace_991384
  have hstable : (prefixWord ++ tailWord_991384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991384).length < 2 ^ (prefixWord ++ tailWord_991384).sum := by decide
  have hdescent : baseEnd_991384 < baseStart_991384 := by decide
  rcases family_descends (prefixWord ++ tailWord_991384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991388 : List Nat := [2, 2, 3, 2, 1, 1, 3, 4, 2]
def baseStart_991388 : Nat := 118140960795 + 991388 * 2 ^ 59
def prefixEnd_991388 : Nat := 4983230072969 + 3 ^ 40 * 991388 * 2
def baseEnd_991388 : Nat := 452496496977486598747285

theorem tailTrace_991388 : CollatzResearch.WordTrace tailWord_991388 prefixEnd_991388 452496496977486598747285 := by
  unfold tailWord_991388
  simp only [CollatzResearch.WordTrace]
  refine ⟨18079445466189033217803409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24105927288252044290404545 18079445466189033217803409)
  ·
    refine ⟨13559584099641774913352557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18079445466189033217803409 13559584099641774913352557)
    ·
      refine ⟨5084844037365665592507209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13559584099641774913352557 5084844037365665592507209)
      ·
        refine ⟨3813633028024249194380407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5084844037365665592507209 3813633028024249194380407)
        ·
          refine ⟨5720449542036373791570611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3813633028024249194380407 5720449542036373791570611)
          ·
            refine ⟨8580674313054560687355917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5720449542036373791570611 8580674313054560687355917)
            ·
              refine ⟨3217752867395460257758469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8580674313054560687355917 3217752867395460257758469)
              ·
                refine ⟨603328662636648798329713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3217752867395460257758469 603328662636648798329713)
                ·
                  refine ⟨452496496977486598747285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603328662636648798329713 452496496977486598747285)
                  ·
                    rfl

theorem cell20_991388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_991388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991388 prefixEnd_991388 := by exact prefixLift 991388
  have htrace : WordTrace (prefixWord ++ tailWord_991388) baseStart_991388 baseEnd_991388 := by
    simpa [prefixWord, tailWord_991388, baseEnd_991388] using wordTrace_append hprefix tailTrace_991388
  have hstable : (prefixWord ++ tailWord_991388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991388).length < 2 ^ (prefixWord ++ tailWord_991388).sum := by decide
  have hdescent : baseEnd_991388 < baseStart_991388 := by decide
  rcases family_descends (prefixWord ++ tailWord_991388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991416 : List Nat := [2, 1, 2, 1, 2, 1, 7, 4]
def baseStart_991416 : Nat := 118140960795 + 991416 * 2 ^ 59
def prefixEnd_991416 : Nat := 4983230072969 + 3 ^ 40 * 991416 * 2
def baseEnd_991416 : Nat := 150836425646814315271279

theorem tailTrace_991416 : CollatzResearch.WordTrace tailWord_991416 prefixEnd_991416 150836425646814315271279 := by
  unfold tailWord_991416
  simp only [CollatzResearch.WordTrace]
  refine ⟨18079956088138313608813051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24106608117517751478417401 18079956088138313608813051)
  ·
    refine ⟨27119934132207470413219577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18079956088138313608813051 27119934132207470413219577)
    ·
      refine ⟨20339950599155602809914683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27119934132207470413219577 20339950599155602809914683)
      ·
        refine ⟨30509925898733404214872025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20339950599155602809914683 30509925898733404214872025)
        ·
          refine ⟨22882444424050053161154019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30509925898733404214872025 22882444424050053161154019)
          ·
            refine ⟨34323666636075079741731029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22882444424050053161154019 34323666636075079741731029)
            ·
              refine ⟨804460936783009681446821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 34323666636075079741731029 804460936783009681446821)
              ·
                refine ⟨150836425646814315271279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 804460936783009681446821 150836425646814315271279)
                ·
                  rfl

theorem cell20_991416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_991416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991416 prefixEnd_991416 := by exact prefixLift 991416
  have htrace : WordTrace (prefixWord ++ tailWord_991416) baseStart_991416 baseEnd_991416 := by
    simpa [prefixWord, tailWord_991416, baseEnd_991416] using wordTrace_append hprefix tailTrace_991416
  have hstable : (prefixWord ++ tailWord_991416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991416).length < 2 ^ (prefixWord ++ tailWord_991416).sum := by decide
  have hdescent : baseEnd_991416 < baseStart_991416 := by decide
  rcases family_descends (prefixWord ++ tailWord_991416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991436 : List Nat := [2, 2, 1, 6, 1, 2, 1, 2, 3]
def baseStart_991436 : Nat := 118140960795 + 991436 * 2 ^ 59
def prefixEnd_991436 : Nat := 4983230072969 + 3 ^ 40 * 991436 * 2
def baseEnd_991436 : Nat := 452518405485411765147089

theorem tailTrace_991436 : CollatzResearch.WordTrace tailWord_991436 prefixEnd_991436 452518405485411765147089 := by
  unfold tailWord_991436
  simp only [CollatzResearch.WordTrace]
  refine ⟨18080320818102085316677081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24107094424136113755569441 18080320818102085316677081)
  ·
    refine ⟨13560240613576563987507811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18080320818102085316677081 13560240613576563987507811)
    ·
      refine ⟨20340360920364845981261717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13560240613576563987507811 20340360920364845981261717)
      ·
        refine ⟨953454418142102155371643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20340360920364845981261717 953454418142102155371643)
        ·
          refine ⟨1430181627213153233057465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953454418142102155371643 1430181627213153233057465)
          ·
            refine ⟨1072636220409864924793099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1430181627213153233057465 1072636220409864924793099)
            ·
              refine ⟨1608954330614797387189649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1072636220409864924793099 1608954330614797387189649)
              ·
                refine ⟨1206715747961098040392237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1608954330614797387189649 1206715747961098040392237)
                ·
                  refine ⟨452518405485411765147089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1206715747961098040392237 452518405485411765147089)
                  ·
                    rfl

theorem cell20_991436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_991436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991436 prefixEnd_991436 := by exact prefixLift 991436
  have htrace : WordTrace (prefixWord ++ tailWord_991436) baseStart_991436 baseEnd_991436 := by
    simpa [prefixWord, tailWord_991436, baseEnd_991436] using wordTrace_append hprefix tailTrace_991436
  have hstable : (prefixWord ++ tailWord_991436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991436).length < 2 ^ (prefixWord ++ tailWord_991436).sum := by decide
  have hdescent : baseEnd_991436 < baseStart_991436 := by decide
  rcases family_descends (prefixWord ++ tailWord_991436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991468 : List Nat := [2, 2, 1, 1, 2, 3, 1, 4, 4]
def baseStart_991468 : Nat := 118140960795 + 991468 * 2 ^ 59
def prefixEnd_991468 : Nat := 4983230072969 + 3 ^ 40 * 991468 * 2
def baseEnd_991468 : Nat := 452533011157361876080291

theorem tailTrace_991468 : CollatzResearch.WordTrace tailWord_991468 prefixEnd_991468 452533011157361876080291 := by
  unfold tailWord_991468
  simp only [CollatzResearch.WordTrace]
  refine ⟨18080904386044120049259529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24107872514725493399012705 18080904386044120049259529)
  ·
    refine ⟨13560678289533090036944647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18080904386044120049259529 13560678289533090036944647)
    ·
      refine ⟨20341017434299635055416971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13560678289533090036944647 20341017434299635055416971)
      ·
        refine ⟨30511526151449452583125457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20341017434299635055416971 30511526151449452583125457)
        ·
          refine ⟨22883644613587089437344093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30511526151449452583125457 22883644613587089437344093)
          ·
            refine ⟨8581366730095158539004035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22883644613587089437344093 8581366730095158539004035)
            ·
              refine ⟨12872050095142737808506053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8581366730095158539004035 12872050095142737808506053)
              ·
                refine ⟨2413509392839263339094885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12872050095142737808506053 2413509392839263339094885)
                ·
                  refine ⟨452533011157361876080291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2413509392839263339094885 452533011157361876080291)
                  ·
                    rfl

theorem cell20_991468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_991468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991468 prefixEnd_991468 := by exact prefixLift 991468
  have htrace : WordTrace (prefixWord ++ tailWord_991468) baseStart_991468 baseEnd_991468 := by
    simpa [prefixWord, tailWord_991468, baseEnd_991468] using wordTrace_append hprefix tailTrace_991468
  have hstable : (prefixWord ++ tailWord_991468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991468).length < 2 ^ (prefixWord ++ tailWord_991468).sum := by decide
  have hdescent : baseEnd_991468 < baseStart_991468 := by decide
  rcases family_descends (prefixWord ++ tailWord_991468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991471 : List Nat := [1, 1, 2, 1, 6, 3, 2, 4]
def baseStart_991471 : Nat := 118140960795 + 991471 * 2 ^ 59
def prefixEnd_991471 : Nat := 4983230072969 + 3 ^ 40 * 991471 * 2
def baseEnd_991471 : Nat := 150844793479702399660093

theorem tailTrace_991471 : CollatzResearch.WordTrace tailWord_991471 prefixEnd_991471 150844793479702399660093 := by
  unfold tailWord_991471
  simp only [CollatzResearch.WordTrace]
  refine ⟨36161918191077371610878267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24107945460718247740585511 36161918191077371610878267)
  ·
    refine ⟨54242877286616057416317401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36161918191077371610878267 54242877286616057416317401)
    ·
      refine ⟨40682157964962043062238051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54242877286616057416317401 40682157964962043062238051)
      ·
        refine ⟨61023236947443064593357077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40682157964962043062238051 61023236947443064593357077)
        ·
          refine ⟨2860464231911393652813613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61023236947443064593357077 2860464231911393652813613)
          ·
            refine ⟨1072674086966772619805105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2860464231911393652813613 1072674086966772619805105)
            ·
              refine ⟨804505565225079464853829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072674086966772619805105 804505565225079464853829)
              ·
                refine ⟨150844793479702399660093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 804505565225079464853829 150844793479702399660093)
                ·
                  rfl

theorem cell20_991471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 4].length) (baseStart_991471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991471 prefixEnd_991471 := by exact prefixLift 991471
  have htrace : WordTrace (prefixWord ++ tailWord_991471) baseStart_991471 baseEnd_991471 := by
    simpa [prefixWord, tailWord_991471, baseEnd_991471] using wordTrace_append hprefix tailTrace_991471
  have hstable : (prefixWord ++ tailWord_991471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991471).length < 2 ^ (prefixWord ++ tailWord_991471).sum := by decide
  have hdescent : baseEnd_991471 < baseStart_991471 := by decide
  rcases family_descends (prefixWord ++ tailWord_991471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991475 : List Nat := [1, 1, 1, 2, 2, 4, 3, 6]
def baseStart_991475 : Nat := 118140960795 + 991475 * 2 ^ 59
def prefixEnd_991475 : Nat := 4983230072969 + 3 ^ 40 * 991475 * 2
def baseEnd_991475 : Nat := 150845402049366987615643

theorem tailTrace_991475 : CollatzResearch.WordTrace tailWord_991475 prefixEnd_991475 150845402049366987615643 := by
  unfold tailWord_991475
  simp only [CollatzResearch.WordTrace]
  refine ⟨36162064083062880294023879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24108042722041920196015919 36162064083062880294023879)
  ·
    refine ⟨54243096124594320441035819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36162064083062880294023879 54243096124594320441035819)
    ·
      refine ⟨81364644186891480661553729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54243096124594320441035819 81364644186891480661553729)
      ·
        refine ⟨61023483140168610496165297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81364644186891480661553729 61023483140168610496165297)
        ·
          refine ⟨45767612355126457872123973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61023483140168610496165297 45767612355126457872123973)
          ·
            refine ⟨8581427316586210851023245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45767612355126457872123973 8581427316586210851023245)
            ·
              refine ⟨3218035243719829069133717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8581427316586210851023245 3218035243719829069133717)
              ·
                refine ⟨150845402049366987615643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3218035243719829069133717 150845402049366987615643)
                ·
                  rfl

theorem cell20_991475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 6].length) (baseStart_991475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991475 prefixEnd_991475 := by exact prefixLift 991475
  have htrace : WordTrace (prefixWord ++ tailWord_991475) baseStart_991475 baseEnd_991475 := by
    simpa [prefixWord, tailWord_991475, baseEnd_991475] using wordTrace_append hprefix tailTrace_991475
  have hstable : (prefixWord ++ tailWord_991475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991475).length < 2 ^ (prefixWord ++ tailWord_991475).sum := by decide
  have hdescent : baseEnd_991475 < baseStart_991475 := by decide
  rcases family_descends (prefixWord ++ tailWord_991475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991499 : List Nat := [1, 1, 1, 1, 5, 2, 2, 4, 3]
def baseStart_991499 : Nat := 118140960795 + 991499 * 2 ^ 59
def prefixEnd_991499 : Nat := 4983230072969 + 3 ^ 40 * 991499 * 2
def baseEnd_991499 : Nat := 452547160402063546046831

theorem tailTrace_991499 : CollatzResearch.WordTrace tailWord_991499 prefixEnd_991499 452547160402063546046831 := by
  unfold tailWord_991499
  simp only [CollatzResearch.WordTrace]
  refine ⟨36162939434975932392897551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24108626289983954928598367 36162939434975932392897551)
  ·
    refine ⟨54244409152463898589346327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36162939434975932392897551 54244409152463898589346327)
    ·
      refine ⟨81366613728695847884019491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54244409152463898589346327 81366613728695847884019491)
      ·
        refine ⟨122049920593043771826029237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81366613728695847884019491 122049920593043771826029237)
        ·
          refine ⟨11442180055597853608690241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122049920593043771826029237 11442180055597853608690241)
          ·
            refine ⟨8581635041698390206517681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11442180055597853608690241 8581635041698390206517681)
            ·
              refine ⟨6436226281273792654888261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8581635041698390206517681 6436226281273792654888261)
              ·
                refine ⟨1206792427738836122791549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6436226281273792654888261 1206792427738836122791549)
                ·
                  refine ⟨452547160402063546046831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1206792427738836122791549 452547160402063546046831)
                  ·
                    rfl

theorem cell20_991499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 3].length) (baseStart_991499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991499 prefixEnd_991499 := by exact prefixLift 991499
  have htrace : WordTrace (prefixWord ++ tailWord_991499) baseStart_991499 baseEnd_991499 := by
    simpa [prefixWord, tailWord_991499, baseEnd_991499] using wordTrace_append hprefix tailTrace_991499
  have hstable : (prefixWord ++ tailWord_991499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991499).length < 2 ^ (prefixWord ++ tailWord_991499).sum := by decide
  have hdescent : baseEnd_991499 < baseStart_991499 := by decide
  rcases family_descends (prefixWord ++ tailWord_991499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991553 : List Nat := [1, 2, 5, 2, 3, 1, 2, 2, 2]
def baseStart_991553 : Nat := 118140960795 + 991553 * 2 ^ 59
def prefixEnd_991553 : Nat := 4983230072969 + 3 ^ 40 * 991553 * 2
def baseEnd_991553 : Nat := 452571807473479358246611

theorem tailTrace_991553 : CollatzResearch.WordTrace tailWord_991553 prefixEnd_991553 452571807473479358246611 := by
  unfold tailWord_991553
  simp only [CollatzResearch.WordTrace]
  refine ⟨36164908976780299615363313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24109939317853533076908875 36164908976780299615363313)
  ·
    refine ⟨27123681732585224711522485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36164908976780299615363313 27123681732585224711522485)
    ·
      refine ⟨2542845162429864816705233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27123681732585224711522485 2542845162429864816705233)
      ·
        refine ⟨1907133871822398612528925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2542845162429864816705233 1907133871822398612528925)
        ·
          refine ⟨715175201933399479698347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1907133871822398612528925 715175201933399479698347)
          ·
            refine ⟨1072762802900099219547521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715175201933399479698347 1072762802900099219547521)
            ·
              refine ⟨804572102175074414660641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072762802900099219547521 804572102175074414660641)
              ·
                refine ⟨603429076631305810995481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 804572102175074414660641 603429076631305810995481)
                ·
                  refine ⟨452571807473479358246611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603429076631305810995481 452571807473479358246611)
                  ·
                    rfl

theorem cell20_991553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 2].length) (baseStart_991553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991553 prefixEnd_991553 := by exact prefixLift 991553
  have htrace : WordTrace (prefixWord ++ tailWord_991553) baseStart_991553 baseEnd_991553 := by
    simpa [prefixWord, tailWord_991553, baseEnd_991553] using wordTrace_append hprefix tailTrace_991553
  have hstable : (prefixWord ++ tailWord_991553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991553).length < 2 ^ (prefixWord ++ tailWord_991553).sum := by decide
  have hdescent : baseEnd_991553 < baseStart_991553 := by decide
  rcases family_descends (prefixWord ++ tailWord_991553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991568 : List Nat := [2, 1, 1, 1, 1, 8, 1, 5]
def baseStart_991568 : Nat := 118140960795 + 991568 * 2 ^ 59
def prefixEnd_991568 : Nat := 4983230072969 + 3 ^ 40 * 991568 * 2
def baseEnd_991568 : Nat := 150859551294068657582183

theorem tailTrace_991568 : CollatzResearch.WordTrace tailWord_991568 prefixEnd_991568 150859551294068657582183 := by
  unfold tailWord_991568
  simp only [CollatzResearch.WordTrace]
  refine ⟨18082728035862978588579679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24110304047817304784772905 18082728035862978588579679)
  ·
    refine ⟨27124092053794467882869519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18082728035862978588579679 27124092053794467882869519)
    ·
      refine ⟨40686138080691701824304279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27124092053794467882869519 40686138080691701824304279)
      ·
        refine ⟨61029207121037552736456419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40686138080691701824304279 61029207121037552736456419)
        ·
          refine ⟨91543810681556329104684629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61029207121037552736456419 91543810681556329104684629)
          ·
            refine ⟨1072779031424488231695523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 91543810681556329104684629 1072779031424488231695523)
            ·
              refine ⟨1609168547136732347543285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1072779031424488231695523 1609168547136732347543285)
              ·
                refine ⟨150859551294068657582183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1609168547136732347543285 150859551294068657582183)
                ·
                  rfl

theorem cell20_991568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_991568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991568 prefixEnd_991568 := by exact prefixLift 991568
  have htrace : WordTrace (prefixWord ++ tailWord_991568) baseStart_991568 baseEnd_991568 := by
    simpa [prefixWord, tailWord_991568, baseEnd_991568] using wordTrace_append hprefix tailTrace_991568
  have hstable : (prefixWord ++ tailWord_991568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991568).length < 2 ^ (prefixWord ++ tailWord_991568).sum := by decide
  have hdescent : baseEnd_991568 < baseStart_991568 := by decide
  rcases family_descends (prefixWord ++ tailWord_991568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991575 : List Nat := [1, 1, 3, 2, 3, 1, 1, 5, 3]
def baseStart_991575 : Nat := 118140960795 + 991575 * 2 ^ 59
def prefixEnd_991575 : Nat := 4983230072969 + 3 ^ 40 * 991575 * 2
def baseEnd_991575 : Nat := 452581848872945059513187

theorem tailTrace_991575 : CollatzResearch.WordTrace tailWord_991575 prefixEnd_991575 452581848872945059513187 := by
  unfold tailWord_991575
  simp only [CollatzResearch.WordTrace]
  refine ⟨36165711382700597372664179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24110474255133731581776119 36165711382700597372664179)
  ·
    refine ⟨54248567074050896058996269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36165711382700597372664179 54248567074050896058996269)
    ·
      refine ⟨20343212652769086022123601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54248567074050896058996269 20343212652769086022123601)
      ·
        refine ⟨15257409489576814516592701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20343212652769086022123601 15257409489576814516592701)
        ·
          refine ⟨5721528558591305443722263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15257409489576814516592701 5721528558591305443722263)
          ·
            refine ⟨8582292837886958165583395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5721528558591305443722263 8582292837886958165583395)
            ·
              refine ⟨12873439256830437248375093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8582292837886958165583395 12873439256830437248375093)
              ·
                refine ⟨1206884930327853492035165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12873439256830437248375093 1206884930327853492035165)
                ·
                  refine ⟨452581848872945059513187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1206884930327853492035165 452581848872945059513187)
                  ·
                    rfl

theorem cell20_991575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 3].length) (baseStart_991575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991575 prefixEnd_991575 := by exact prefixLift 991575
  have htrace : WordTrace (prefixWord ++ tailWord_991575) baseStart_991575 baseEnd_991575 := by
    simpa [prefixWord, tailWord_991575, baseEnd_991575] using wordTrace_append hprefix tailTrace_991575
  have hstable : (prefixWord ++ tailWord_991575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991575).length < 2 ^ (prefixWord ++ tailWord_991575).sum := by decide
  have hdescent : baseEnd_991575 < baseStart_991575 := by decide
  rcases family_descends (prefixWord ++ tailWord_991575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991613 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 5]
def baseStart_991613 : Nat := 118140960795 + 991613 * 2 ^ 59
def prefixEnd_991613 : Nat := 4983230072969 + 3 ^ 40 * 991613 * 2
def baseEnd_991613 : Nat := 452599193108385816246365

theorem tailTrace_991613 : CollatzResearch.WordTrace tailWord_991613 prefixEnd_991613 452599193108385816246365 := by
  unfold tailWord_991613
  simp only [CollatzResearch.WordTrace]
  refine ⟨36167097356562929862547493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24111398237708619908364995 36167097356562929862547493)
  ·
    refine ⟨6781330754355549349227655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36167097356562929862547493 6781330754355549349227655)
    ·
      refine ⟨10171996131533324023841483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6781330754355549349227655 10171996131533324023841483)
      ·
        refine ⟨15257994197299986035762225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10171996131533324023841483 15257994197299986035762225)
        ·
          refine ⟨11443495647974989526821669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15257994197299986035762225 11443495647974989526821669)
          ·
            refine ⟨2145655433995310536279063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11443495647974989526821669 2145655433995310536279063)
            ·
              refine ⟨3218483150992965804418595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2145655433995310536279063 3218483150992965804418595)
              ·
                refine ⟨4827724726489448706627893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3218483150992965804418595 4827724726489448706627893)
                ·
                  refine ⟨452599193108385816246365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4827724726489448706627893 452599193108385816246365)
                  ·
                    rfl

theorem cell20_991613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_991613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991613 prefixEnd_991613 := by exact prefixLift 991613
  have htrace : WordTrace (prefixWord ++ tailWord_991613) baseStart_991613 baseEnd_991613 := by
    simpa [prefixWord, tailWord_991613, baseEnd_991613] using wordTrace_append hprefix tailTrace_991613
  have hstable : (prefixWord ++ tailWord_991613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991613).length < 2 ^ (prefixWord ++ tailWord_991613).sum := by decide
  have hdescent : baseEnd_991613 < baseStart_991613 := by decide
  rcases family_descends (prefixWord ++ tailWord_991613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991626 : List Nat := [3, 1, 2, 5, 1, 1, 3, 1, 3]
def baseStart_991626 : Nat := 118140960795 + 991626 * 2 ^ 59
def prefixEnd_991626 : Nat := 4983230072969 + 3 ^ 40 * 991626 * 2
def baseEnd_991626 : Nat := 452605126662615548812979

theorem tailTrace_991626 : CollatzResearch.WordTrace tailWord_991626 prefixEnd_991626 452605126662615548812979 := by
  unfold tailWord_991626
  simp only [CollatzResearch.WordTrace]
  refine ⟨9041892876378958270692683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24111714337010555388513821 9041892876378958270692683)
  ·
    refine ⟨13562839314568437406039025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9041892876378958270692683 13562839314568437406039025)
    ·
      refine ⟨10172129485926328054529269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13562839314568437406039025 10172129485926328054529269)
      ·
        refine ⟨953637139305593255112119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10172129485926328054529269 953637139305593255112119)
        ·
          refine ⟨1430455708958389882668179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953637139305593255112119 1430455708958389882668179)
          ·
            refine ⟨2145683563437584824002269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430455708958389882668179 2145683563437584824002269)
            ·
              refine ⟨804631336289094309000851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2145683563437584824002269 804631336289094309000851)
              ·
                refine ⟨1206947004433641463501277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804631336289094309000851 1206947004433641463501277)
                ·
                  refine ⟨452605126662615548812979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1206947004433641463501277 452605126662615548812979)
                  ·
                    rfl

theorem cell20_991626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_991626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991626 prefixEnd_991626 := by exact prefixLift 991626
  have htrace : WordTrace (prefixWord ++ tailWord_991626) baseStart_991626 baseEnd_991626 := by
    simpa [prefixWord, tailWord_991626, baseEnd_991626] using wordTrace_append hprefix tailTrace_991626
  have hstable : (prefixWord ++ tailWord_991626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991626).length < 2 ^ (prefixWord ++ tailWord_991626).sum := by decide
  have hdescent : baseEnd_991626 < baseStart_991626 := by decide
  rcases family_descends (prefixWord ++ tailWord_991626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991661 : List Nat := [1, 5, 2, 2, 2, 2, 6]
def baseStart_991661 : Nat := 118140960795 + 991661 * 2 ^ 59
def prefixEnd_991661 : Nat := 4983230072969 + 3 ^ 40 * 991661 * 2
def baseEnd_991661 : Nat := 50291233512923442516241

theorem tailTrace_991661 : CollatzResearch.WordTrace tailWord_991661 prefixEnd_991661 50291233512923442516241 := by
  unfold tailWord_991661
  simp only [CollatzResearch.WordTrace]
  refine ⟨36168848060389034060294837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24112565373592689373529891 36168848060389034060294837)
  ·
    refine ⟨3390829505661471943152641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36168848060389034060294837 3390829505661471943152641)
    ·
      refine ⟨2543122129246103957364481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3390829505661471943152641 2543122129246103957364481)
      ·
        refine ⟨1907341596934577968023361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2543122129246103957364481 1907341596934577968023361)
        ·
          refine ⟨1430506197700933476017521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1907341596934577968023361 1430506197700933476017521)
          ·
            refine ⟨1072879648275700107013141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1430506197700933476017521 1072879648275700107013141)
            ·
              refine ⟨50291233512923442516241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1072879648275700107013141 50291233512923442516241)
              ·
                rfl

theorem cell20_991661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 6].length) (baseStart_991661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991661 prefixEnd_991661 := by exact prefixLift 991661
  have htrace : WordTrace (prefixWord ++ tailWord_991661) baseStart_991661 baseEnd_991661 := by
    simpa [prefixWord, tailWord_991661, baseEnd_991661] using wordTrace_append hprefix tailTrace_991661
  have hstable : (prefixWord ++ tailWord_991661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991661).length < 2 ^ (prefixWord ++ tailWord_991661).sum := by decide
  have hdescent : baseEnd_991661 < baseStart_991661 := by decide
  rcases family_descends (prefixWord ++ tailWord_991661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991665 : List Nat := [1, 2, 2, 4, 1, 2, 8]
def baseStart_991665 : Nat := 118140960795 + 991665 * 2 ^ 59
def prefixEnd_991665 : Nat := 4983230072969 + 3 ^ 40 * 991665 * 2
def baseEnd_991665 : Nat := 50291436369478305168091

theorem tailTrace_991665 : CollatzResearch.WordTrace tailWord_991665 prefixEnd_991665 50291436369478305168091 := by
  unfold tailWord_991665
  simp only [CollatzResearch.WordTrace]
  refine ⟨36168993952374542743440449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24112662634916361828960299 36168993952374542743440449)
  ·
    refine ⟨27126745464280907057580337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36168993952374542743440449 27126745464280907057580337)
    ·
      refine ⟨20345059098210680293185253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27126745464280907057580337 20345059098210680293185253)
      ·
        refine ⟨3814698580914502554972235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20345059098210680293185253 3814698580914502554972235)
        ·
          refine ⟨5722047871371753832458353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3814698580914502554972235 5722047871371753832458353)
          ·
            refine ⟨4291535903528815374343765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5722047871371753832458353 4291535903528815374343765)
            ·
              refine ⟨50291436369478305168091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4291535903528815374343765 50291436369478305168091)
              ·
                rfl

theorem cell20_991665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 8].length) (baseStart_991665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991665 prefixEnd_991665 := by exact prefixLift 991665
  have htrace : WordTrace (prefixWord ++ tailWord_991665) baseStart_991665 baseEnd_991665 := by
    simpa [prefixWord, tailWord_991665, baseEnd_991665] using wordTrace_append hprefix tailTrace_991665
  have hstable : (prefixWord ++ tailWord_991665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991665).length < 2 ^ (prefixWord ++ tailWord_991665).sum := by decide
  have hdescent : baseEnd_991665 < baseStart_991665 := by decide
  rcases family_descends (prefixWord ++ tailWord_991665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991713 : List Nat := [1, 2, 3, 1, 2, 2, 2, 5, 2]
def baseStart_991713 : Nat := 118140960795 + 991713 * 2 ^ 59
def prefixEnd_991713 : Nat := 4983230072969 + 3 ^ 40 * 991713 * 2
def baseEnd_991713 : Nat := 452644835833229912912623

theorem tailTrace_991713 : CollatzResearch.WordTrace tailWord_991713 prefixEnd_991713 452644835833229912912623 := by
  unfold tailWord_991713
  simp only [CollatzResearch.WordTrace]
  refine ⟨36170744656200646941187793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24113829770800431294125195 36170744656200646941187793)
  ·
    refine ⟨27128058492150485205890845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36170744656200646941187793 27128058492150485205890845)
    ·
      refine ⟨10173021934556431952209067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27128058492150485205890845 10173021934556431952209067)
      ·
        refine ⟨15259532901834647928313601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10173021934556431952209067 15259532901834647928313601)
        ·
          refine ⟨11444649676375985946235201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15259532901834647928313601 11444649676375985946235201)
          ·
            refine ⟨8583487257281989459676401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11444649676375985946235201 8583487257281989459676401)
            ·
              refine ⟨6437615442961492094757301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8583487257281989459676401 6437615442961492094757301)
              ·
                refine ⟨603526447777639883883497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6437615442961492094757301 603526447777639883883497)
                ·
                  refine ⟨452644835833229912912623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603526447777639883883497 452644835833229912912623)
                  ·
                    rfl

theorem cell20_991713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 2].length) (baseStart_991713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991713 prefixEnd_991713 := by exact prefixLift 991713
  have htrace : WordTrace (prefixWord ++ tailWord_991713) baseStart_991713 baseEnd_991713 := by
    simpa [prefixWord, tailWord_991713, baseEnd_991713] using wordTrace_append hprefix tailTrace_991713
  have hstable : (prefixWord ++ tailWord_991713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991713).length < 2 ^ (prefixWord ++ tailWord_991713).sum := by decide
  have hdescent : baseEnd_991713 < baseStart_991713 := by decide
  rcases family_descends (prefixWord ++ tailWord_991713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991751 : List Nat := [1, 1, 4, 3, 3, 1, 1, 2, 4]
def baseStart_991751 : Nat := 118140960795 + 991751 * 2 ^ 59
def prefixEnd_991751 : Nat := 4983230072969 + 3 ^ 40 * 991751 * 2
def baseEnd_991751 : Nat := 452662180068670669645801

theorem tailTrace_991751 : CollatzResearch.WordTrace tailWord_991751 prefixEnd_991751 452662180068670669645801 := by
  unfold tailWord_991751
  simp only [CollatzResearch.WordTrace]
  refine ⟨36172130630062979431071107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24114753753375319620714071 36172130630062979431071107)
  ·
    refine ⟨54258195945094469146606661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36172130630062979431071107 54258195945094469146606661)
    ·
      refine ⟨10173411739705212964988749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54258195945094469146606661 10173411739705212964988749)
      ·
        refine ⟨3815029402389454861870781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10173411739705212964988749 3815029402389454861870781)
        ·
          refine ⟨1430636025896045573201543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3815029402389454861870781 1430636025896045573201543)
          ·
            refine ⟨2145954038844068359802315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430636025896045573201543 2145954038844068359802315)
            ·
              refine ⟨3218931058266102539703473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2145954038844068359802315 3218931058266102539703473)
              ·
                refine ⟨2414198293699576904777605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3218931058266102539703473 2414198293699576904777605)
                ·
                  refine ⟨452662180068670669645801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2414198293699576904777605 452662180068670669645801)
                  ·
                    rfl

theorem cell20_991751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 4].length) (baseStart_991751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991751 prefixEnd_991751 := by exact prefixLift 991751
  have htrace : WordTrace (prefixWord ++ tailWord_991751) baseStart_991751 baseEnd_991751 := by
    simpa [prefixWord, tailWord_991751, baseEnd_991751] using wordTrace_append hprefix tailTrace_991751
  have hstable : (prefixWord ++ tailWord_991751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991751).length < 2 ^ (prefixWord ++ tailWord_991751).sum := by decide
  have hdescent : baseEnd_991751 < baseStart_991751 := by decide
  rcases family_descends (prefixWord ++ tailWord_991751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991768 : List Nat := [2, 1, 2, 3, 3, 2, 2, 3, 2]
def baseStart_991768 : Nat := 118140960795 + 991768 * 2 ^ 59
def prefixEnd_991768 : Nat := 4983230072969 + 3 ^ 40 * 991768 * 2
def baseEnd_991768 : Nat := 452669939331894166079065

theorem tailTrace_991768 : CollatzResearch.WordTrace tailWord_991768 prefixEnd_991768 452669939331894166079065 := by
  unfold tailWord_991768
  simp only [CollatzResearch.WordTrace]
  refine ⟨18086375335500695667219979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24115167114000927556293305 18086375335500695667219979)
  ·
    refine ⟨27129563003251043500829969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18086375335500695667219979 27129563003251043500829969)
    ·
      refine ⟨20347172252438282625622477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27129563003251043500829969 20347172252438282625622477)
      ·
        refine ⟨7630189594664355984608429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20347172252438282625622477 7630189594664355984608429)
        ·
          refine ⟨2861321097999133494228161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7630189594664355984608429 2861321097999133494228161)
          ·
            refine ⟨2145990823499350120671121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2861321097999133494228161 2145990823499350120671121)
            ·
              refine ⟨1609493117624512590503341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2145990823499350120671121 1609493117624512590503341)
              ·
                refine ⟨603559919109192221438753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1609493117624512590503341 603559919109192221438753)
                ·
                  refine ⟨452669939331894166079065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603559919109192221438753 452669939331894166079065)
                  ·
                    rfl

theorem cell20_991768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 2].length) (baseStart_991768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991768 prefixEnd_991768 := by exact prefixLift 991768
  have htrace : WordTrace (prefixWord ++ tailWord_991768) baseStart_991768 baseEnd_991768 := by
    simpa [prefixWord, tailWord_991768, baseEnd_991768] using wordTrace_append hprefix tailTrace_991768
  have hstable : (prefixWord ++ tailWord_991768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991768).length < 2 ^ (prefixWord ++ tailWord_991768).sum := by decide
  have hdescent : baseEnd_991768 < baseStart_991768 := by decide
  rcases family_descends (prefixWord ++ tailWord_991768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991779 : List Nat := [1, 1, 1, 4, 4, 2, 7]
def baseStart_991779 : Nat := 118140960795 + 991779 * 2 ^ 59
def prefixEnd_991779 : Nat := 4983230072969 + 3 ^ 40 * 991779 * 2
def baseEnd_991779 : Nat := 50297217781291890745817

theorem tailTrace_991779 : CollatzResearch.WordTrace tailWord_991779 prefixEnd_991779 50297217781291890745817 := by
  unfold tailWord_991779
  simp only [CollatzResearch.WordTrace]
  refine ⟨36173151873961540213090391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24115434582641026808726927 36173151873961540213090391)
  ·
    refine ⟨54259727810942310319635587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36173151873961540213090391 54259727810942310319635587)
    ·
      refine ⟨81389591716413465479453381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54259727810942310319635587 81389591716413465479453381)
      ·
        refine ⟨15260548446827524777397509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81389591716413465479453381 15260548446827524777397509)
        ·
          refine ⟨2861352833780160895762033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15260548446827524777397509 2861352833780160895762033)
          ·
            refine ⟨2146014625335120671821525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2861352833780160895762033 2146014625335120671821525)
            ·
              refine ⟨50297217781291890745817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2146014625335120671821525 50297217781291890745817)
              ·
                rfl

theorem cell20_991779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 7].length) (baseStart_991779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991779 prefixEnd_991779 := by exact prefixLift 991779
  have htrace : WordTrace (prefixWord ++ tailWord_991779) baseStart_991779 baseEnd_991779 := by
    simpa [prefixWord, tailWord_991779, baseEnd_991779] using wordTrace_append hprefix tailTrace_991779
  have hstable : (prefixWord ++ tailWord_991779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991779).length < 2 ^ (prefixWord ++ tailWord_991779).sum := by decide
  have hdescent : baseEnd_991779 < baseStart_991779 := by decide
  rcases family_descends (prefixWord ++ tailWord_991779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991844 : List Nat := [2, 3, 1, 1, 2, 2, 5, 2, 2]
def baseStart_991844 : Nat := 118140960795 + 991844 * 2 ^ 59
def prefixEnd_991844 : Nat := 4983230072969 + 3 ^ 40 * 991844 * 2
def baseEnd_991844 : Nat := 452704627802775679545421

theorem tailTrace_991844 : CollatzResearch.WordTrace tailWord_991844 prefixEnd_991844 452704627802775679545421 := by
  unfold tailWord_991844
  simp only [CollatzResearch.WordTrace]
  refine ⟨18087761309363028157103293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24117015079150704209471057 18087761309363028157103293)
  ·
    refine ⟨6782910491011135558913735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18087761309363028157103293 6782910491011135558913735)
    ·
      refine ⟨10174365736516703338370603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6782910491011135558913735 10174365736516703338370603)
      ·
        refine ⟨15261548604775055007555905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10174365736516703338370603 15261548604775055007555905)
        ·
          refine ⟨11446161453581291255666929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15261548604775055007555905 11446161453581291255666929)
          ·
            refine ⟨8584621090185968441750197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11446161453581291255666929 8584621090185968441750197)
            ·
              refine ⟨804808227204934541414081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8584621090185968441750197 804808227204934541414081)
              ·
                refine ⟨603606170403700906060561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 804808227204934541414081 603606170403700906060561)
                ·
                  refine ⟨452704627802775679545421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603606170403700906060561 452704627802775679545421)
                  ·
                    rfl

theorem cell20_991844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_991844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991844 prefixEnd_991844 := by exact prefixLift 991844
  have htrace : WordTrace (prefixWord ++ tailWord_991844) baseStart_991844 baseEnd_991844 := by
    simpa [prefixWord, tailWord_991844, baseEnd_991844] using wordTrace_append hprefix tailTrace_991844
  have hstable : (prefixWord ++ tailWord_991844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991844).length < 2 ^ (prefixWord ++ tailWord_991844).sum := by decide
  have hdescent : baseEnd_991844 < baseStart_991844 := by decide
  rcases family_descends (prefixWord ++ tailWord_991844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991858 : List Nat := [3, 2, 1, 2, 4, 1, 1, 3, 3]
def baseStart_991858 : Nat := 118140960795 + 991858 * 2 ^ 59
def prefixEnd_991858 : Nat := 4983230072969 + 3 ^ 40 * 991858 * 2
def baseEnd_991858 : Nat := 452711017784253853078697

theorem tailTrace_991858 : CollatzResearch.WordTrace tailWord_991858 prefixEnd_991858 452711017784253853078697 := by
  unfold tailWord_991858
  simp only [CollatzResearch.WordTrace]
  refine ⟨9044008310168834176304057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24117355493783557803477485 9044008310168834176304057)
  ·
    refine ⟨6783006232626625632228043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9044008310168834176304057 6783006232626625632228043)
    ·
      refine ⟨10174509348939938448342065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6783006232626625632228043 10174509348939938448342065)
      ·
        refine ⟨7630882011704953836256549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10174509348939938448342065 7630882011704953836256549)
        ·
          refine ⟨1430790377194678844298103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7630882011704953836256549 1430790377194678844298103)
          ·
            refine ⟨2146185565792018266447155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430790377194678844298103 2146185565792018266447155)
            ·
              refine ⟨3219278348688027399670733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2146185565792018266447155 3219278348688027399670733)
              ·
                refine ⟨1207229380758010274876525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3219278348688027399670733 1207229380758010274876525)
                ·
                  refine ⟨452711017784253853078697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1207229380758010274876525 452711017784253853078697)
                  ·
                    rfl

theorem cell20_991858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_991858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991858 prefixEnd_991858 := by exact prefixLift 991858
  have htrace : WordTrace (prefixWord ++ tailWord_991858) baseStart_991858 baseEnd_991858 := by
    simpa [prefixWord, tailWord_991858, baseEnd_991858] using wordTrace_append hprefix tailTrace_991858
  have hstable : (prefixWord ++ tailWord_991858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991858).length < 2 ^ (prefixWord ++ tailWord_991858).sum := by decide
  have hdescent : baseEnd_991858 < baseStart_991858 := by decide
  rcases family_descends (prefixWord ++ tailWord_991858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991962 : List Nat := [3, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_991962 : Nat := 118140960795 + 991962 * 2 ^ 59
def prefixEnd_991962 : Nat := 4983230072969 + 3 ^ 40 * 991962 * 2
def baseEnd_991962 : Nat := 452758486218091713611605

theorem tailTrace_991962 : CollatzResearch.WordTrace tailWord_991962 prefixEnd_991962 452758486218091713611605 := by
  unfold tailWord_991962
  simp only [CollatzResearch.WordTrace]
  refine ⟨9044956608074640616750535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24119884288199041644668093 9044956608074640616750535)
  ·
    refine ⟨13567434912111960925125803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9044956608074640616750535 13567434912111960925125803)
    ·
      refine ⟨20351152368167941387688705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13567434912111960925125803 20351152368167941387688705)
      ·
        refine ⟨15263364276125956040766529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20351152368167941387688705 15263364276125956040766529)
        ·
          refine ⟨11447523207094467030574897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15263364276125956040766529 11447523207094467030574897)
          ·
            refine ⟨8585642405320850272931173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11447523207094467030574897 8585642405320850272931173)
            ·
              refine ⟨1609807950997659426174595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8585642405320850272931173 1609807950997659426174595)
              ·
                refine ⟨2414711926496489139261893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1609807950997659426174595 2414711926496489139261893)
                ·
                  refine ⟨452758486218091713611605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2414711926496489139261893 452758486218091713611605)
                  ·
                    rfl

theorem cell20_991962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_991962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991962 prefixEnd_991962 := by exact prefixLift 991962
  have htrace : WordTrace (prefixWord ++ tailWord_991962) baseStart_991962 baseEnd_991962 := by
    simpa [prefixWord, tailWord_991962, baseEnd_991962] using wordTrace_append hprefix tailTrace_991962
  have hstable : (prefixWord ++ tailWord_991962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991962).length < 2 ^ (prefixWord ++ tailWord_991962).sum := by decide
  have hdescent : baseEnd_991962 < baseStart_991962 := by decide
  rcases family_descends (prefixWord ++ tailWord_991962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991972 : List Nat := [2, 3, 1, 1, 1, 5, 3, 1, 3]
def baseStart_991972 : Nat := 118140960795 + 991972 * 2 ^ 59
def prefixEnd_991972 : Nat := 4983230072969 + 3 ^ 40 * 991972 * 2
def baseEnd_991972 : Nat := 452763050490576123278231

theorem tailTrace_991972 : CollatzResearch.WordTrace tailWord_991972 prefixEnd_991972 452763050490576123278231 := by
  unfold tailWord_991972
  simp only [CollatzResearch.WordTrace]
  refine ⟨18090095581131167087433085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24120127441508222783244113 18090095581131167087433085)
  ·
    refine ⟨6783785842924187657787407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18090095581131167087433085 6783785842924187657787407)
    ·
      refine ⟨10175678764386281486681111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6783785842924187657787407 10175678764386281486681111)
      ·
        refine ⟨15263518146579422230021667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10175678764386281486681111 15263518146579422230021667)
        ·
          refine ⟨22895277219869133345032501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15263518146579422230021667 22895277219869133345032501)
          ·
            refine ⟨2146432239362731251096797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22895277219869133345032501 2146432239362731251096797)
            ·
              refine ⟨804912089761024219161299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2146432239362731251096797 804912089761024219161299)
              ·
                refine ⟨1207368134641536328741949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804912089761024219161299 1207368134641536328741949)
                ·
                  refine ⟨452763050490576123278231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1207368134641536328741949 452763050490576123278231)
                  ·
                    rfl

theorem cell20_991972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_991972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991972 prefixEnd_991972 := by exact prefixLift 991972
  have htrace : WordTrace (prefixWord ++ tailWord_991972) baseStart_991972 baseEnd_991972 := by
    simpa [prefixWord, tailWord_991972, baseEnd_991972] using wordTrace_append hprefix tailTrace_991972
  have hstable : (prefixWord ++ tailWord_991972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991972).length < 2 ^ (prefixWord ++ tailWord_991972).sum := by decide
  have hdescent : baseEnd_991972 < baseStart_991972 := by decide
  rcases family_descends (prefixWord ++ tailWord_991972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_991986 : List Nat := [3, 2, 1, 3, 1, 2, 4, 4]
def baseStart_991986 : Nat := 118140960795 + 991986 * 2 ^ 59
def prefixEnd_991986 : Nat := 4983230072969 + 3 ^ 40 * 991986 * 2
def baseEnd_991986 : Nat := 150923146824018098937169

theorem tailTrace_991986 : CollatzResearch.WordTrace tailWord_991986 prefixEnd_991986 150923146824018098937169 := by
  unfold tailWord_991986
  simp only [CollatzResearch.WordTrace]
  refine ⟨9045175446052903641468953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24120467856141076377250541 9045175446052903641468953)
  ·
    refine ⟨6783881584539677731101715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9045175446052903641468953 6783881584539677731101715)
    ·
      refine ⟨10175822376809516596652573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6783881584539677731101715 10175822376809516596652573)
      ·
        refine ⟨3815933391303568723744715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10175822376809516596652573 3815933391303568723744715)
        ·
          refine ⟨5723900086955353085617073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3815933391303568723744715 5723900086955353085617073)
          ·
            refine ⟨4292925065216514814212805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5723900086955353085617073 4292925065216514814212805)
            ·
              refine ⟨804923449728096527664901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4292925065216514814212805 804923449728096527664901)
              ·
                refine ⟨150923146824018098937169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 804923449728096527664901 150923146824018098937169)
                ·
                  rfl

theorem cell20_991986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_991986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_991986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_991986 prefixEnd_991986 := by exact prefixLift 991986
  have htrace : WordTrace (prefixWord ++ tailWord_991986) baseStart_991986 baseEnd_991986 := by
    simpa [prefixWord, tailWord_991986, baseEnd_991986] using wordTrace_append hprefix tailTrace_991986
  have hstable : (prefixWord ++ tailWord_991986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_991986).length < 2 ^ (prefixWord ++ tailWord_991986).sum := by decide
  have hdescent : baseEnd_991986 < baseStart_991986 := by decide
  rcases family_descends (prefixWord ++ tailWord_991986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
