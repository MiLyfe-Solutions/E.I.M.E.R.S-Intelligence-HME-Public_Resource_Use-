import V185TrunkScan23Chunk0663

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3925362 : List Nat := [3, 2, 1, 2, 1, 2, 5, 1, 1, 2, 3]
def baseStart_3925362 : Nat := 118140960795 + 3925362 * 2 ^ 59
def prefixEnd_3925362 : Nat := 4983230072969 + 3 ^ 40 * 3925362 * 2
def baseEnd_3925362 : Nat := 2015597448894176236822595

theorem tailTrace_3925362 : CollatzResearch.WordTrace tailWord_3925362 prefixEnd_3925362 2015597448894176236822595 := by
  unfold tailWord_3925362
  simp only [CollatzResearch.WordTrace]
  refine ⟨35792428501272836825390585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95446476003394231534374893 35792428501272836825390585)
  ·
    refine ⟨26844321375954627619042939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35792428501272836825390585 26844321375954627619042939)
    ·
      refine ⟨40266482063931941428564409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26844321375954627619042939 40266482063931941428564409)
      ·
        refine ⟨30199861547948956071423307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40266482063931941428564409 30199861547948956071423307)
        ·
          refine ⟨45299792321923434107134961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30199861547948956071423307 45299792321923434107134961)
          ·
            refine ⟨33974844241442575580351221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45299792321923434107134961 33974844241442575580351221)
            ·
              refine ⟨3185141647635241460657927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33974844241442575580351221 3185141647635241460657927)
              ·
                refine ⟨4777712471452862190986891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3185141647635241460657927 4777712471452862190986891)
                ·
                  refine ⟨7166568707179293286480337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4777712471452862190986891 7166568707179293286480337)
                  ·
                    refine ⟨5374926530384469964860253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7166568707179293286480337 5374926530384469964860253)
                    ·
                      refine ⟨2015597448894176236822595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5374926530384469964860253 2015597448894176236822595)
                      ·
                        rfl

theorem cell23_3925362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_3925362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925362 prefixEnd_3925362 := by exact prefixLift 3925362
  have htrace : WordTrace (prefixWord ++ tailWord_3925362) baseStart_3925362 baseEnd_3925362 := by
    simpa [prefixWord, tailWord_3925362, baseEnd_3925362] using wordTrace_append hprefix tailTrace_3925362
  have hstable : (prefixWord ++ tailWord_3925362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925362).length < 2 ^ (prefixWord ++ tailWord_3925362).sum := by decide
  have hdescent : baseEnd_3925362 < baseStart_3925362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925402 : List Nat := [3, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2]
def baseStart_3925402 : Nat := 118140960795 + 3925402 * 2 ^ 59
def prefixEnd_3925402 : Nat := 4983230072969 + 3 ^ 40 * 3925402 * 2
def baseEnd_3925402 : Nat := 2015617988120356080322411

theorem tailTrace_3925402 : CollatzResearch.WordTrace tailWord_3925402 prefixEnd_3925402 2015617988120356080322411 := by
  unfold tailWord_3925402
  simp only [CollatzResearch.WordTrace]
  refine ⟨35792793231236608533254615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95447448616630956088678973 35792793231236608533254615)
  ·
    refine ⟨53689189846854912799881923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35792793231236608533254615 53689189846854912799881923)
    ·
      refine ⟨80533784770282369199822885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53689189846854912799881923 80533784770282369199822885)
      ·
        refine ⟨15100084644427944224966791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80533784770282369199822885 15100084644427944224966791)
        ·
          refine ⟨22650126966641916337450187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15100084644427944224966791 22650126966641916337450187)
          ·
            refine ⟨33975190449962874506175281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22650126966641916337450187 33975190449962874506175281)
            ·
              refine ⟨25481392837472155879631461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33975190449962874506175281 25481392837472155879631461)
              ·
                refine ⟨4777761157026029227430899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25481392837472155879631461 4777761157026029227430899)
                ·
                  refine ⟨7166641735539043841146349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4777761157026029227430899 7166641735539043841146349)
                  ·
                    refine ⟨2687490650827141440429881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7166641735539043841146349 2687490650827141440429881)
                    ·
                      refine ⟨2015617988120356080322411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2687490650827141440429881 2015617988120356080322411)
                      ·
                        rfl

theorem cell23_3925402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_3925402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925402 prefixEnd_3925402 := by exact prefixLift 3925402
  have htrace : WordTrace (prefixWord ++ tailWord_3925402) baseStart_3925402 baseEnd_3925402 := by
    simpa [prefixWord, tailWord_3925402, baseEnd_3925402] using wordTrace_append hprefix tailTrace_3925402
  have hstable : (prefixWord ++ tailWord_3925402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925402).length < 2 ^ (prefixWord ++ tailWord_3925402).sum := by decide
  have hdescent : baseEnd_3925402 < baseStart_3925402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925568 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 7]
def baseStart_3925568 : Nat := 118140960795 + 3925568 * 2 ^ 59
def prefixEnd_3925568 : Nat := 4983230072969 + 3 ^ 40 * 3925568 * 2
def baseEnd_3925568 : Nat := 2015703225909002430846647

theorem tailTrace_3925568 : CollatzResearch.WordTrace tailWord_3925568 prefixEnd_3925568 2015703225909002430846647 := by
  unfold tailWord_3925568
  simp only [CollatzResearch.WordTrace]
  refine ⟨71588613721172522241780679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95451484961563362989040905 71588613721172522241780679)
  ·
    refine ⟨107382920581758783362671019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71588613721172522241780679 107382920581758783362671019)
    ·
      refine ⟨161074380872638175044006529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107382920581758783362671019 161074380872638175044006529)
      ·
        refine ⟨120805785654478631283004897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161074380872638175044006529 120805785654478631283004897)
        ·
          refine ⟨90604339240858973462253673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120805785654478631283004897 90604339240858973462253673)
          ·
            refine ⟨67953254430644230096690255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90604339240858973462253673 67953254430644230096690255)
            ·
              refine ⟨101929881645966345145035383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67953254430644230096690255 101929881645966345145035383)
              ·
                refine ⟨152894822468949517717553075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101929881645966345145035383 152894822468949517717553075)
                ·
                  refine ⟨229342233703424276576329613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152894822468949517717553075 229342233703424276576329613)
                  ·
                    refine ⟨86003337638784103716123605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 229342233703424276576329613 86003337638784103716123605)
                    ·
                      refine ⟨2015703225909002430846647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86003337638784103716123605 2015703225909002430846647)
                      ·
                        rfl

theorem cell23_3925568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_3925568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925568 prefixEnd_3925568 := by exact prefixLift 3925568
  have htrace : WordTrace (prefixWord ++ tailWord_3925568) baseStart_3925568 baseEnd_3925568 := by
    simpa [prefixWord, tailWord_3925568, baseEnd_3925568] using wordTrace_append hprefix tailTrace_3925568
  have hstable : (prefixWord ++ tailWord_3925568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925568).length < 2 ^ (prefixWord ++ tailWord_3925568).sum := by decide
  have hdescent : baseEnd_3925568 < baseStart_3925568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925625 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 1, 1, 6]
def baseStart_3925625 : Nat := 118140960795 + 3925625 * 2 ^ 59
def prefixEnd_3925625 : Nat := 4983230072969 + 3 ^ 40 * 3925625 * 2
def baseEnd_3925625 : Nat := 2015732494306308707833885

theorem tailTrace_3925625 : CollatzResearch.WordTrace tailWord_3925625 prefixEnd_3925625 2015732494306308707833885 := by
  unfold tailWord_3925625
  simp only [CollatzResearch.WordTrace]
  refine ⟨143179306403138543218386329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95452870935425695478924219 143179306403138543218386329)
  ·
    refine ⟨107384479802353907413789747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143179306403138543218386329 107384479802353907413789747)
    ·
      refine ⟨161076719703530861120684621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107384479802353907413789747 161076719703530861120684621)
      ·
        refine ⟨60403769888824072920256733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161076719703530861120684621 60403769888824072920256733)
        ·
          refine ⟨22651413708309027345096275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60403769888824072920256733 22651413708309027345096275)
          ·
            refine ⟨33977120562463541017644413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22651413708309027345096275 33977120562463541017644413)
            ·
              refine ⟨12741420210923827881616655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33977120562463541017644413 12741420210923827881616655)
              ·
                refine ⟨19112130316385741822424983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12741420210923827881616655 19112130316385741822424983)
                ·
                  refine ⟨28668195474578612733637475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19112130316385741822424983 28668195474578612733637475)
                  ·
                    refine ⟨43002293211867919100456213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28668195474578612733637475 43002293211867919100456213)
                    ·
                      refine ⟨2015732494306308707833885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43002293211867919100456213 2015732494306308707833885)
                      ·
                        rfl

theorem cell23_3925625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_3925625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925625 prefixEnd_3925625 := by exact prefixLift 3925625
  have htrace : WordTrace (prefixWord ++ tailWord_3925625) baseStart_3925625 baseEnd_3925625 := by
    simpa [prefixWord, tailWord_3925625, baseEnd_3925625] using wordTrace_append hprefix tailTrace_3925625
  have hstable : (prefixWord ++ tailWord_3925625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925625).length < 2 ^ (prefixWord ++ tailWord_3925625).sum := by decide
  have hdescent : baseEnd_3925625 < baseStart_3925625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925629 : List Nat := [1, 4, 1, 1, 4, 2, 2, 2, 1, 1, 4]
def baseStart_3925629 : Nat := 118140960795 + 3925629 * 2 ^ 59
def prefixEnd_3925629 : Nat := 4983230072969 + 3 ^ 40 * 3925629 * 2
def baseEnd_3925629 : Nat := 2015734548228926692183867

theorem tailTrace_3925629 : CollatzResearch.WordTrace tailWord_3925629 prefixEnd_3925629 2015734548228926692183867 := by
  unfold tailWord_3925629
  simp only [CollatzResearch.WordTrace]
  refine ⟨143179452295124051901531941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95452968196749367934354627 143179452295124051901531941)
  ·
    refine ⟨26846147305335759731537239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143179452295124051901531941 26846147305335759731537239)
    ·
      refine ⟨40269220958003639597305859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26846147305335759731537239 40269220958003639597305859)
      ·
        refine ⟨60403831437005459395958789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40269220958003639597305859 60403831437005459395958789)
        ·
          refine ⟨11325718394438523636742273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60403831437005459395958789 11325718394438523636742273)
          ·
            refine ⟨8494288795828892727556705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11325718394438523636742273 8494288795828892727556705)
            ·
              refine ⟨6370716596871669545667529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8494288795828892727556705 6370716596871669545667529)
              ·
                refine ⟨4778037447653752159250647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6370716596871669545667529 4778037447653752159250647)
                ·
                  refine ⟨7167056171480628238875971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4778037447653752159250647 7167056171480628238875971)
                  ·
                    refine ⟨10750584257220942358313957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7167056171480628238875971 10750584257220942358313957)
                    ·
                      refine ⟨2015734548228926692183867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10750584257220942358313957 2015734548228926692183867)
                      ·
                        rfl

theorem cell23_3925629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_3925629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925629 prefixEnd_3925629 := by exact prefixLift 3925629
  have htrace : WordTrace (prefixWord ++ tailWord_3925629) baseStart_3925629 baseEnd_3925629 := by
    simpa [prefixWord, tailWord_3925629, baseEnd_3925629] using wordTrace_append hprefix tailTrace_3925629
  have hstable : (prefixWord ++ tailWord_3925629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925629).length < 2 ^ (prefixWord ++ tailWord_3925629).sum := by decide
  have hdescent : baseEnd_3925629 < baseStart_3925629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925640 : List Nat := [2, 1, 3, 5, 1, 2, 1, 3, 1, 1, 3]
def baseStart_3925640 : Nat := 118140960795 + 3925640 * 2 ^ 59
def prefixEnd_3925640 : Nat := 4983230072969 + 3 ^ 40 * 3925640 * 2
def baseEnd_3925640 : Nat := 2015740196516126149146317

theorem tailTrace_3925640 : CollatzResearch.WordTrace tailWord_3925640 prefixEnd_3925640 2015740196516126149146317 := by
  unfold tailWord_3925640
  simp only [CollatzResearch.WordTrace]
  refine ⟨71589926749042100390091187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95453235665389467186788249 71589926749042100390091187)
  ·
    refine ⟨107384890123563150585136781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71589926749042100390091187 107384890123563150585136781)
    ·
      refine ⟨40269333796336181469426293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107384890123563150585136781 40269333796336181469426293)
      ·
        refine ⟨3775250043406517012758715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40269333796336181469426293 3775250043406517012758715)
        ·
          refine ⟨5662875065109775519138073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3775250043406517012758715 5662875065109775519138073)
          ·
            refine ⟨4247156298832331639353555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5662875065109775519138073 4247156298832331639353555)
            ·
              refine ⟨6370734448248497459030333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4247156298832331639353555 6370734448248497459030333)
              ·
                refine ⟨2389025418093186547136375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6370734448248497459030333 2389025418093186547136375)
                ·
                  refine ⟨3583538127139779820704563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2389025418093186547136375 3583538127139779820704563)
                  ·
                    refine ⟨5375307190709669731056845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3583538127139779820704563 5375307190709669731056845)
                    ·
                      refine ⟨2015740196516126149146317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5375307190709669731056845 2015740196516126149146317)
                      ·
                        rfl

theorem cell23_3925640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_3925640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925640 prefixEnd_3925640 := by exact prefixLift 3925640
  have htrace : WordTrace (prefixWord ++ tailWord_3925640) baseStart_3925640 baseEnd_3925640 := by
    simpa [prefixWord, tailWord_3925640, baseEnd_3925640] using wordTrace_append hprefix tailTrace_3925640
  have hstable : (prefixWord ++ tailWord_3925640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925640).length < 2 ^ (prefixWord ++ tailWord_3925640).sum := by decide
  have hdescent : baseEnd_3925640 < baseStart_3925640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925679 : List Nat := [1, 1, 2, 1, 2, 4, 3, 3, 2, 1, 3]
def baseStart_3925679 : Nat := 118140960795 + 3925679 * 2 ^ 59
def prefixEnd_3925679 : Nat := 4983230072969 + 3 ^ 40 * 3925679 * 2
def baseEnd_3925679 : Nat := 2015760222261651496558637

theorem tailTrace_3925679 : CollatzResearch.WordTrace tailWord_3925679 prefixEnd_3925679 2015760222261651496558637 := by
  unfold tailWord_3925679
  simp only [CollatzResearch.WordTrace]
  refine ⟨143181275944942910440852091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95454183963295273627234727 143181275944942910440852091)
  ·
    refine ⟨214771913917414365661278137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143181275944942910440852091 214771913917414365661278137)
    ·
      refine ⟨161078935438060774245958603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214771913917414365661278137 161078935438060774245958603)
      ·
        refine ⟨241618403157091161368937905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161078935438060774245958603 241618403157091161368937905)
        ·
          refine ⟨181213802367818371026703429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241618403157091161368937905 181213802367818371026703429)
          ·
            refine ⟨33977587943965944567506893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181213802367818371026703429 33977587943965944567506893)
            ·
              refine ⟨12741595478987229212815085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33977587943965944567506893 12741595478987229212815085)
              ·
                refine ⟨4778098304620210954805657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12741595478987229212815085 4778098304620210954805657)
                ·
                  refine ⟨3583573728465158216104243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4778098304620210954805657 3583573728465158216104243)
                  ·
                    refine ⟨5375360592697737324156365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3583573728465158216104243 5375360592697737324156365)
                    ·
                      refine ⟨2015760222261651496558637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5375360592697737324156365 2015760222261651496558637)
                      ·
                        rfl

theorem cell23_3925679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 1, 3].length) (baseStart_3925679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925679 prefixEnd_3925679 := by exact prefixLift 3925679
  have htrace : WordTrace (prefixWord ++ tailWord_3925679) baseStart_3925679 baseEnd_3925679 := by
    simpa [prefixWord, tailWord_3925679, baseEnd_3925679] using wordTrace_append hprefix tailTrace_3925679
  have hstable : (prefixWord ++ tailWord_3925679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925679).length < 2 ^ (prefixWord ++ tailWord_3925679).sum := by decide
  have hdescent : baseEnd_3925679 < baseStart_3925679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925722 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3]
def baseStart_3925722 : Nat := 118140960795 + 3925722 * 2 ^ 59
def prefixEnd_3925722 : Nat := 4983230072969 + 3 ^ 40 * 3925722 * 2
def baseEnd_3925722 : Nat := 2015782301929794828320939

theorem tailTrace_3925722 : CollatzResearch.WordTrace tailWord_3925722 prefixEnd_3925722 2015782301929794828320939 := by
  unfold tailWord_3925722
  simp only [CollatzResearch.WordTrace]
  refine ⟨35795711070946782196166855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95455229522524752523111613 35795711070946782196166855)
  ·
    refine ⟨53693566606420173294250283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35795711070946782196166855 53693566606420173294250283)
    ·
      refine ⟨80540349909630259941375425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53693566606420173294250283 80540349909630259941375425)
      ·
        refine ⟨60405262432222694956031569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80540349909630259941375425 60405262432222694956031569)
        ·
          refine ⟨45303946824167021217023677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60405262432222694956031569 45303946824167021217023677)
          ·
            refine ⟨16988980059062632956383879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45303946824167021217023677 16988980059062632956383879)
            ·
              refine ⟨25483470088593949434575819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16988980059062632956383879 25483470088593949434575819)
              ·
                refine ⟨38225205132890924151863729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25483470088593949434575819 38225205132890924151863729)
                ·
                  refine ⟨28668903849668193113897797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38225205132890924151863729 28668903849668193113897797)
                  ·
                    refine ⟨5375419471812786208855837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28668903849668193113897797 5375419471812786208855837)
                    ·
                      refine ⟨2015782301929794828320939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5375419471812786208855837 2015782301929794828320939)
                      ·
                        rfl

theorem cell23_3925722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_3925722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925722 prefixEnd_3925722 := by exact prefixLift 3925722
  have htrace : WordTrace (prefixWord ++ tailWord_3925722) baseStart_3925722 baseEnd_3925722 := by
    simpa [prefixWord, tailWord_3925722, baseEnd_3925722] using wordTrace_append hprefix tailTrace_3925722
  have hstable : (prefixWord ++ tailWord_3925722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925722).length < 2 ^ (prefixWord ++ tailWord_3925722).sum := by decide
  have hdescent : baseEnd_3925722 < baseStart_3925722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925732 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_3925732 : Nat := 118140960795 + 3925732 * 2 ^ 59
def prefixEnd_3925732 : Nat := 4983230072969 + 3 ^ 40 * 3925732 * 2
def baseEnd_3925732 : Nat := 2015787436736339789195893

theorem tailTrace_3925732 : CollatzResearch.WordTrace tailWord_3925732 prefixEnd_3925732 2015787436736339789195893 := by
  unfold tailWord_3925732
  simp only [CollatzResearch.WordTrace]
  refine ⟨71591604506875450246265725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95455472675833933661687633 71591604506875450246265725)
  ·
    refine ⟨26846851690078293842349647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71591604506875450246265725 26846851690078293842349647)
    ·
      refine ⟨40270277535117440763524471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26846851690078293842349647 40270277535117440763524471)
      ·
        refine ⟨60405416302676161145286707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40270277535117440763524471 60405416302676161145286707)
        ·
          refine ⟨90608124454014241717930061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60405416302676161145286707 90608124454014241717930061)
          ·
            refine ⟨33978046670255340644223773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90608124454014241717930061 33978046670255340644223773)
            ·
              refine ⟨12741767501345752741583915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33978046670255340644223773 12741767501345752741583915)
              ·
                refine ⟨19112651252018629112375873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12741767501345752741583915 19112651252018629112375873)
                ·
                  refine ⟨14334488439013971834281905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19112651252018629112375873 14334488439013971834281905)
                  ·
                    refine ⟨10750866329260478875711429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14334488439013971834281905 10750866329260478875711429)
                    ·
                      refine ⟨2015787436736339789195893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10750866329260478875711429 2015787436736339789195893)
                      ·
                        rfl

theorem cell23_3925732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_3925732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925732 prefixEnd_3925732 := by exact prefixLift 3925732
  have htrace : WordTrace (prefixWord ++ tailWord_3925732) baseStart_3925732 baseEnd_3925732 := by
    simpa [prefixWord, tailWord_3925732, baseEnd_3925732] using wordTrace_append hprefix tailTrace_3925732
  have hstable : (prefixWord ++ tailWord_3925732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925732).length < 2 ^ (prefixWord ++ tailWord_3925732).sum := by decide
  have hdescent : baseEnd_3925732 < baseStart_3925732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925736 : List Nat := [2, 1, 4, 1, 3, 2, 2, 1, 1, 4, 2]
def baseStart_3925736 : Nat := 118140960795 + 3925736 * 2 ^ 59
def prefixEnd_3925736 : Nat := 4983230072969 + 3 ^ 40 * 3925736 * 2
def baseEnd_3925736 : Nat := 2015789490658957773545875

theorem tailTrace_3925736 : CollatzResearch.WordTrace tailWord_3925736 prefixEnd_3925736 2015789490658957773545875 := by
  unfold tailWord_3925736
  simp only [CollatzResearch.WordTrace]
  refine ⟨71591677452868204587838531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95455569937157606117118041 71591677452868204587838531)
  ·
    refine ⟨107387516179302306881757797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71591677452868204587838531 107387516179302306881757797)
    ·
      refine ⟨20135159283619182540329587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107387516179302306881757797 20135159283619182540329587)
      ·
        refine ⟨30202738925428773810494381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20135159283619182540329587 30202738925428773810494381)
        ·
          refine ⟨11326027097035790178935393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30202738925428773810494381 11326027097035790178935393)
          ·
            refine ⟨8494520322776842634201545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11326027097035790178935393 8494520322776842634201545)
            ·
              refine ⟨6370890242082631975651159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8494520322776842634201545 6370890242082631975651159)
              ·
                refine ⟨9556335363123947963476739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6370890242082631975651159 9556335363123947963476739)
                ·
                  refine ⟨14334503044685921945215109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9556335363123947963476739 14334503044685921945215109)
                  ·
                    refine ⟨2687719320878610364727833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14334503044685921945215109 2687719320878610364727833)
                    ·
                      refine ⟨2015789490658957773545875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2687719320878610364727833 2015789490658957773545875)
                      ·
                        rfl

theorem cell23_3925736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_3925736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925736 prefixEnd_3925736 := by exact prefixLift 3925736
  have htrace : WordTrace (prefixWord ++ tailWord_3925736) baseStart_3925736 baseEnd_3925736 := by
    simpa [prefixWord, tailWord_3925736, baseEnd_3925736] using wordTrace_append hprefix tailTrace_3925736
  have hstable : (prefixWord ++ tailWord_3925736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925736).length < 2 ^ (prefixWord ++ tailWord_3925736).sum := by decide
  have hdescent : baseEnd_3925736 < baseStart_3925736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925742 : List Nat := [4, 1, 2, 1, 1, 2, 3, 2, 7]
def baseStart_3925742 : Nat := 118140960795 + 3925742 * 2 ^ 59
def prefixEnd_3925742 : Nat := 4983230072969 + 3 ^ 40 * 3925742 * 2
def baseEnd_3925742 : Nat := 223976952393653861118983

theorem tailTrace_3925742 : CollatzResearch.WordTrace tailWord_3925742 prefixEnd_3925742 223976952393653861118983 := by
  unfold tailWord_3925742
  simp only [CollatzResearch.WordTrace]
  refine ⟨17897946717964334025049435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95455715829143114800263653 17897946717964334025049435)
  ·
    refine ⟨26846920076946501037574153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17897946717964334025049435 26846920076946501037574153)
    ·
      refine ⟨20135190057709875778180615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26846920076946501037574153 20135190057709875778180615)
      ·
        refine ⟨30202785086564813667270923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20135190057709875778180615 30202785086564813667270923)
        ·
          refine ⟨45304177629847220500906385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30202785086564813667270923 45304177629847220500906385)
          ·
            refine ⟨33978133222385415375679789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45304177629847220500906385 33978133222385415375679789)
            ·
              refine ⟨12741799958394530765879921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33978133222385415375679789 12741799958394530765879921)
              ·
                refine ⟨9556349968795898074409941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12741799958394530765879921 9556349968795898074409941)
                ·
                  refine ⟨223976952393653861118983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9556349968795898074409941 223976952393653861118983)
                  ·
                    rfl

theorem cell23_3925742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_3925742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925742 prefixEnd_3925742 := by exact prefixLift 3925742
  have htrace : WordTrace (prefixWord ++ tailWord_3925742) baseStart_3925742 baseEnd_3925742 := by
    simpa [prefixWord, tailWord_3925742, baseEnd_3925742] using wordTrace_append hprefix tailTrace_3925742
  have hstable : (prefixWord ++ tailWord_3925742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925742).length < 2 ^ (prefixWord ++ tailWord_3925742).sum := by decide
  have hdescent : baseEnd_3925742 < baseStart_3925742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925772 : List Nat := [2, 2, 1, 2, 2, 1, 2, 4, 2, 5]
def baseStart_3925772 : Nat := 118140960795 + 3925772 * 2 ^ 59
def prefixEnd_3925772 : Nat := 4983230072969 + 3 ^ 40 * 3925772 * 2
def baseEnd_3925772 : Nat := 671935991987506544231903

theorem tailTrace_3925772 : CollatzResearch.WordTrace tailWord_3925772 prefixEnd_3925772 671935991987506544231903 := by
  unfold tailWord_3925772
  simp only [CollatzResearch.WordTrace]
  refine ⟨71592333966802993661993785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95456445289070658215991713 71592333966802993661993785)
  ·
    refine ⟨53694250475102245246495339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71592333966802993661993785 53694250475102245246495339)
    ·
      refine ⟨80541375712653367869743009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53694250475102245246495339 80541375712653367869743009)
      ·
        refine ⟨60406031784490025902307257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80541375712653367869743009 60406031784490025902307257)
        ·
          refine ⟨45304523838367519426730443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60406031784490025902307257 45304523838367519426730443)
          ·
            refine ⟨67956785757551279140095665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45304523838367519426730443 67956785757551279140095665)
            ·
              refine ⟨50967589318163459355071749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67956785757551279140095665 50967589318163459355071749)
              ·
                refine ⟨9556422997155648629075953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50967589318163459355071749 9556422997155648629075953)
                ·
                  refine ⟨7167317247866736471806965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9556422997155648629075953 7167317247866736471806965)
                  ·
                    refine ⟨671935991987506544231903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7167317247866736471806965 671935991987506544231903)
                    ·
                      rfl

theorem cell23_3925772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_3925772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925772 prefixEnd_3925772 := by exact prefixLift 3925772
  have htrace : WordTrace (prefixWord ++ tailWord_3925772) baseStart_3925772 baseEnd_3925772 := by
    simpa [prefixWord, tailWord_3925772, baseEnd_3925772] using wordTrace_append hprefix tailTrace_3925772
  have hstable : (prefixWord ++ tailWord_3925772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925772).length < 2 ^ (prefixWord ++ tailWord_3925772).sum := by decide
  have hdescent : baseEnd_3925772 < baseStart_3925772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925792 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 4]
def baseStart_3925792 : Nat := 118140960795 + 3925792 * 2 ^ 59
def prefixEnd_3925792 : Nat := 4983230072969 + 3 ^ 40 * 3925792 * 2
def baseEnd_3925792 : Nat := 2015818245575609554445617

theorem tailTrace_3925792 : CollatzResearch.WordTrace tailWord_3925792 prefixEnd_3925792 2015818245575609554445617 := by
  unfold tailWord_3925792
  simp only [CollatzResearch.WordTrace]
  refine ⟨71592698696766765369857815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95456931595689020493143753 71592698696766765369857815)
  ·
    refine ⟨107389048045150148054786723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71592698696766765369857815 107389048045150148054786723)
    ·
      refine ⟨161083572067725222082180085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107389048045150148054786723 161083572067725222082180085)
      ·
        refine ⟨15101584881349239570204383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161083572067725222082180085 15101584881349239570204383)
        ·
          refine ⟨22652377322023859355306575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15101584881349239570204383 22652377322023859355306575)
          ·
            refine ⟨33978565983035789032959863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22652377322023859355306575 33978565983035789032959863)
            ·
              refine ⟨50967848974553683549439795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33978565983035789032959863 50967848974553683549439795)
              ·
                refine ⟨76451773461830525324159693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50967848974553683549439795 76451773461830525324159693)
                ·
                  refine ⟨28669415048186446996559885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76451773461830525324159693 28669415048186446996559885)
                  ·
                    refine ⟨10751030643069917623709957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28669415048186446996559885 10751030643069917623709957)
                    ·
                      refine ⟨2015818245575609554445617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10751030643069917623709957 2015818245575609554445617)
                      ·
                        rfl

theorem cell23_3925792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_3925792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925792 prefixEnd_3925792 := by exact prefixLift 3925792
  have htrace : WordTrace (prefixWord ++ tailWord_3925792) baseStart_3925792 baseEnd_3925792 := by
    simpa [prefixWord, tailWord_3925792, baseEnd_3925792] using wordTrace_append hprefix tailTrace_3925792
  have hstable : (prefixWord ++ tailWord_3925792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925792).length < 2 ^ (prefixWord ++ tailWord_3925792).sum := by decide
  have hdescent : baseEnd_3925792 < baseStart_3925792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925829 : List Nat := [1, 3, 1, 1, 1, 2, 5, 2, 2, 2, 3]
def baseStart_3925829 : Nat := 118140960795 + 3925829 * 2 ^ 59
def prefixEnd_3925829 : Nat := 4983230072969 + 3 ^ 40 * 3925829 * 2
def baseEnd_3925829 : Nat := 2015837244359825909682947

theorem tailTrace_3925829 : CollatzResearch.WordTrace tailWord_3925829 prefixEnd_3925829 2015837244359825909682947 := by
  unfold tailWord_3925829
  simp only [CollatzResearch.WordTrace]
  refine ⟨143186746894399486058812541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95457831262932990705875027 143186746894399486058812541)
  ·
    refine ⟨53695030085399807272054703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143186746894399486058812541 53695030085399807272054703)
    ·
      refine ⟨80542545128099710908082055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53695030085399807272054703 80542545128099710908082055)
      ·
        refine ⟨120813817692149566362123083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80542545128099710908082055 120813817692149566362123083)
        ·
          refine ⟨181220726538224349543184625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120813817692149566362123083 181220726538224349543184625)
          ·
            refine ⟨135915544903668262157388469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181220726538224349543184625 135915544903668262157388469)
            ·
              refine ⟨12742082334718899577255169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135915544903668262157388469 12742082334718899577255169)
              ·
                refine ⟨9556561751039174682941377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12742082334718899577255169 9556561751039174682941377)
                ·
                  refine ⟨7167421313279381012206033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9556561751039174682941377 7167421313279381012206033)
                  ·
                    refine ⟨5375565984959535759154525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7167421313279381012206033 5375565984959535759154525)
                    ·
                      refine ⟨2015837244359825909682947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5375565984959535759154525 2015837244359825909682947)
                      ·
                        rfl

theorem cell23_3925829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_3925829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925829 prefixEnd_3925829 := by exact prefixLift 3925829
  have htrace : WordTrace (prefixWord ++ tailWord_3925829) baseStart_3925829 baseEnd_3925829 := by
    simpa [prefixWord, tailWord_3925829, baseEnd_3925829] using wordTrace_append hprefix tailTrace_3925829
  have hstable : (prefixWord ++ tailWord_3925829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925829).length < 2 ^ (prefixWord ++ tailWord_3925829).sum := by decide
  have hdescent : baseEnd_3925829 < baseStart_3925829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925832 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 8]
def baseStart_3925832 : Nat := 118140960795 + 3925832 * 2 ^ 59
def prefixEnd_3925832 : Nat := 4983230072969 + 3 ^ 40 * 3925832 * 2
def baseEnd_3925832 : Nat := 223982087200198821993937

theorem tailTrace_3925832 : CollatzResearch.WordTrace tailWord_3925832 prefixEnd_3925832 223982087200198821993937 := by
  unfold tailWord_3925832
  simp only [CollatzResearch.WordTrace]
  refine ⟨71593428156694308785585875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95457904208925745047447833 71593428156694308785585875)
  ·
    refine ⟨107390142235041463178378813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71593428156694308785585875 107390142235041463178378813)
    ·
      refine ⟨40271303338140548691892055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107390142235041463178378813 40271303338140548691892055)
      ·
        refine ⟨60406955007210823037838083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40271303338140548691892055 60406955007210823037838083)
        ·
          refine ⟨90610432510816234556757125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60406955007210823037838083 90610432510816234556757125)
          ·
            refine ⟨16989456095778043979391961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90610432510816234556757125 16989456095778043979391961)
            ·
              refine ⟨12742092071833532984543971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16989456095778043979391961 12742092071833532984543971)
              ·
                refine ⟨19113138107750299476815957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12742092071833532984543971 19113138107750299476815957)
                ·
                  refine ⟨223982087200198821993937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19113138107750299476815957 223982087200198821993937)
                  ·
                    rfl

theorem cell23_3925832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 8].length) (baseStart_3925832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925832 prefixEnd_3925832 := by exact prefixLift 3925832
  have htrace : WordTrace (prefixWord ++ tailWord_3925832) baseStart_3925832 baseEnd_3925832 := by
    simpa [prefixWord, tailWord_3925832, baseEnd_3925832] using wordTrace_append hprefix tailTrace_3925832
  have hstable : (prefixWord ++ tailWord_3925832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925832).length < 2 ^ (prefixWord ++ tailWord_3925832).sum := by decide
  have hdescent : baseEnd_3925832 < baseStart_3925832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925893 : List Nat := [1, 3, 1, 1, 3, 2, 3, 4, 1, 1, 3]
def baseStart_3925893 : Nat := 118140960795 + 3925893 * 2 ^ 59
def prefixEnd_3925893 : Nat := 4983230072969 + 3 ^ 40 * 3925893 * 2
def baseEnd_3925893 : Nat := 2015870107121713659282653

theorem tailTrace_3925893 : CollatzResearch.WordTrace tailWord_3925893 prefixEnd_3925893 2015870107121713659282653 := by
  unfold tailWord_3925893
  simp only [CollatzResearch.WordTrace]
  refine ⟨143189081166167624989142333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95459387444111749992761555 143189081166167624989142333)
  ·
    refine ⟨53695905437312859370928375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143189081166167624989142333 53695905437312859370928375)
    ·
      refine ⟨80543858155969289056392563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53695905437312859370928375 80543858155969289056392563)
      ·
        refine ⟨120815787233953933584588845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80543858155969289056392563 120815787233953933584588845)
        ·
          refine ⟨45305920212732725094220817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120815787233953933584588845 45305920212732725094220817)
          ·
            refine ⟨33979440159549543820665613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45305920212732725094220817 33979440159549543820665613)
            ·
              refine ⟨12742290059831078932749605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33979440159549543820665613 12742290059831078932749605)
              ·
                refine ⟨2389179386218327299890551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12742290059831078932749605 2389179386218327299890551)
                ·
                  refine ⟨3583769079327490949835827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2389179386218327299890551 3583769079327490949835827)
                  ·
                    refine ⟨5375653618991236424753741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3583769079327490949835827 5375653618991236424753741)
                    ·
                      refine ⟨2015870107121713659282653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5375653618991236424753741 2015870107121713659282653)
                      ·
                        rfl

theorem cell23_3925893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 1, 1, 3].length) (baseStart_3925893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925893 prefixEnd_3925893 := by exact prefixLift 3925893
  have htrace : WordTrace (prefixWord ++ tailWord_3925893) baseStart_3925893 baseEnd_3925893 := by
    simpa [prefixWord, tailWord_3925893, baseEnd_3925893] using wordTrace_append hprefix tailTrace_3925893
  have hstable : (prefixWord ++ tailWord_3925893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925893).length < 2 ^ (prefixWord ++ tailWord_3925893).sum := by decide
  have hdescent : baseEnd_3925893 < baseStart_3925893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925899 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 2, 6, 2]
def baseStart_3925899 : Nat := 118140960795 + 3925899 * 2 ^ 59
def prefixEnd_3925899 : Nat := 4983230072969 + 3 ^ 40 * 3925899 * 2
def baseEnd_3925899 : Nat := 2015873188005640635807625

theorem tailTrace_3925899 : CollatzResearch.WordTrace tailWord_3925899 prefixEnd_3925899 2015873188005640635807625 := by
  unfold tailWord_3925899
  simp only [CollatzResearch.WordTrace]
  refine ⟨143189300004145888013860751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95459533336097258675907167 143189300004145888013860751)
  ·
    refine ⟨214783950006218832020791127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143189300004145888013860751 214783950006218832020791127)
    ·
      refine ⟨322175925009328248031186691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214783950006218832020791127 322175925009328248031186691)
      ·
        refine ⟨483263887513992372046780037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322175925009328248031186691 483263887513992372046780037)
        ·
          refine ⟨90611978908873569758771257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 483263887513992372046780037 90611978908873569758771257)
          ·
            refine ⟨67958984181655177319078443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90611978908873569758771257 67958984181655177319078443)
            ·
              refine ⟨101938476272482765978617665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67958984181655177319078443 101938476272482765978617665)
              ·
                refine ⟨76453857204362074483963249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101938476272482765978617665 76453857204362074483963249)
                ·
                  refine ⟨57340392903271555862972437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76453857204362074483963249 57340392903271555862972437)
                  ·
                    refine ⟨2687830917340854181076833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57340392903271555862972437 2687830917340854181076833)
                    ·
                      refine ⟨2015873188005640635807625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2687830917340854181076833 2015873188005640635807625)
                      ·
                        rfl

theorem cell23_3925899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 6, 2].length) (baseStart_3925899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925899 prefixEnd_3925899 := by exact prefixLift 3925899
  have htrace : WordTrace (prefixWord ++ tailWord_3925899) baseStart_3925899 baseEnd_3925899 := by
    simpa [prefixWord, tailWord_3925899, baseEnd_3925899] using wordTrace_append hprefix tailTrace_3925899
  have hstable : (prefixWord ++ tailWord_3925899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925899).length < 2 ^ (prefixWord ++ tailWord_3925899).sum := by decide
  have hdescent : baseEnd_3925899 < baseStart_3925899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925909 : List Nat := [1, 3, 2, 1, 1, 3, 4, 1, 1, 6]
def baseStart_3925909 : Nat := 118140960795 + 3925909 * 2 ^ 59
def prefixEnd_3925909 : Nat := 4983230072969 + 3 ^ 40 * 3925909 * 2
def baseEnd_3925909 : Nat := 671959440937395198894193

theorem tailTrace_3925909 : CollatzResearch.WordTrace tailWord_3925909 prefixEnd_3925909 671959440937395198894193 := by
  unfold tailWord_3925909
  simp only [CollatzResearch.WordTrace]
  refine ⟨143189664734109659721724781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95459776489406439814483187 143189664734109659721724781)
  ·
    refine ⟨53696124275291122395646793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143189664734109659721724781 53696124275291122395646793)
    ·
      refine ⟨40272093206468341796735095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53696124275291122395646793 40272093206468341796735095)
      ·
        refine ⟨60408139809702512695102643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40272093206468341796735095 60408139809702512695102643)
        ·
          refine ⟨90612209714553769042653965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60408139809702512695102643 90612209714553769042653965)
          ·
            refine ⟨33979578642957663390995237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90612209714553769042653965 33979578642957663390995237)
            ·
              refine ⟨6371170995554561885811607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33979578642957663390995237 6371170995554561885811607)
              ·
                refine ⟨9556756493331842828717411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6371170995554561885811607 9556756493331842828717411)
                ·
                  refine ⟨14335134739997764243076117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9556756493331842828717411 14335134739997764243076117)
                  ·
                    refine ⟨671959440937395198894193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14335134739997764243076117 671959440937395198894193)
                    ·
                      rfl

theorem cell23_3925909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_3925909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925909 prefixEnd_3925909 := by exact prefixLift 3925909
  have htrace : WordTrace (prefixWord ++ tailWord_3925909) baseStart_3925909 baseEnd_3925909 := by
    simpa [prefixWord, tailWord_3925909, baseEnd_3925909] using wordTrace_append hprefix tailTrace_3925909
  have hstable : (prefixWord ++ tailWord_3925909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925909).length < 2 ^ (prefixWord ++ tailWord_3925909).sum := by decide
  have hdescent : baseEnd_3925909 < baseStart_3925909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925916 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3925916 : Nat := 118140960795 + 3925916 * 2 ^ 59
def prefixEnd_3925916 : Nat := 4983230072969 + 3 ^ 40 * 3925916 * 2
def baseEnd_3925916 : Nat := 2015881917176767069295047

theorem tailTrace_3925916 : CollatzResearch.WordTrace tailWord_3925916 prefixEnd_3925916 2015881917176767069295047 := by
  unfold tailWord_3925916
  simp only [CollatzResearch.WordTrace]
  refine ⟨71594960022542149958614801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95459946696722866611486401 71594960022542149958614801)
  ·
    refine ⟨53696220016906612468961101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71594960022542149958614801 53696220016906612468961101)
    ·
      refine ⟨20136082506339979675860413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53696220016906612468961101 20136082506339979675860413)
      ·
        refine ⟨7551030939877492378447655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20136082506339979675860413 7551030939877492378447655)
        ·
          refine ⟨11326546409816238567671483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7551030939877492378447655 11326546409816238567671483)
          ·
            refine ⟨16989819614724357851507225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11326546409816238567671483 16989819614724357851507225)
            ·
              refine ⟨12742364711043268388630419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16989819614724357851507225 12742364711043268388630419)
              ·
                refine ⟨19113547066564902582945629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12742364711043268388630419 19113547066564902582945629)
                ·
                  refine ⟨7167580149961838468604611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19113547066564902582945629 7167580149961838468604611)
                  ·
                    refine ⟨10751370224942757702906917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7167580149961838468604611 10751370224942757702906917)
                    ·
                      refine ⟨2015881917176767069295047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10751370224942757702906917 2015881917176767069295047)
                      ·
                        rfl

theorem cell23_3925916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3925916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925916 prefixEnd_3925916 := by exact prefixLift 3925916
  have htrace : WordTrace (prefixWord ++ tailWord_3925916) baseStart_3925916 baseEnd_3925916 := by
    simpa [prefixWord, tailWord_3925916, baseEnd_3925916] using wordTrace_append hprefix tailTrace_3925916
  have hstable : (prefixWord ++ tailWord_3925916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925916).length < 2 ^ (prefixWord ++ tailWord_3925916).sum := by decide
  have hdescent : baseEnd_3925916 < baseStart_3925916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925950 : List Nat := [4, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2]
def baseStart_3925950 : Nat := 118140960795 + 3925950 * 2 ^ 59
def prefixEnd_3925950 : Nat := 4983230072969 + 3 ^ 40 * 3925950 * 2
def baseEnd_3925950 : Nat := 2015899375519019936269891

theorem tailTrace_3925950 : CollatzResearch.WordTrace tailWord_3925950 prefixEnd_3925950 2015899375519019936269891 := by
  unfold tailWord_3925950
  simp only [CollatzResearch.WordTrace]
  refine ⟨17898895015870140465495913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95460773417974082482644869 17898895015870140465495913)
  ·
    refine ⟨13424171261902605349121935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17898895015870140465495913 13424171261902605349121935)
    ·
      refine ⟨20136256892853908023682903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13424171261902605349121935 20136256892853908023682903)
      ·
        refine ⟨30204385339280862035524355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20136256892853908023682903 30204385339280862035524355)
        ·
          refine ⟨45306578008921293053286533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30204385339280862035524355 45306578008921293053286533)
          ·
            refine ⟨8494983376672742447491225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45306578008921293053286533 8494983376672742447491225)
            ·
              refine ⟨6371237532504556835618419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8494983376672742447491225 6371237532504556835618419)
              ·
                refine ⟨9556856298756835253427629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6371237532504556835618419 9556856298756835253427629)
                ·
                  refine ⟨3583821112033813220035361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9556856298756835253427629 3583821112033813220035361)
                  ·
                    refine ⟨2687865834025359915026521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3583821112033813220035361 2687865834025359915026521)
                    ·
                      refine ⟨2015899375519019936269891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2687865834025359915026521 2015899375519019936269891)
                      ·
                        rfl

theorem cell23_3925950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_3925950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925950 prefixEnd_3925950 := by exact prefixLift 3925950
  have htrace : WordTrace (prefixWord ++ tailWord_3925950) baseStart_3925950 baseEnd_3925950 := by
    simpa [prefixWord, tailWord_3925950, baseEnd_3925950] using wordTrace_append hprefix tailTrace_3925950
  have hstable : (prefixWord ++ tailWord_3925950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925950).length < 2 ^ (prefixWord ++ tailWord_3925950).sum := by decide
  have hdescent : baseEnd_3925950 < baseStart_3925950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925970 : List Nat := [3, 2, 2, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_3925970 : Nat := 118140960795 + 3925970 * 2 ^ 59
def prefixEnd_3925970 : Nat := 4983230072969 + 3 ^ 40 * 3925970 * 2
def baseEnd_3925970 : Nat := 2015909645132109858019799

theorem tailTrace_3925970 : CollatzResearch.WordTrace tailWord_3925970 prefixEnd_3925970 2015909645132109858019799 := by
  unfold tailWord_3925970
  simp only [CollatzResearch.WordTrace]
  refine ⟨35797972396722166784923841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95461259724592444759796909 35797972396722166784923841)
  ·
    refine ⟨26848479297541625088692881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35797972396722166784923841 26848479297541625088692881)
    ·
      refine ⟨20136359473156218816519661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26848479297541625088692881 20136359473156218816519661)
      ·
        refine ⟨7551134802433582056194873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20136359473156218816519661 7551134802433582056194873)
        ·
          refine ⟨5663351101825186542146155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7551134802433582056194873 5663351101825186542146155)
          ·
            refine ⟨8495026652737779813219233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5663351101825186542146155 8495026652737779813219233)
            ·
              refine ⟨6371269989553334859914425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8495026652737779813219233 6371269989553334859914425)
              ·
                refine ⟨4778452492165001144935819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6371269989553334859914425 4778452492165001144935819)
                ·
                  refine ⟨7167678738247501717403729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4778452492165001144935819 7167678738247501717403729)
                  ·
                    refine ⟨5375759053685626288052797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7167678738247501717403729 5375759053685626288052797)
                    ·
                      refine ⟨2015909645132109858019799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5375759053685626288052797 2015909645132109858019799)
                      ·
                        rfl

theorem cell23_3925970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_3925970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925970 prefixEnd_3925970 := by exact prefixLift 3925970
  have htrace : WordTrace (prefixWord ++ tailWord_3925970) baseStart_3925970 baseEnd_3925970 := by
    simpa [prefixWord, tailWord_3925970, baseEnd_3925970] using wordTrace_append hprefix tailTrace_3925970
  have hstable : (prefixWord ++ tailWord_3925970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925970).length < 2 ^ (prefixWord ++ tailWord_3925970).sum := by decide
  have hdescent : baseEnd_3925970 < baseStart_3925970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926019 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 4]
def baseStart_3926019 : Nat := 118140960795 + 3926019 * 2 ^ 59
def prefixEnd_3926019 : Nat := 4983230072969 + 3 ^ 40 * 3926019 * 2
def baseEnd_3926019 : Nat := 2015934805684180166307073

theorem tailTrace_3926019 : CollatzResearch.WordTrace tailWord_3926019 prefixEnd_3926019 2015934805684180166307073 := by
  unfold tailWord_3926019
  simp only [CollatzResearch.WordTrace]
  refine ⟨143193676763711148508229111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95462451175807432338819407 143193676763711148508229111)
  ·
    refine ⟨214790515145566722762343667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143193676763711148508229111 214790515145566722762343667)
    ·
      refine ⟨322185772718350084143515501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214790515145566722762343667 322185772718350084143515501)
      ·
        refine ⟨120819664769381281553818313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322185772718350084143515501 120819664769381281553818313)
        ·
          refine ⟨90614748577035961165363735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120819664769381281553818313 90614748577035961165363735)
          ·
            refine ⟨135922122865553941748045603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90614748577035961165363735 135922122865553941748045603)
            ·
              refine ⟨203883184298330912622068405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135922122865553941748045603 203883184298330912622068405)
              ·
                refine ⟨19114048527968523058318913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203883184298330912622068405 19114048527968523058318913)
                ·
                  refine ⟨14335536395976392293739185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19114048527968523058318913 14335536395976392293739185)
                  ·
                    refine ⟨10751652296982294220304389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14335536395976392293739185 10751652296982294220304389)
                    ·
                      refine ⟨2015934805684180166307073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10751652296982294220304389 2015934805684180166307073)
                      ·
                        rfl

theorem cell23_3926019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_3926019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926019 prefixEnd_3926019 := by exact prefixLift 3926019
  have htrace : WordTrace (prefixWord ++ tailWord_3926019) baseStart_3926019 baseEnd_3926019 := by
    simpa [prefixWord, tailWord_3926019, baseEnd_3926019] using wordTrace_append hprefix tailTrace_3926019
  have hstable : (prefixWord ++ tailWord_3926019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926019).length < 2 ^ (prefixWord ++ tailWord_3926019).sum := by decide
  have hdescent : baseEnd_3926019 < baseStart_3926019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926059 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 4, 5]
def baseStart_3926059 : Nat := 118140960795 + 3926059 * 2 ^ 59
def prefixEnd_3926059 : Nat := 4983230072969 + 3 ^ 40 * 3926059 * 2
def baseEnd_3926059 : Nat := 671985114970120003268963

theorem tailTrace_3926059 : CollatzResearch.WordTrace tailWord_3926059 prefixEnd_3926059 671985114970120003268963 := by
  unfold tailWord_3926059
  simp only [CollatzResearch.WordTrace]
  refine ⟨143195135683566235339685231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95463423789044156893123487 143195135683566235339685231)
  ·
    refine ⟨214792703525349353009527847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143195135683566235339685231 214792703525349353009527847)
    ·
      refine ⟨322189055288024029514291771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214792703525349353009527847 322189055288024029514291771)
      ·
        refine ⟨483283582932036044271437657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322189055288024029514291771 483283582932036044271437657)
        ·
          refine ⟨362462687199027033203578243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483283582932036044271437657 362462687199027033203578243)
          ·
            refine ⟨543694030798540549805367365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362462687199027033203578243 543694030798540549805367365)
            ·
              refine ⟨101942630774726353088506381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 543694030798540549805367365 101942630774726353088506381)
              ·
                refine ⟨38228486540522382408189893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101942630774726353088506381 38228486540522382408189893)
                ·
                  refine ⟨7167841226347946701535605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38228486540522382408189893 7167841226347946701535605)
                  ·
                    refine ⟨671985114970120003268963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7167841226347946701535605 671985114970120003268963)
                    ·
                      rfl

theorem cell23_3926059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 5].length) (baseStart_3926059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926059 prefixEnd_3926059 := by exact prefixLift 3926059
  have htrace : WordTrace (prefixWord ++ tailWord_3926059) baseStart_3926059 baseEnd_3926059 := by
    simpa [prefixWord, tailWord_3926059, baseEnd_3926059] using wordTrace_append hprefix tailTrace_3926059
  have hstable : (prefixWord ++ tailWord_3926059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926059).length < 2 ^ (prefixWord ++ tailWord_3926059).sum := by decide
  have hdescent : baseEnd_3926059 < baseStart_3926059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926073 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 2, 3, 3]
def baseStart_3926073 : Nat := 118140960795 + 3926073 * 2 ^ 59
def prefixEnd_3926073 : Nat := 4983230072969 + 3 ^ 40 * 3926073 * 2
def baseEnd_3926073 : Nat := 2015962533639522955031825

theorem tailTrace_3926073 : CollatzResearch.WordTrace tailWord_3926073 prefixEnd_3926073 2015962533639522955031825 := by
  unfold tailWord_3926073
  simp only [CollatzResearch.WordTrace]
  refine ⟨143195646305515515730694873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95463764203677010487129915 143195646305515515730694873)
  ·
    refine ⟨107396734729136636798021155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143195646305515515730694873 107396734729136636798021155)
    ·
      refine ⟨161095102093704955197031733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107396734729136636798021155 161095102093704955197031733)
      ·
        refine ⟨15102665821284839549721725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161095102093704955197031733 15102665821284839549721725)
        ·
          refine ⟨5663499682981814831145647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15102665821284839549721725 5663499682981814831145647)
          ·
            refine ⟨8495249524472722246718471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5663499682981814831145647 8495249524472722246718471)
            ·
              refine ⟨12742874286709083370077707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8495249524472722246718471 12742874286709083370077707)
              ·
                refine ⟨19114311430063625055116561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12742874286709083370077707 19114311430063625055116561)
                ·
                  refine ⟨14335733572547718791337421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19114311430063625055116561 14335733572547718791337421)
                  ·
                    refine ⟨5375900089705394546751533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14335733572547718791337421 5375900089705394546751533)
                    ·
                      refine ⟨2015962533639522955031825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5375900089705394546751533 2015962533639522955031825)
                      ·
                        rfl

theorem cell23_3926073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_3926073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926073 prefixEnd_3926073 := by exact prefixLift 3926073
  have htrace : WordTrace (prefixWord ++ tailWord_3926073) baseStart_3926073 baseEnd_3926073 := by
    simpa [prefixWord, tailWord_3926073, baseEnd_3926073] using wordTrace_append hprefix tailTrace_3926073
  have hstable : (prefixWord ++ tailWord_3926073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926073).length < 2 ^ (prefixWord ++ tailWord_3926073).sum := by decide
  have hdescent : baseEnd_3926073 < baseStart_3926073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926106 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 5, 4]
def baseStart_3926106 : Nat := 118140960795 + 3926106 * 2 ^ 59
def prefixEnd_3926106 : Nat := 4983230072969 + 3 ^ 40 * 3926106 * 2
def baseEnd_3926106 : Nat := 671993159500373775306391

theorem tailTrace_3926106 : CollatzResearch.WordTrace tailWord_3926106 prefixEnd_3926106 671993159500373775306391 := by
  unfold tailWord_3926106
  simp only [CollatzResearch.WordTrace]
  refine ⟨35799212478598990591661543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95464566609597308244430781 35799212478598990591661543)
  ·
    refine ⟨53698818717898485887492315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35799212478598990591661543 53698818717898485887492315)
    ·
      refine ⟨80548228076847728831238473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53698818717898485887492315 80548228076847728831238473)
      ·
        refine ⟨60411171057635796623428855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80548228076847728831238473 60411171057635796623428855)
        ·
          refine ⟨90616756586453694935143283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60411171057635796623428855 90616756586453694935143283)
          ·
            refine ⟨135925134879680542402714925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90616756586453694935143283 135925134879680542402714925)
            ·
              refine ⟨50971925579880203401018097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135925134879680542402714925 50971925579880203401018097)
              ·
                refine ⟨38228944184910152550763573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50971925579880203401018097 38228944184910152550763573)
                ·
                  refine ⟨3583963517335326801634085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38228944184910152550763573 3583963517335326801634085)
                  ·
                    refine ⟨671993159500373775306391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3583963517335326801634085 671993159500373775306391)
                    ·
                      rfl

theorem cell23_3926106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 5, 4].length) (baseStart_3926106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926106 prefixEnd_3926106 := by exact prefixLift 3926106
  have htrace : WordTrace (prefixWord ++ tailWord_3926106) baseStart_3926106 baseEnd_3926106 := by
    simpa [prefixWord, tailWord_3926106, baseEnd_3926106] using wordTrace_append hprefix tailTrace_3926106
  have hstable : (prefixWord ++ tailWord_3926106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926106).length < 2 ^ (prefixWord ++ tailWord_3926106).sum := by decide
  have hdescent : baseEnd_3926106 < baseStart_3926106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926126 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_3926126 : Nat := 118140960795 + 3926126 * 2 ^ 59
def prefixEnd_3926126 : Nat := 4983230072969 + 3 ^ 40 * 3926126 * 2
def baseEnd_3926126 : Nat := 2015989748114211247669081

theorem tailTrace_3926126 : CollatzResearch.WordTrace tailWord_3926126 prefixEnd_3926126 2015989748114211247669081 := by
  unfold tailWord_3926126
  simp only [CollatzResearch.WordTrace]
  refine ⟨17899697421790438222796779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95465052916215670521582821 17899697421790438222796779)
  ·
    refine ⟨26849546132685657334195169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17899697421790438222796779 26849546132685657334195169)
    ·
      refine ⟨20137159599514243000646377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26849546132685657334195169 20137159599514243000646377)
      ·
        refine ⟨15102869699635682250484783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20137159599514243000646377 15102869699635682250484783)
        ·
          refine ⟨22654304549453523375727175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15102869699635682250484783 22654304549453523375727175)
          ·
            refine ⟨33981456824180285063590763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22654304549453523375727175 33981456824180285063590763)
            ·
              refine ⟨50972185236270427595386145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33981456824180285063590763 50972185236270427595386145)
              ·
                refine ⟨38229138927202820696539609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50972185236270427595386145 38229138927202820696539609)
                ·
                  refine ⟨28671854195402115522404707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38229138927202820696539609 28671854195402115522404707)
                  ·
                    refine ⟨43007781293103173283607061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28671854195402115522404707 43007781293103173283607061)
                    ·
                      refine ⟨2015989748114211247669081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43007781293103173283607061 2015989748114211247669081)
                      ·
                        rfl

theorem cell23_3926126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_3926126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926126 prefixEnd_3926126 := by exact prefixLift 3926126
  have htrace : WordTrace (prefixWord ++ tailWord_3926126) baseStart_3926126 baseEnd_3926126 := by
    simpa [prefixWord, tailWord_3926126, baseEnd_3926126] using wordTrace_append hprefix tailTrace_3926126
  have hstable : (prefixWord ++ tailWord_3926126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926126).length < 2 ^ (prefixWord ++ tailWord_3926126).sum := by decide
  have hdescent : baseEnd_3926126 < baseStart_3926126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926174 : List Nat := [4, 3, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_3926174 : Nat := 118140960795 + 3926174 * 2 ^ 59
def prefixEnd_3926174 : Nat := 4983230072969 + 3 ^ 40 * 3926174 * 2
def baseEnd_3926174 : Nat := 672004798395209019956287

theorem tailTrace_3926174 : CollatzResearch.WordTrace tailWord_3926174 prefixEnd_3926174 672004798395209019956287 := by
  unfold tailWord_3926174
  simp only [CollatzResearch.WordTrace]
  refine ⟨17899916259768701247515197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95466220052099739986747717 17899916259768701247515197)
  ·
    refine ⟨6712468597413262967818199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17899916259768701247515197 6712468597413262967818199)
    ·
      refine ⟨10068702896119894451727299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6712468597413262967818199 10068702896119894451727299)
      ·
        refine ⟨15103054344179841677590949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10068702896119894451727299 15103054344179841677590949)
        ·
          refine ⟨2831822689533720314548303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15103054344179841677590949 2831822689533720314548303)
          ·
            refine ⟨4247734034300580471822455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831822689533720314548303 4247734034300580471822455)
            ·
              refine ⟨6371601051450870707733683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4247734034300580471822455 6371601051450870707733683)
              ·
                refine ⟨9557401577176306061600525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6371601051450870707733683 9557401577176306061600525)
                ·
                  refine ⟨3584025591441114773100197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9557401577176306061600525 3584025591441114773100197)
                  ·
                    refine ⟨672004798395209019956287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3584025591441114773100197 672004798395209019956287)
                    ·
                      rfl

theorem cell23_3926174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_3926174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926174 prefixEnd_3926174 := by exact prefixLift 3926174
  have htrace : WordTrace (prefixWord ++ tailWord_3926174) baseStart_3926174 baseEnd_3926174 := by
    simpa [prefixWord, tailWord_3926174, baseEnd_3926174] using wordTrace_append hprefix tailTrace_3926174
  have hstable : (prefixWord ++ tailWord_3926174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926174).length < 2 ^ (prefixWord ++ tailWord_3926174).sum := by decide
  have hdescent : baseEnd_3926174 < baseStart_3926174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926226 : List Nat := [3, 2, 2, 2, 1, 13]
def baseStart_3926226 : Nat := 118140960795 + 3926226 * 2 ^ 59
def prefixEnd_3926226 : Nat := 4983230072969 + 3 ^ 40 * 3926226 * 2
def baseEnd_3926226 : Nat := 8296465416377205170447

theorem tailTrace_3926226 : CollatzResearch.WordTrace tailWord_3926226 prefixEnd_3926226 8296465416377205170447 := by
  unfold tailWord_3926226
  simp only [CollatzResearch.WordTrace]
  refine ⟨35800306668490305715253633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95467484449307481907343021 35800306668490305715253633)
  ·
    refine ⟨26850230001367729286440225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35800306668490305715253633 26850230001367729286440225)
    ·
      refine ⟨20137672501025796964830169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26850230001367729286440225 20137672501025796964830169)
      ·
        refine ⟨15103254375769347723622627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20137672501025796964830169 15103254375769347723622627)
        ·
          refine ⟨22654881563654021585433941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15103254375769347723622627 22654881563654021585433941)
          ·
            refine ⟨8296465416377205170447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 22654881563654021585433941 8296465416377205170447)
            ·
              rfl

theorem cell23_3926226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 13].length) (baseStart_3926226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926226 prefixEnd_3926226 := by exact prefixLift 3926226
  have htrace : WordTrace (prefixWord ++ tailWord_3926226) baseStart_3926226 baseEnd_3926226 := by
    simpa [prefixWord, tailWord_3926226, baseEnd_3926226] using wordTrace_append hprefix tailTrace_3926226
  have hstable : (prefixWord ++ tailWord_3926226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926226).length < 2 ^ (prefixWord ++ tailWord_3926226).sum := by decide
  have hdescent : baseEnd_3926226 < baseStart_3926226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926270 : List Nat := [4, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_3926270 : Nat := 118140960795 + 3926270 * 2 ^ 59
def prefixEnd_3926270 : Nat := 4983230072969 + 3 ^ 40 * 3926270 * 2
def baseEnd_3926270 : Nat := 2016063689328458684268419

theorem tailTrace_3926270 : CollatzResearch.WordTrace tailWord_3926270 prefixEnd_3926270 2016063689328458684268419 := by
  unfold tailWord_3926270
  simp only [CollatzResearch.WordTrace]
  refine ⟨17900353935725227296952033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95468554323867878917077509 17900353935725227296952033)
  ·
    refine ⟨13425265451793920472714025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17900353935725227296952033 13425265451793920472714025)
    ·
      refine ⟨10068949088845440354535519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13425265451793920472714025 10068949088845440354535519)
      ·
        refine ⟨15103423633268160531803279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10068949088845440354535519 15103423633268160531803279)
        ·
          refine ⟨22655135449902240797704919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15103423633268160531803279 22655135449902240797704919)
          ·
            refine ⟨33982703174853361196557379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22655135449902240797704919 33982703174853361196557379)
            ·
              refine ⟨50974054762280041794836069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33982703174853361196557379 50974054762280041794836069)
              ·
                refine ⟨9557635267927507836531763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50974054762280041794836069 9557635267927507836531763)
                ·
                  refine ⟨14336452901891261754797645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9557635267927507836531763 14336452901891261754797645)
                  ·
                    refine ⟨5376169838209223158049117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14336452901891261754797645 5376169838209223158049117)
                    ·
                      refine ⟨2016063689328458684268419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5376169838209223158049117 2016063689328458684268419)
                      ·
                        rfl

theorem cell23_3926270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_3926270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926270 prefixEnd_3926270 := by exact prefixLift 3926270
  have htrace : WordTrace (prefixWord ++ tailWord_3926270) baseStart_3926270 baseEnd_3926270 := by
    simpa [prefixWord, tailWord_3926270, baseEnd_3926270] using wordTrace_append hprefix tailTrace_3926270
  have hstable : (prefixWord ++ tailWord_3926270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926270).length < 2 ^ (prefixWord ++ tailWord_3926270).sum := by decide
  have hdescent : baseEnd_3926270 < baseStart_3926270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926274 : List Nat := [3, 4, 1, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_3926274 : Nat := 118140960795 + 3926274 * 2 ^ 59
def prefixEnd_3926274 : Nat := 4983230072969 + 3 ^ 40 * 3926274 * 2
def baseEnd_3926274 : Nat := 2016065743251076668618401

theorem tailTrace_3926274 : CollatzResearch.WordTrace tailWord_3926274 prefixEnd_3926274 2016065743251076668618401 := by
  unfold tailWord_3926274
  simp only [CollatzResearch.WordTrace]
  refine ⟨35800744344446831764690469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95468651585191551372507917 35800744344446831764690469)
  ·
    refine ⟨6712639564583780955879463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35800744344446831764690469 6712639564583780955879463)
    ·
      refine ⟨10068959346875671433819195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6712639564583780955879463 10068959346875671433819195)
      ·
        refine ⟨15103439020313507150728793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10068959346875671433819195 15103439020313507150728793)
        ·
          refine ⟨11327579265235130363046595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15103439020313507150728793 11327579265235130363046595)
          ·
            refine ⟨16991368897852695544569893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11327579265235130363046595 16991368897852695544569893)
            ·
              refine ⟨3185881668347380414606855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16991368897852695544569893 3185881668347380414606855)
              ·
                refine ⟨4778822502521070621910283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3185881668347380414606855 4778822502521070621910283)
                ·
                  refine ⟨7168233753781605932865425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4778822502521070621910283 7168233753781605932865425)
                  ·
                    refine ⟨5376175315336204449649069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7168233753781605932865425 5376175315336204449649069)
                    ·
                      refine ⟨2016065743251076668618401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5376175315336204449649069 2016065743251076668618401)
                      ·
                        rfl

theorem cell23_3926274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_3926274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926274 prefixEnd_3926274 := by exact prefixLift 3926274
  have htrace : WordTrace (prefixWord ++ tailWord_3926274) baseStart_3926274 baseEnd_3926274 := by
    simpa [prefixWord, tailWord_3926274, baseEnd_3926274] using wordTrace_append hprefix tailTrace_3926274
  have hstable : (prefixWord ++ tailWord_3926274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926274).length < 2 ^ (prefixWord ++ tailWord_3926274).sum := by decide
  have hdescent : baseEnd_3926274 < baseStart_3926274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926303 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 2, 6]
def baseStart_3926303 : Nat := 118140960795 + 3926303 * 2 ^ 59
def prefixEnd_3926303 : Nat := 4983230072969 + 3 ^ 40 * 3926303 * 2
def baseEnd_3926303 : Nat := 672026878063352351718589

theorem tailTrace_3926303 : CollatzResearch.WordTrace tailWord_3926303 prefixEnd_3926303 672026878063352351718589 := by
  unfold tailWord_3926303
  simp only [CollatzResearch.WordTrace]
  refine ⟨143204035094682265011567563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95469356729788176674378375 143204035094682265011567563)
  ·
    refine ⟨214806052642023397517351345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143204035094682265011567563 214806052642023397517351345)
    ·
      refine ⟨161104539481517548138013509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214806052642023397517351345 161104539481517548138013509)
      ·
        refine ⟨30207101152784540275877533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161104539481517548138013509 30207101152784540275877533)
        ·
          refine ⟨11327662932294202603454075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30207101152784540275877533 11327662932294202603454075)
          ·
            refine ⟨16991494398441303905181113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11327662932294202603454075 16991494398441303905181113)
            ·
              refine ⟨12743620798830977928885835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16991494398441303905181113 12743620798830977928885835)
              ·
                refine ⟨19115431198246466893328753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12743620798830977928885835 19115431198246466893328753)
                ·
                  refine ⟨14336573398684850169996565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19115431198246466893328753 14336573398684850169996565)
                  ·
                    refine ⟨672026878063352351718589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14336573398684850169996565 672026878063352351718589)
                    ·
                      rfl

theorem cell23_3926303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 6].length) (baseStart_3926303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926303 prefixEnd_3926303 := by exact prefixLift 3926303
  have htrace : WordTrace (prefixWord ++ tailWord_3926303) baseStart_3926303 baseEnd_3926303 := by
    simpa [prefixWord, tailWord_3926303, baseEnd_3926303] using wordTrace_append hprefix tailTrace_3926303
  have hstable : (prefixWord ++ tailWord_3926303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926303).length < 2 ^ (prefixWord ++ tailWord_3926303).sum := by decide
  have hdescent : baseEnd_3926303 < baseStart_3926303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926304 : List Nat := [2, 1, 1, 5, 2, 2, 3, 1, 2, 1, 3]
def baseStart_3926304 : Nat := 118140960795 + 3926304 * 2 ^ 59
def prefixEnd_3926304 : Nat := 4983230072969 + 3 ^ 40 * 3926304 * 2
def baseEnd_3926304 : Nat := 2016081147670711551243263

theorem tailTrace_3926304 : CollatzResearch.WordTrace tailWord_3926304 prefixEnd_3926304 2016081147670711551243263 := by
  unfold tailWord_3926304
  simp only [CollatzResearch.WordTrace]
  refine ⟨71602035783839321091176983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95469381045119094788235977 71602035783839321091176983)
  ·
    refine ⟨107403053675758981636765475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71602035783839321091176983 107403053675758981636765475)
    ·
      refine ⟨161104580513638472455148213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107403053675758981636765475 161104580513638472455148213)
      ·
        refine ⟨15103554423153606792670145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161104580513638472455148213 15103554423153606792670145)
        ·
          refine ⟨11327665817365205094502609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15103554423153606792670145 11327665817365205094502609)
          ·
            refine ⟨8495749363023903820876957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11327665817365205094502609 8495749363023903820876957)
            ·
              refine ⟨3185906011133963932828859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8495749363023903820876957 3185906011133963932828859)
              ·
                refine ⟨4778859016700945899243289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3185906011133963932828859 4778859016700945899243289)
                ·
                  refine ⟨3584144262525709424432467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4778859016700945899243289 3584144262525709424432467)
                  ·
                    refine ⟨5376216393788564136648701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3584144262525709424432467 5376216393788564136648701)
                    ·
                      refine ⟨2016081147670711551243263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5376216393788564136648701 2016081147670711551243263)
                      ·
                        rfl

theorem cell23_3926304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_3926304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926304 prefixEnd_3926304 := by exact prefixLift 3926304
  have htrace : WordTrace (prefixWord ++ tailWord_3926304) baseStart_3926304 baseEnd_3926304 := by
    simpa [prefixWord, tailWord_3926304, baseEnd_3926304] using wordTrace_append hprefix tailTrace_3926304
  have hstable : (prefixWord ++ tailWord_3926304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926304).length < 2 ^ (prefixWord ++ tailWord_3926304).sum := by decide
  have hdescent : baseEnd_3926304 < baseStart_3926304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926311 : List Nat := [1, 1, 8, 1, 2, 1, 2, 7]
def baseStart_3926311 : Nat := 118140960795 + 3926311 * 2 ^ 59
def prefixEnd_3926311 : Nat := 4983230072969 + 3 ^ 40 * 3926311 * 2
def baseEnd_3926311 : Nat := 74669805260566408290953

theorem tailTrace_3926311 : CollatzResearch.WordTrace tailWord_3926311 prefixEnd_3926311 74669805260566408290953 := by
  unfold tailWord_3926311
  simp only [CollatzResearch.WordTrace]
  refine ⟨143204326878653282377858787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95469551252435521585239191 143204326878653282377858787)
  ·
    refine ⟨214806490317979923566788181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143204326878653282377858787 214806490317979923566788181)
    ·
      refine ⟨2517263558413827229298299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 214806490317979923566788181 2517263558413827229298299)
      ·
        refine ⟨3775895337620740843947449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2517263558413827229298299 3775895337620740843947449)
        ·
          refine ⟨2831921503215555632960587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3775895337620740843947449 2831921503215555632960587)
          ·
            refine ⟨4247882254823333449440881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831921503215555632960587 4247882254823333449440881)
            ·
              refine ⟨3185911691117500087080661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4247882254823333449440881 3185911691117500087080661)
              ·
                refine ⟨74669805260566408290953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3185911691117500087080661 74669805260566408290953)
                ·
                  rfl

theorem cell23_3926311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 7].length) (baseStart_3926311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926311 prefixEnd_3926311 := by exact prefixLift 3926311
  have htrace : WordTrace (prefixWord ++ tailWord_3926311) baseStart_3926311 baseEnd_3926311 := by
    simpa [prefixWord, tailWord_3926311, baseEnd_3926311] using wordTrace_append hprefix tailTrace_3926311
  have hstable : (prefixWord ++ tailWord_3926311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926311).length < 2 ^ (prefixWord ++ tailWord_3926311).sum := by decide
  have hdescent : baseEnd_3926311 < baseStart_3926311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926457 : List Nat := [1, 2, 1, 4, 3, 3, 1, 2, 6]
def baseStart_3926457 : Nat := 118140960795 + 3926457 * 2 ^ 59
def prefixEnd_3926457 : Nat := 4983230072969 + 3 ^ 40 * 3926457 * 2
def baseEnd_3926457 : Nat := 224017745578983272514451

theorem tailTrace_3926457 : CollatzResearch.WordTrace tailWord_3926457 prefixEnd_3926457 224017745578983272514451 := by
  unfold tailWord_3926457
  simp only [CollatzResearch.WordTrace]
  refine ⟨143209651936124349312673625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95473101290749566208449083 143209651936124349312673625)
  ·
    refine ⟨107407238952093261984505219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143209651936124349312673625 107407238952093261984505219)
    ·
      refine ⟨161110858428139892976757829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107407238952093261984505219 161110858428139892976757829)
      ·
        refine ⟨30208285955276229933142093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161110858428139892976757829 30208285955276229933142093)
        ·
          refine ⟨11328107233228586224928285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30208285955276229933142093 11328107233228586224928285)
          ·
            refine ⟨4248040212460719834348107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11328107233228586224928285 4248040212460719834348107)
            ·
              refine ⟨6372060318691079751522161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4248040212460719834348107 6372060318691079751522161)
              ·
                refine ⟨4779045239018309813641621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6372060318691079751522161 4779045239018309813641621)
                ·
                  refine ⟨224017745578983272514451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4779045239018309813641621 224017745578983272514451)
                  ·
                    rfl

theorem cell23_3926457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 6].length) (baseStart_3926457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926457 prefixEnd_3926457 := by exact prefixLift 3926457
  have htrace : WordTrace (prefixWord ++ tailWord_3926457) baseStart_3926457 baseEnd_3926457 := by
    simpa [prefixWord, tailWord_3926457, baseEnd_3926457] using wordTrace_append hprefix tailTrace_3926457
  have hstable : (prefixWord ++ tailWord_3926457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926457).length < 2 ^ (prefixWord ++ tailWord_3926457).sum := by decide
  have hdescent : baseEnd_3926457 < baseStart_3926457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926460 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3926460 : Nat := 118140960795 + 3926460 * 2 ^ 59
def prefixEnd_3926460 : Nat := 4983230072969 + 3 ^ 40 * 3926460 * 2
def baseEnd_3926460 : Nat := 2016161250652812940892545

theorem tailTrace_3926460 : CollatzResearch.WordTrace tailWord_3926460 prefixEnd_3926460 2016161250652812940892545 := by
  unfold tailWord_3926460
  simp only [CollatzResearch.WordTrace]
  refine ⟨71604880677556740412516417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95473174236742320550021889 71604880677556740412516417)
  ·
    refine ⟨53703660508167555309387313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71604880677556740412516417 53703660508167555309387313)
    ·
      refine ⟨40277745381125666482040485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53703660508167555309387313 40277745381125666482040485)
      ·
        refine ⟨7552077258961062465382591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40277745381125666482040485 7552077258961062465382591)
        ·
          refine ⟨11328115888441593698073887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7552077258961062465382591 11328115888441593698073887)
          ·
            refine ⟨16992173832662390547110831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11328115888441593698073887 16992173832662390547110831)
            ·
              refine ⟨25488260748993585820666247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16992173832662390547110831 25488260748993585820666247)
              ·
                refine ⟨38232391123490378730999371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25488260748993585820666247 38232391123490378730999371)
                ·
                  refine ⟨57348586685235568096499057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38232391123490378730999371 57348586685235568096499057)
                  ·
                    refine ⟨43011440013926676072374293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57348586685235568096499057 43011440013926676072374293)
                    ·
                      refine ⟨2016161250652812940892545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43011440013926676072374293 2016161250652812940892545)
                      ·
                        rfl

theorem cell23_3926460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3926460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926460 prefixEnd_3926460 := by exact prefixLift 3926460
  have htrace : WordTrace (prefixWord ++ tailWord_3926460) baseStart_3926460 baseEnd_3926460 := by
    simpa [prefixWord, tailWord_3926460, baseEnd_3926460] using wordTrace_append hprefix tailTrace_3926460
  have hstable : (prefixWord ++ tailWord_3926460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926460).length < 2 ^ (prefixWord ++ tailWord_3926460).sum := by decide
  have hdescent : baseEnd_3926460 < baseStart_3926460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926484 : List Nat := [2, 4, 1, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_3926484 : Nat := 118140960795 + 3926484 * 2 ^ 59
def prefixEnd_3926484 : Nat := 4983230072969 + 3 ^ 40 * 3926484 * 2
def baseEnd_3926484 : Nat := 2016173574188520846992435

theorem tailTrace_3926484 : CollatzResearch.WordTrace tailWord_3926484 prefixEnd_3926484 2016173574188520846992435 := by
  unfold tailWord_3926484
  simp only [CollatzResearch.WordTrace]
  refine ⟨71605318353513266461953253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95473757804684355282604337 71605318353513266461953253)
  ·
    refine ⟨13425997191283737461616235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71605318353513266461953253 13425997191283737461616235)
    ·
      refine ⟨20138995786925606192424353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13425997191283737461616235 20138995786925606192424353)
      ·
        refine ⟨15104246840194204644318265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20138995786925606192424353 15104246840194204644318265)
        ·
          refine ⟨11328185130145653483238699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15104246840194204644318265 11328185130145653483238699)
          ·
            refine ⟨16992277695218480224858049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11328185130145653483238699 16992277695218480224858049)
            ·
              refine ⟨12744208271413860168643537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16992277695218480224858049 12744208271413860168643537)
              ·
                refine ⟨9558156203560395126482653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12744208271413860168643537 9558156203560395126482653)
                ·
                  refine ⟨3584308576335148172430995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9558156203560395126482653 3584308576335148172430995)
                  ·
                    refine ⟨5376462864502722258646493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3584308576335148172430995 5376462864502722258646493)
                    ·
                      refine ⟨2016173574188520846992435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5376462864502722258646493 2016173574188520846992435)
                      ·
                        rfl

theorem cell23_3926484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_3926484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926484 prefixEnd_3926484 := by exact prefixLift 3926484
  have htrace : WordTrace (prefixWord ++ tailWord_3926484) baseStart_3926484 baseEnd_3926484 := by
    simpa [prefixWord, tailWord_3926484, baseEnd_3926484] using wordTrace_append hprefix tailTrace_3926484
  have hstable : (prefixWord ++ tailWord_3926484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926484).length < 2 ^ (prefixWord ++ tailWord_3926484).sum := by decide
  have hdescent : baseEnd_3926484 < baseStart_3926484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926518 : List Nat := [5, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3]
def baseStart_3926518 : Nat := 118140960795 + 3926518 * 2 ^ 59
def prefixEnd_3926518 : Nat := 4983230072969 + 3 ^ 40 * 3926518 * 2
def baseEnd_3926518 : Nat := 2016191032530773713967279

theorem tailTrace_3926518 : CollatzResearch.WordTrace tailWord_3926518 prefixEnd_3926518 2016191032530773713967279 := by
  unfold tailWord_3926518
  simp only [CollatzResearch.WordTrace]
  refine ⟨8950742299306459795665263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95474584525935571153762805 8950742299306459795665263)
  ·
    refine ⟨13426113448959689693497895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8950742299306459795665263 13426113448959689693497895)
    ·
      refine ⟨20139170173439534540246843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13426113448959689693497895 20139170173439534540246843)
      ·
        refine ⟨30208755260159301810370265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20139170173439534540246843 30208755260159301810370265)
        ·
          refine ⟨22656566445119476357777699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30208755260159301810370265 22656566445119476357777699)
          ·
            refine ⟨33984849667679214536666549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22656566445119476357777699 33984849667679214536666549)
            ·
              refine ⟨3186079656344926362812489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33984849667679214536666549 3186079656344926362812489)
              ·
                refine ⟨2389559742258694772109367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3186079656344926362812489 2389559742258694772109367)
                ·
                  refine ⟨3584339613388042158164051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2389559742258694772109367 3584339613388042158164051)
                  ·
                    refine ⟨5376509420082063237246077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3584339613388042158164051 5376509420082063237246077)
                    ·
                      refine ⟨2016191032530773713967279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5376509420082063237246077 2016191032530773713967279)
                      ·
                        rfl

theorem cell23_3926518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_3926518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926518 prefixEnd_3926518 := by exact prefixLift 3926518
  have htrace : WordTrace (prefixWord ++ tailWord_3926518) baseStart_3926518 baseEnd_3926518 := by
    simpa [prefixWord, tailWord_3926518, baseEnd_3926518] using wordTrace_append hprefix tailTrace_3926518
  have hstable : (prefixWord ++ tailWord_3926518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926518).length < 2 ^ (prefixWord ++ tailWord_3926518).sum := by decide
  have hdescent : baseEnd_3926518 < baseStart_3926518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926523 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 7]
def baseStart_3926523 : Nat := 118140960795 + 3926523 * 2 ^ 59
def prefixEnd_3926523 : Nat := 4983230072969 + 3 ^ 40 * 3926523 * 2
def baseEnd_3926523 : Nat := 2016193599934046194404755

theorem tailTrace_3926523 : CollatzResearch.WordTrace tailWord_3926523 prefixEnd_3926523 2016193599934046194404755 := by
  unfold tailWord_3926523
  simp only [CollatzResearch.WordTrace]
  refine ⟨143212059153885242584576223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95474706102590161723050815 143212059153885242584576223)
  ·
    refine ⟨214818088730827863876864335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143212059153885242584576223 214818088730827863876864335)
    ·
      refine ⟨322227133096241795815296503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214818088730827863876864335 322227133096241795815296503)
      ·
        refine ⟨483340699644362693722944755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322227133096241795815296503 483340699644362693722944755)
        ·
          refine ⟨725011049466544040584417133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483340699644362693722944755 725011049466544040584417133)
          ·
            refine ⟨271879143549954015219156425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 725011049466544040584417133 271879143549954015219156425)
            ·
              refine ⟨203909357662465511414367319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271879143549954015219156425 203909357662465511414367319)
              ·
                refine ⟨305864036493698267121550979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203909357662465511414367319 305864036493698267121550979)
                ·
                  refine ⟨458796054740547400682326469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305864036493698267121550979 458796054740547400682326469)
                  ·
                    refine ⟨86024260263852637627936213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 458796054740547400682326469 86024260263852637627936213)
                    ·
                      refine ⟨2016193599934046194404755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86024260263852637627936213 2016193599934046194404755)
                      ·
                        rfl

theorem cell23_3926523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 7].length) (baseStart_3926523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926523 prefixEnd_3926523 := by exact prefixLift 3926523
  have htrace : WordTrace (prefixWord ++ tailWord_3926523) baseStart_3926523 baseEnd_3926523 := by
    simpa [prefixWord, tailWord_3926523, baseEnd_3926523] using wordTrace_append hprefix tailTrace_3926523
  have hstable : (prefixWord ++ tailWord_3926523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926523).length < 2 ^ (prefixWord ++ tailWord_3926523).sum := by decide
  have hdescent : baseEnd_3926523 < baseStart_3926523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926541 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_3926541 : Nat := 118140960795 + 3926541 * 2 ^ 59
def prefixEnd_3926541 : Nat := 4983230072969 + 3 ^ 40 * 3926541 * 2
def baseEnd_3926541 : Nat := 2016202842585827123979673

theorem tailTrace_3926541 : CollatzResearch.WordTrace tailWord_3926541 prefixEnd_3926541 2016202842585827123979673 := by
  unfold tailWord_3926541
  simp only [CollatzResearch.WordTrace]
  refine ⟨143212715667820031658731477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95475143778546687772487651 143212715667820031658731477)
  ·
    refine ⟨3356548023464531992001519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 143212715667820031658731477 3356548023464531992001519)
    ·
      refine ⟨5034822035196797988002279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3356548023464531992001519 5034822035196797988002279)
      ·
        refine ⟨7552233052795196982003419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5034822035196797988002279 7552233052795196982003419)
        ·
          refine ⟨11328349579192795473005129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7552233052795196982003419 11328349579192795473005129)
          ·
            refine ⟨8496262184394596604753847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11328349579192795473005129 8496262184394596604753847)
            ·
              refine ⟨12744393276591894907130771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8496262184394596604753847 12744393276591894907130771)
              ·
                refine ⟨19116589914887842360696157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12744393276591894907130771 19116589914887842360696157)
                ·
                  refine ⟨7168721218082940885261059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19116589914887842360696157 7168721218082940885261059)
                  ·
                    refine ⟨10753081827124411327891589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7168721218082940885261059 10753081827124411327891589)
                    ·
                      refine ⟨2016202842585827123979673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10753081827124411327891589 2016202842585827123979673)
                      ·
                        rfl

theorem cell23_3926541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_3926541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926541 prefixEnd_3926541 := by exact prefixLift 3926541
  have htrace : WordTrace (prefixWord ++ tailWord_3926541) baseStart_3926541 baseEnd_3926541 := by
    simpa [prefixWord, tailWord_3926541, baseEnd_3926541] using wordTrace_append hprefix tailTrace_3926541
  have hstable : (prefixWord ++ tailWord_3926541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926541).length < 2 ^ (prefixWord ++ tailWord_3926541).sum := by decide
  have hdescent : baseEnd_3926541 < baseStart_3926541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926557 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_3926557 : Nat := 118140960795 + 3926557 * 2 ^ 59
def prefixEnd_3926557 : Nat := 4983230072969 + 3 ^ 40 * 3926557 * 2
def baseEnd_3926557 : Nat := 2016211058276299061379599

theorem tailTrace_3926557 : CollatzResearch.WordTrace tailWord_3926557 prefixEnd_3926557 2016211058276299061379599 := by
  unfold tailWord_3926557
  simp only [CollatzResearch.WordTrace]
  refine ⟨143213299235762066391313925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95475532823841377594209283 143213299235762066391313925)
  ·
    refine ⟨26852493606705387448371361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143213299235762066391313925 26852493606705387448371361)
    ·
      refine ⟨20139370205029040586278521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26852493606705387448371361 20139370205029040586278521)
      ·
        refine ⟨15104527653771780439708891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20139370205029040586278521 15104527653771780439708891)
        ·
          refine ⟨22656791480657670659563337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15104527653771780439708891 22656791480657670659563337)
          ·
            refine ⟨16992593610493252994672503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22656791480657670659563337 16992593610493252994672503)
            ·
              refine ⟨25488890415739879492008755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16992593610493252994672503 25488890415739879492008755)
              ·
                refine ⟨38233335623609819238013133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25488890415739879492008755 38233335623609819238013133)
                ·
                  refine ⟨14337500858853682214254925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38233335623609819238013133 14337500858853682214254925)
                  ·
                    refine ⟨5376562822070130830345597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14337500858853682214254925 5376562822070130830345597)
                    ·
                      refine ⟨2016211058276299061379599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5376562822070130830345597 2016211058276299061379599)
                      ·
                        rfl

theorem cell23_3926557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_3926557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926557 prefixEnd_3926557 := by exact prefixLift 3926557
  have htrace : WordTrace (prefixWord ++ tailWord_3926557) baseStart_3926557 baseEnd_3926557 := by
    simpa [prefixWord, tailWord_3926557, baseEnd_3926557] using wordTrace_append hprefix tailTrace_3926557
  have hstable : (prefixWord ++ tailWord_3926557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926557).length < 2 ^ (prefixWord ++ tailWord_3926557).sum := by decide
  have hdescent : baseEnd_3926557 < baseStart_3926557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926600 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_3926600 : Nat := 118140960795 + 3926600 * 2 ^ 59
def prefixEnd_3926600 : Nat := 4983230072969 + 3 ^ 40 * 3926600 * 2
def baseEnd_3926600 : Nat := 2016233137944442393141901

theorem tailTrace_3926600 : CollatzResearch.WordTrace tailWord_3926600 prefixEnd_3926600 2016233137944442393141901 := by
  unfold tailWord_3926600
  simp only [CollatzResearch.WordTrace]
  refine ⟨71607433787303142367564627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95476578383070856490086169 71607433787303142367564627)
  ·
    refine ⟨107411150680954713551346941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71607433787303142367564627 107411150680954713551346941)
    ·
      refine ⟨40279181505358017581755103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107411150680954713551346941 40279181505358017581755103)
      ·
        refine ⟨60418772258037026372632655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40279181505358017581755103 60418772258037026372632655)
        ·
          refine ⟨90628158387055539558948983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60418772258037026372632655 90628158387055539558948983)
          ·
            refine ⟨135942237580583309338423475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90628158387055539558948983 135942237580583309338423475)
            ·
              refine ⟨203913356370874964007635213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135942237580583309338423475 203913356370874964007635213)
              ·
                refine ⟨76467508639078111502863205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203913356370874964007635213 76467508639078111502863205)
                ·
                  refine ⟨14337657869827145906786851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76467508639078111502863205 14337657869827145906786851)
                  ·
                    refine ⟨21506486804740718860180277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14337657869827145906786851 21506486804740718860180277)
                    ·
                      refine ⟨2016233137944442393141901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21506486804740718860180277 2016233137944442393141901)
                      ·
                        rfl

theorem cell23_3926600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_3926600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926600 prefixEnd_3926600 := by exact prefixLift 3926600
  have htrace : WordTrace (prefixWord ++ tailWord_3926600) baseStart_3926600 baseEnd_3926600 := by
    simpa [prefixWord, tailWord_3926600, baseEnd_3926600] using wordTrace_append hprefix tailTrace_3926600
  have hstable : (prefixWord ++ tailWord_3926600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926600).length < 2 ^ (prefixWord ++ tailWord_3926600).sum := by decide
  have hdescent : baseEnd_3926600 < baseStart_3926600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926637 : List Nat := [1, 5, 1, 1, 3, 1, 1, 3, 7]
def baseStart_3926637 : Nat := 118140960795 + 3926637 * 2 ^ 59
def prefixEnd_3926637 : Nat := 4983230072969 + 3 ^ 40 * 3926637 * 2
def baseEnd_3926637 : Nat := 224028015192073194264359

theorem tailTrace_3926637 : CollatzResearch.WordTrace tailWord_3926637 prefixEnd_3926637 224028015192073194264359 := by
  unfold tailWord_3926637
  simp only [CollatzResearch.WordTrace]
  refine ⟨143216217075472240054226165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95477478050314826702817443 143216217075472240054226165)
  ·
    refine ⟨13426520350825522505083703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143216217075472240054226165 13426520350825522505083703)
    ·
      refine ⟨20139780526238283757625555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13426520350825522505083703 20139780526238283757625555)
      ·
        refine ⟨30209670789357425636438333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20139780526238283757625555 30209670789357425636438333)
        ·
          refine ⟨11328626546009034613664375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30209670789357425636438333 11328626546009034613664375)
          ·
            refine ⟨16992939819013551920496563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11328626546009034613664375 16992939819013551920496563)
            ·
              refine ⟨25489409728520327880744845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16992939819013551920496563 25489409728520327880744845)
              ·
                refine ⟨9558528648195122955279317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25489409728520327880744845 9558528648195122955279317)
                ·
                  refine ⟨224028015192073194264359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9558528648195122955279317 224028015192073194264359)
                  ·
                    rfl

theorem cell23_3926637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_3926637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926637 prefixEnd_3926637 := by exact prefixLift 3926637
  have htrace : WordTrace (prefixWord ++ tailWord_3926637) baseStart_3926637 baseEnd_3926637 := by
    simpa [prefixWord, tailWord_3926637, baseEnd_3926637] using wordTrace_append hprefix tailTrace_3926637
  have hstable : (prefixWord ++ tailWord_3926637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926637).length < 2 ^ (prefixWord ++ tailWord_3926637).sum := by decide
  have hdescent : baseEnd_3926637 < baseStart_3926637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926647 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 3]
def baseStart_3926647 : Nat := 118140960795 + 3926647 * 2 ^ 59
def prefixEnd_3926647 : Nat := 4983230072969 + 3 ^ 40 * 3926647 * 2
def baseEnd_3926647 : Nat := 2016257271535203709254185

theorem tailTrace_3926647 : CollatzResearch.WordTrace tailWord_3926647 prefixEnd_3926647 2016257271535203709254185 := by
  unfold tailWord_3926647
  simp only [CollatzResearch.WordTrace]
  refine ⟨143216581805436011762090195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95477721203624007841393463 143216581805436011762090195)
  ·
    refine ⟨214824872708154017643135293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143216581805436011762090195 214824872708154017643135293)
    ·
      refine ⟨80559327265557756616175735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214824872708154017643135293 80559327265557756616175735)
      ·
        refine ⟨120838990898336634924263603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80559327265557756616175735 120838990898336634924263603)
        ·
          refine ⟨181258486347504952386395405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120838990898336634924263603 181258486347504952386395405)
          ·
            refine ⟨67971932380314357144898277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181258486347504952386395405 67971932380314357144898277)
            ·
              refine ⟨12744737321308941964668427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67971932380314357144898277 12744737321308941964668427)
              ·
                refine ⟨19117105981963412947002641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12744737321308941964668427 19117105981963412947002641)
                ·
                  refine ⟨14337829486472559710251981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19117105981963412947002641 14337829486472559710251981)
                  ·
                    refine ⟨5376686057427209891344493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14337829486472559710251981 5376686057427209891344493)
                    ·
                      refine ⟨2016257271535203709254185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5376686057427209891344493 2016257271535203709254185)
                      ·
                        rfl

theorem cell23_3926647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_3926647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926647 prefixEnd_3926647 := by exact prefixLift 3926647
  have htrace : WordTrace (prefixWord ++ tailWord_3926647) baseStart_3926647 baseEnd_3926647 := by
    simpa [prefixWord, tailWord_3926647, baseEnd_3926647] using wordTrace_append hprefix tailTrace_3926647
  have hstable : (prefixWord ++ tailWord_3926647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926647).length < 2 ^ (prefixWord ++ tailWord_3926647).sum := by decide
  have hdescent : baseEnd_3926647 < baseStart_3926647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926684 : List Nat := [2, 2, 3, 2, 2, 2, 1, 2, 2, 5]
def baseStart_3926684 : Nat := 118140960795 + 3926684 * 2 ^ 59
def prefixEnd_3926684 : Nat := 4983230072969 + 3 ^ 40 * 3926684 * 2
def baseEnd_3926684 : Nat := 672092090106473354830505

theorem tailTrace_3926684 : CollatzResearch.WordTrace tailWord_3926684 prefixEnd_3926684 672092090106473354830505 := by
  unfold tailWord_3926684
  simp only [CollatzResearch.WordTrace]
  refine ⟨71608965653150983540593553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95478620870867978054124737 71608965653150983540593553)
  ·
    refine ⟨53706724239863237655445165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71608965653150983540593553 53706724239863237655445165)
    ·
      refine ⟨20140021589948714120791937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53706724239863237655445165 20140021589948714120791937)
      ·
        refine ⟨15105016192461535590593953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20140021589948714120791937 15105016192461535590593953)
        ·
          refine ⟨11328762144346151692945465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15105016192461535590593953 11328762144346151692945465)
          ·
            refine ⟨8496571608259613769709099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11328762144346151692945465 8496571608259613769709099)
            ·
              refine ⟨12744857412389420654563649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8496571608259613769709099 12744857412389420654563649)
              ·
                refine ⟨9558643059292065490922737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12744857412389420654563649 9558643059292065490922737)
                ·
                  refine ⟨7168982294469049118192053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9558643059292065490922737 7168982294469049118192053)
                  ·
                    refine ⟨672092090106473354830505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7168982294469049118192053 672092090106473354830505)
                    ·
                      rfl

theorem cell23_3926684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_3926684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926684 prefixEnd_3926684 := by exact prefixLift 3926684
  have htrace : WordTrace (prefixWord ++ tailWord_3926684) baseStart_3926684 baseEnd_3926684 := by
    simpa [prefixWord, tailWord_3926684, baseEnd_3926684] using wordTrace_append hprefix tailTrace_3926684
  have hstable : (prefixWord ++ tailWord_3926684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926684).length < 2 ^ (prefixWord ++ tailWord_3926684).sum := by decide
  have hdescent : baseEnd_3926684 < baseStart_3926684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926744 : List Nat := [2, 1, 2, 2, 3, 3, 2, 2, 6]
def baseStart_3926744 : Nat := 118140960795 + 3926744 * 2 ^ 59
def prefixEnd_3926744 : Nat := 4983230072969 + 3 ^ 40 * 3926744 * 2
def baseEnd_3926744 : Nat := 224034119906521092193471

theorem tailTrace_3926744 : CollatzResearch.WordTrace tailWord_3926744 prefixEnd_3926744 224034119906521092193471 := by
  unfold tailWord_3926744
  simp only [CollatzResearch.WordTrace]
  refine ⟨71610059843042298664185643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95480079790723064885580857 71610059843042298664185643)
  ·
    refine ⟨107415089764563447996278465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71610059843042298664185643 107415089764563447996278465)
    ·
      refine ⟨80561317323422585997208849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107415089764563447996278465 80561317323422585997208849)
      ·
        refine ⟨60420987992566939497906637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80561317323422585997208849 60420987992566939497906637)
        ·
          refine ⟨22657870497212602311714989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60420987992566939497906637 22657870497212602311714989)
          ·
            refine ⟨8496701436454725866893121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22657870497212602311714989 8496701436454725866893121)
            ·
              refine ⟨6372526077341044400169841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8496701436454725866893121 6372526077341044400169841)
              ·
                refine ⟨4779394558005783300127381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6372526077341044400169841 4779394558005783300127381)
                ·
                  refine ⟨224034119906521092193471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4779394558005783300127381 224034119906521092193471)
                  ·
                    rfl

theorem cell23_3926744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 6].length) (baseStart_3926744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926744 prefixEnd_3926744 := by exact prefixLift 3926744
  have htrace : WordTrace (prefixWord ++ tailWord_3926744) baseStart_3926744 baseEnd_3926744 := by
    simpa [prefixWord, tailWord_3926744, baseEnd_3926744] using wordTrace_append hprefix tailTrace_3926744
  have hstable : (prefixWord ++ tailWord_3926744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926744).length < 2 ^ (prefixWord ++ tailWord_3926744).sum := by decide
  have hdescent : baseEnd_3926744 < baseStart_3926744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926764 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 1, 5, 2]
def baseStart_3926764 : Nat := 118140960795 + 3926764 * 2 ^ 59
def prefixEnd_3926764 : Nat := 4983230072969 + 3 ^ 40 * 3926764 * 2
def baseEnd_3926764 : Nat := 2016317348771779751491147

theorem tailTrace_3926764 : CollatzResearch.WordTrace tailWord_3926764 prefixEnd_3926764 2016317348771779751491147 := by
  unfold tailWord_3926764
  simp only [CollatzResearch.WordTrace]
  refine ⟨71610424573006070372049673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95480566097341427162732897 71610424573006070372049673)
  ·
    refine ⟨53707818429754552779037255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71610424573006070372049673 53707818429754552779037255)
    ·
      refine ⟨80561727644631829168555883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53707818429754552779037255 80561727644631829168555883)
      ·
        refine ⟨120842591466947743752833825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80561727644631829168555883 120842591466947743752833825)
        ·
          refine ⟨90631943600210807814625369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120842591466947743752833825 90631943600210807814625369)
          ·
            refine ⟨67973957700158105860969027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90631943600210807814625369 67973957700158105860969027)
            ·
              refine ⟨101960936550237158791453541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67973957700158105860969027 101960936550237158791453541)
              ·
                refine ⟨19117675603169467273397539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101960936550237158791453541 19117675603169467273397539)
                ·
                  refine ⟨28676513404754200910096309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19117675603169467273397539 28676513404754200910096309)
                  ·
                    refine ⟨2688423131695706335321529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28676513404754200910096309 2688423131695706335321529)
                    ·
                      refine ⟨2016317348771779751491147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2688423131695706335321529 2016317348771779751491147)
                      ·
                        rfl

theorem cell23_3926764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 5, 2].length) (baseStart_3926764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926764 prefixEnd_3926764 := by exact prefixLift 3926764
  have htrace : WordTrace (prefixWord ++ tailWord_3926764) baseStart_3926764 baseEnd_3926764 := by
    simpa [prefixWord, tailWord_3926764, baseEnd_3926764] using wordTrace_append hprefix tailTrace_3926764
  have hstable : (prefixWord ++ tailWord_3926764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926764).length < 2 ^ (prefixWord ++ tailWord_3926764).sum := by decide
  have hdescent : baseEnd_3926764 < baseStart_3926764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926772 : List Nat := [2, 6, 1, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_3926772 : Nat := 118140960795 + 3926772 * 2 ^ 59
def prefixEnd_3926772 : Nat := 4983230072969 + 3 ^ 40 * 3926772 * 2
def baseEnd_3926772 : Nat := 2016321456617015720191111

theorem tailTrace_3926772 : CollatzResearch.WordTrace tailWord_3926772 prefixEnd_3926772 2016321456617015720191111 := by
  unfold tailWord_3926772
  simp only [CollatzResearch.WordTrace]
  refine ⟨71610570464991579055195285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95480760619988772073593713 71610570464991579055195285)
  ·
    refine ⟨3356745490546480268212279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71610570464991579055195285 3356745490546480268212279)
    ·
      refine ⟨5035118235819720402318419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3356745490546480268212279 5035118235819720402318419)
      ·
        refine ⟨7552677353729580603477629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5035118235819720402318419 7552677353729580603477629)
        ·
          refine ⟨2832254007648592726304111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7552677353729580603477629 2832254007648592726304111)
          ·
            refine ⟨4248381011472889089456167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2832254007648592726304111 4248381011472889089456167)
            ·
              refine ⟨6372571517209333634184251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4248381011472889089456167 6372571517209333634184251)
              ·
                refine ⟨9558857275814000451276377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6372571517209333634184251 9558857275814000451276377)
                ·
                  refine ⟨7169142956860500338457283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9558857275814000451276377 7169142956860500338457283)
                  ·
                    refine ⟨10753714435290750507685925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7169142956860500338457283 10753714435290750507685925)
                    ·
                      refine ⟨2016321456617015720191111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10753714435290750507685925 2016321456617015720191111)
                      ·
                        rfl

theorem cell23_3926772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_3926772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926772 prefixEnd_3926772 := by exact prefixLift 3926772
  have htrace : WordTrace (prefixWord ++ tailWord_3926772) baseStart_3926772 baseEnd_3926772 := by
    simpa [prefixWord, tailWord_3926772, baseEnd_3926772] using wordTrace_append hprefix tailTrace_3926772
  have hstable : (prefixWord ++ tailWord_3926772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926772).length < 2 ^ (prefixWord ++ tailWord_3926772).sum := by decide
  have hdescent : baseEnd_3926772 < baseStart_3926772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926774 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_3926774 : Nat := 118140960795 + 3926774 * 2 ^ 59
def prefixEnd_3926774 : Nat := 4983230072969 + 3 ^ 40 * 3926774 * 2
def baseEnd_3926774 : Nat := 672107494526108237455367

theorem tailTrace_3926774 : CollatzResearch.WordTrace tailWord_3926774 prefixEnd_3926774 672107494526108237455367 := by
  unfold tailWord_3926774
  simp only [CollatzResearch.WordTrace]
  refine ⟨8951325867248494528247711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95480809250650608301308917 8951325867248494528247711)
  ·
    refine ⟨13426988800872741792371567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8951325867248494528247711 13426988800872741792371567)
    ·
      refine ⟨20140483201309112688557351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13426988800872741792371567 20140483201309112688557351)
      ·
        refine ⟨30210724801963669032836027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20140483201309112688557351 30210724801963669032836027)
        ·
          refine ⟨45316087202945503549254041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30210724801963669032836027 45316087202945503549254041)
          ·
            refine ⟨33987065402209127661940531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45316087202945503549254041 33987065402209127661940531)
            ·
              refine ⟨50980598103313691492910797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33987065402209127661940531 50980598103313691492910797)
              ·
                refine ⟨19117724288742634309841549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50980598103313691492910797 19117724288742634309841549)
                ·
                  refine ⟨7169146608278487866190581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19117724288742634309841549 7169146608278487866190581)
                  ·
                    refine ⟨672107494526108237455367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7169146608278487866190581 672107494526108237455367)
                    ·
                      rfl

theorem cell23_3926774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_3926774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926774 prefixEnd_3926774 := by exact prefixLift 3926774
  have htrace : WordTrace (prefixWord ++ tailWord_3926774) baseStart_3926774 baseEnd_3926774 := by
    simpa [prefixWord, tailWord_3926774, baseEnd_3926774] using wordTrace_append hprefix tailTrace_3926774
  have hstable : (prefixWord ++ tailWord_3926774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926774).length < 2 ^ (prefixWord ++ tailWord_3926774).sum := by decide
  have hdescent : baseEnd_3926774 < baseStart_3926774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926791 : List Nat := [1, 1, 4, 4, 1, 2, 1, 3, 1, 5]
def baseStart_3926791 : Nat := 118140960795 + 3926791 * 2 ^ 59
def prefixEnd_3926791 : Nat := 4983230072969 + 3 ^ 40 * 3926791 * 2
def baseEnd_3926791 : Nat := 672110404249817048617841

theorem tailTrace_3926791 : CollatzResearch.WordTrace tailWord_3926791 prefixEnd_3926791 672110404249817048617841 := by
  unfold tailWord_3926791
  simp only [CollatzResearch.WordTrace]
  refine ⟨143221833916914324355332227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95481222611276216236888151 143221833916914324355332227)
  ·
    refine ⟨214832750875371486532998341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143221833916914324355332227 214832750875371486532998341)
    ·
      refine ⟨40281140789132153724937189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214832750875371486532998341 40281140789132153724937189)
      ·
        refine ⟨7552713897962278823425723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40281140789132153724937189 7552713897962278823425723)
        ·
          refine ⟨11329070846943418235138585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7552713897962278823425723 11329070846943418235138585)
          ·
            refine ⟨8496803135207563676353939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11329070846943418235138585 8496803135207563676353939)
            ·
              refine ⟨12745204702811345514530909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8496803135207563676353939 12745204702811345514530909)
              ·
                refine ⟨4779451763554254567949091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12745204702811345514530909 4779451763554254567949091)
                ·
                  refine ⟨7169177645331381851923637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4779451763554254567949091 7169177645331381851923637)
                  ·
                    refine ⟨672110404249817048617841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7169177645331381851923637 672110404249817048617841)
                    ·
                      rfl

theorem cell23_3926791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_3926791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926791 prefixEnd_3926791 := by exact prefixLift 3926791
  have htrace : WordTrace (prefixWord ++ tailWord_3926791) baseStart_3926791 baseEnd_3926791 := by
    simpa [prefixWord, tailWord_3926791, baseEnd_3926791] using wordTrace_append hprefix tailTrace_3926791
  have hstable : (prefixWord ++ tailWord_3926791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926791).length < 2 ^ (prefixWord ++ tailWord_3926791).sum := by decide
  have hdescent : baseEnd_3926791 < baseStart_3926791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926817 : List Nat := [1, 2, 3, 2, 1, 2, 2, 10]
def baseStart_3926817 : Nat := 118140960795 + 3926817 * 2 ^ 59
def prefixEnd_3926817 : Nat := 4983230072969 + 3 ^ 40 * 3926817 * 2
def baseEnd_3926817 : Nat := 74679428268387705338089

theorem tailTrace_3926817 : CollatzResearch.WordTrace tailWord_3926817 prefixEnd_3926817 74679428268387705338089 := by
  unfold tailWord_3926817
  simp only [CollatzResearch.WordTrace]
  refine ⟨143222782214820130795778705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95481854809880087197185803 143222782214820130795778705)
  ·
    refine ⟨107417086661115098096834029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143222782214820130795778705 107417086661115098096834029)
    ·
      refine ⟨40281407497918161786312761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107417086661115098096834029 40281407497918161786312761)
      ·
        refine ⟨30211055623438621339734571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40281407497918161786312761 30211055623438621339734571)
        ·
          refine ⟨45316583435157932009601857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30211055623438621339734571 45316583435157932009601857)
          ·
            refine ⟨33987437576368449007201393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45316583435157932009601857 33987437576368449007201393)
            ·
              refine ⟨25490578182276336755401045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33987437576368449007201393 25490578182276336755401045)
              ·
                refine ⟨74679428268387705338089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25490578182276336755401045 74679428268387705338089)
                ·
                  rfl

theorem cell23_3926817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 10].length) (baseStart_3926817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926817 prefixEnd_3926817 := by exact prefixLift 3926817
  have htrace : WordTrace (prefixWord ++ tailWord_3926817) baseStart_3926817 baseEnd_3926817 := by
    simpa [prefixWord, tailWord_3926817, baseEnd_3926817] using wordTrace_append hprefix tailTrace_3926817
  have hstable : (prefixWord ++ tailWord_3926817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926817).length < 2 ^ (prefixWord ++ tailWord_3926817).sum := by decide
  have hdescent : baseEnd_3926817 < baseStart_3926817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926824 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_3926824 : Nat := 118140960795 + 3926824 * 2 ^ 59
def prefixEnd_3926824 : Nat := 4983230072969 + 3 ^ 40 * 3926824 * 2
def baseEnd_3926824 : Nat := 2016348157611049516740871

theorem tailTrace_3926824 : CollatzResearch.WordTrace tailWord_3926824 prefixEnd_3926824 2016348157611049516740871 := by
  unfold tailWord_3926824
  simp only [CollatzResearch.WordTrace]
  refine ⟨71611518762897385495641763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95482025017196513994189017 71611518762897385495641763)
  ·
    refine ⟨107417278144346078243462645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71611518762897385495641763 107417278144346078243462645)
    ·
      refine ⟨10070369826032444835324623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107417278144346078243462645 10070369826032444835324623)
      ·
        refine ⟨15105554739048667252986935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10070369826032444835324623 15105554739048667252986935)
        ·
          refine ⟨22658332108573000879480403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15105554739048667252986935 22658332108573000879480403)
          ·
            refine ⟨33987498162859501319220605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22658332108573000879480403 33987498162859501319220605)
            ·
              refine ⟨12745311811072312994707727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33987498162859501319220605 12745311811072312994707727)
              ·
                refine ⟨19117967716608469492061591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12745311811072312994707727 19117967716608469492061591)
                ·
                  refine ⟨28676951574912704238092387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19117967716608469492061591 28676951574912704238092387)
                  ·
                    refine ⟨43015427362369056357138581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28676951574912704238092387 43015427362369056357138581)
                    ·
                      refine ⟨2016348157611049516740871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43015427362369056357138581 2016348157611049516740871)
                      ·
                        rfl

theorem cell23_3926824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_3926824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926824 prefixEnd_3926824 := by exact prefixLift 3926824
  have htrace : WordTrace (prefixWord ++ tailWord_3926824) baseStart_3926824 baseEnd_3926824 := by
    simpa [prefixWord, tailWord_3926824, baseEnd_3926824] using wordTrace_append hprefix tailTrace_3926824
  have hstable : (prefixWord ++ tailWord_3926824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926824).length < 2 ^ (prefixWord ++ tailWord_3926824).sum := by decide
  have hdescent : baseEnd_3926824 < baseStart_3926824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926844 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 3, 3, 3]
def baseStart_3926844 : Nat := 118140960795 + 3926844 * 2 ^ 59
def prefixEnd_3926844 : Nat := 4983230072969 + 3 ^ 40 * 3926844 * 2
def baseEnd_3926844 : Nat := 2016358427224139438490779

theorem tailTrace_3926844 : CollatzResearch.WordTrace tailWord_3926844 prefixEnd_3926844 2016358427224139438490779 := by
  unfold tailWord_3926844
  simp only [CollatzResearch.WordTrace]
  refine ⟨71611883492861157203505793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95482511323814876271341057 71611883492861157203505793)
  ·
    refine ⟨53708912619645867902629345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71611883492861157203505793 53708912619645867902629345)
    ·
      refine ⟨40281684464734400926972009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53708912619645867902629345 40281684464734400926972009)
      ·
        refine ⟨30211263348550800695229007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40281684464734400926972009 30211263348550800695229007)
        ·
          refine ⟨45316895022826201042843511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30211263348550800695229007 45316895022826201042843511)
          ·
            refine ⟨67975342534239301564265267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45316895022826201042843511 67975342534239301564265267)
            ·
              refine ⟨101963013801358952346397901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67975342534239301564265267 101963013801358952346397901)
              ·
                refine ⟨38236130175509607129899213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101963013801358952346397901 38236130175509607129899213)
                ·
                  refine ⟨14338548815816102673712205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38236130175509607129899213 14338548815816102673712205)
                  ·
                    refine ⟨5376955805931038502642077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14338548815816102673712205 5376955805931038502642077)
                    ·
                      refine ⟨2016358427224139438490779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5376955805931038502642077 2016358427224139438490779)
                      ·
                        rfl

theorem cell23_3926844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_3926844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926844 prefixEnd_3926844 := by exact prefixLift 3926844
  have htrace : WordTrace (prefixWord ++ tailWord_3926844) baseStart_3926844 baseEnd_3926844 := by
    simpa [prefixWord, tailWord_3926844, baseEnd_3926844] using wordTrace_append hprefix tailTrace_3926844
  have hstable : (prefixWord ++ tailWord_3926844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926844).length < 2 ^ (prefixWord ++ tailWord_3926844).sum := by decide
  have hdescent : baseEnd_3926844 < baseStart_3926844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926882 : List Nat := [3, 3, 2, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_3926882 : Nat := 118140960795 + 3926882 * 2 ^ 59
def prefixEnd_3926882 : Nat := 4983230072969 + 3 ^ 40 * 3926882 * 2
def baseEnd_3926882 : Nat := 2016377939489010289815605

theorem tailTrace_3926882 : CollatzResearch.WordTrace tailWord_3926882 prefixEnd_3926882 2016377939489010289815605 := by
  unfold tailWord_3926882
  simp only [CollatzResearch.WordTrace]
  refine ⟨35806288239896161724223725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95483435306389764597929933 35806288239896161724223725)
  ·
    refine ⟨13427358089961060646583897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35806288239896161724223725 13427358089961060646583897)
    ·
      refine ⟨10070518567470795484937923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13427358089961060646583897 10070518567470795484937923)
      ·
        refine ⟨15105777851206193227406885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10070518567470795484937923 15105777851206193227406885)
        ·
          refine ⟨2832333347101161230138791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15105777851206193227406885 2832333347101161230138791)
          ·
            refine ⟨4248500020651741845208187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2832333347101161230138791 4248500020651741845208187)
            ·
              refine ⟨6372750030977612767812281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4248500020651741845208187 6372750030977612767812281)
              ·
                refine ⟨4779562523233209575859211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6372750030977612767812281 4779562523233209575859211)
                ·
                  refine ⟨7169343784849814363788817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4779562523233209575859211 7169343784849814363788817)
                  ·
                    refine ⟨5377007838637360772841613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7169343784849814363788817 5377007838637360772841613)
                    ·
                      refine ⟨2016377939489010289815605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5377007838637360772841613 2016377939489010289815605)
                      ·
                        rfl

theorem cell23_3926882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_3926882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926882 prefixEnd_3926882 := by exact prefixLift 3926882
  have htrace : WordTrace (prefixWord ++ tailWord_3926882) baseStart_3926882 baseEnd_3926882 := by
    simpa [prefixWord, tailWord_3926882, baseEnd_3926882] using wordTrace_append hprefix tailTrace_3926882
  have hstable : (prefixWord ++ tailWord_3926882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926882).length < 2 ^ (prefixWord ++ tailWord_3926882).sum := by decide
  have hdescent : baseEnd_3926882 < baseStart_3926882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926888 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 3, 3, 2]
def baseStart_3926888 : Nat := 118140960795 + 3926888 * 2 ^ 59
def prefixEnd_3926888 : Nat := 4983230072969 + 3 ^ 40 * 3926888 * 2
def baseEnd_3926888 : Nat := 2016381020372937266340577

theorem tailTrace_3926888 : CollatzResearch.WordTrace tailWord_3926888 prefixEnd_3926888 2016381020372937266340577 := by
  unfold tailWord_3926888
  simp only [CollatzResearch.WordTrace]
  refine ⟨71612685898781454960806659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95483581198375273281075545 71612685898781454960806659)
  ·
    refine ⟨107419028848172182441209989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71612685898781454960806659 107419028848172182441209989)
    ·
      refine ⟨20141067909032284207726873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107419028848172182441209989 20141067909032284207726873)
      ·
        refine ⟨15105800931774213155795155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20141067909032284207726873 15105800931774213155795155)
        ·
          refine ⟨22658701397661319733692733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15105800931774213155795155 22658701397661319733692733)
          ·
            refine ⟨8497013024122994900134775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22658701397661319733692733 8497013024122994900134775)
            ·
              refine ⟨12745519536184492350202163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8497013024122994900134775 12745519536184492350202163)
              ·
                refine ⟨19118279304276738525303245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12745519536184492350202163 19118279304276738525303245)
                ·
                  refine ⟨7169354739103776946988717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19118279304276738525303245 7169354739103776946988717)
                  ·
                    refine ⟨2688508027163916355120769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7169354739103776946988717 2688508027163916355120769)
                    ·
                      refine ⟨2016381020372937266340577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2688508027163916355120769 2016381020372937266340577)
                      ·
                        rfl

theorem cell23_3926888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_3926888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926888 prefixEnd_3926888 := by exact prefixLift 3926888
  have htrace : WordTrace (prefixWord ++ tailWord_3926888) baseStart_3926888 baseEnd_3926888 := by
    simpa [prefixWord, tailWord_3926888, baseEnd_3926888] using wordTrace_append hprefix tailTrace_3926888
  have hstable : (prefixWord ++ tailWord_3926888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926888).length < 2 ^ (prefixWord ++ tailWord_3926888).sum := by decide
  have hdescent : baseEnd_3926888 < baseStart_3926888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3926905 : List Nat := [1, 2, 1, 3, 2, 4, 3, 1, 1, 3, 2]
def baseStart_3926905 : Nat := 118140960795 + 3926905 * 2 ^ 59
def prefixEnd_3926905 : Nat := 4983230072969 + 3 ^ 40 * 3926905 * 2
def baseEnd_3926905 : Nat := 2016389749544063699827999

theorem tailTrace_3926905 : CollatzResearch.WordTrace tailWord_3926905 prefixEnd_3926905 2016389749544063699827999 := by
  unfold tailWord_3926905
  simp only [CollatzResearch.WordTrace]
  refine ⟨143225991838501321824982169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95483994559000881216654779 143225991838501321824982169)
  ·
    refine ⟨107419493878875991368736627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143225991838501321824982169 107419493878875991368736627)
    ·
      refine ⟨161129240818313987053104941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107419493878875991368736627 161129240818313987053104941)
      ·
        refine ⟨60423465306867745144914353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161129240818313987053104941 60423465306867745144914353)
        ·
          refine ⟨45317598980150808858685765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60423465306867745144914353 45317598980150808858685765)
          ·
            refine ⟨8497049808778276661003581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45317598980150808858685765 8497049808778276661003581)
            ·
              refine ⟨3186393678291853747876343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8497049808778276661003581 3186393678291853747876343)
              ·
                refine ⟨4779590517437780621814515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3186393678291853747876343 4779590517437780621814515)
                ·
                  refine ⟨7169385776156670932721773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4779590517437780621814515 7169385776156670932721773)
                  ·
                    refine ⟨2688519666058751599770665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7169385776156670932721773 2688519666058751599770665)
                    ·
                      refine ⟨2016389749544063699827999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2688519666058751599770665 2016389749544063699827999)
                      ·
                        rfl

theorem cell23_3926905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_3926905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3926905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3926905 prefixEnd_3926905 := by exact prefixLift 3926905
  have htrace : WordTrace (prefixWord ++ tailWord_3926905) baseStart_3926905 baseEnd_3926905 := by
    simpa [prefixWord, tailWord_3926905, baseEnd_3926905] using wordTrace_append hprefix tailTrace_3926905
  have hstable : (prefixWord ++ tailWord_3926905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3926905).length < 2 ^ (prefixWord ++ tailWord_3926905).sum := by decide
  have hdescent : baseEnd_3926905 < baseStart_3926905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3926905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927011 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 3]
def baseStart_3927011 : Nat := 118140960795 + 3927011 * 2 ^ 59
def prefixEnd_3927011 : Nat := 4983230072969 + 3 ^ 40 * 3927011 * 2
def baseEnd_3927011 : Nat := 2016444178493440285102511

theorem tailTrace_3927011 : CollatzResearch.WordTrace tailWord_3927011 prefixEnd_3927011 2016444178493440285102511 := by
  unfold tailWord_3927011
  simp only [CollatzResearch.WordTrace]
  refine ⟨143229857976117301928340887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95486571984078201285560591 143229857976117301928340887)
  ·
    refine ⟨214844786964175952892511331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143229857976117301928340887 214844786964175952892511331)
    ·
      refine ⟨322267180446263929338766997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214844786964175952892511331 322267180446263929338766997)
      ·
        refine ⟨15106274083418621687754703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 322267180446263929338766997 15106274083418621687754703)
        ·
          refine ⟨22659411125127932531632055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15106274083418621687754703 22659411125127932531632055)
          ·
            refine ⟨33989116687691898797448083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22659411125127932531632055 33989116687691898797448083)
            ·
              refine ⟨50983675031537848196172125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33989116687691898797448083 50983675031537848196172125)
              ·
                refine ⟨19118878136826693073564547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50983675031537848196172125 19118878136826693073564547)
                ·
                  refine ⟨28678317205240039610346821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19118878136826693073564547 28678317205240039610346821)
                  ·
                    refine ⟨5377184475982507426940029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28678317205240039610346821 5377184475982507426940029)
                    ·
                      refine ⟨2016444178493440285102511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5377184475982507426940029 2016444178493440285102511)
                      ·
                        rfl

theorem cell23_3927011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_3927011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927011 prefixEnd_3927011 := by exact prefixLift 3927011
  have htrace : WordTrace (prefixWord ++ tailWord_3927011) baseStart_3927011 baseEnd_3927011 := by
    simpa [prefixWord, tailWord_3927011, baseEnd_3927011] using wordTrace_append hprefix tailTrace_3927011
  have hstable : (prefixWord ++ tailWord_3927011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927011).length < 2 ^ (prefixWord ++ tailWord_3927011).sum := by decide
  have hdescent : baseEnd_3927011 < baseStart_3927011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927034 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8]
def baseStart_3927034 : Nat := 118140960795 + 3927034 * 2 ^ 59
def prefixEnd_3927034 : Nat := 4983230072969 + 3 ^ 40 * 3927034 * 2
def baseEnd_3927034 : Nat := 2016455988548493695114905

theorem tailTrace_3927034 : CollatzResearch.WordTrace tailWord_3927034 prefixEnd_3927034 2016455988548493695114905 := by
  unfold tailWord_3927034
  simp only [CollatzResearch.WordTrace]
  refine ⟨35807674213758494214107039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95487131236689317904285437 35807674213758494214107039)
  ·
    refine ⟨53711511320637741321160559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35807674213758494214107039 53711511320637741321160559)
    ·
      refine ⟨80567266980956611981740839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53711511320637741321160559 80567266980956611981740839)
      ·
        refine ⟨120850900471434917972611259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80567266980956611981740839 120850900471434917972611259)
        ·
          refine ⟨181276350707152376958916889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120850900471434917972611259 181276350707152376958916889)
          ·
            refine ⟨135957263030364282719187667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181276350707152376958916889 135957263030364282719187667)
            ·
              refine ⟨203935894545546424078781501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135957263030364282719187667 203935894545546424078781501)
              ·
                refine ⟨76475960454579909029543063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203935894545546424078781501 76475960454579909029543063)
                ·
                  refine ⟨114713940681869863544314595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76475960454579909029543063 114713940681869863544314595)
                  ·
                    refine ⟨172070911022804795316471893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114713940681869863544314595 172070911022804795316471893)
                    ·
                      refine ⟨2016455988548493695114905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 172070911022804795316471893 2016455988548493695114905)
                      ·
                        rfl

theorem cell23_3927034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_3927034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927034 prefixEnd_3927034 := by exact prefixLift 3927034
  have htrace : WordTrace (prefixWord ++ tailWord_3927034) baseStart_3927034 baseEnd_3927034 := by
    simpa [prefixWord, tailWord_3927034, baseEnd_3927034] using wordTrace_append hprefix tailTrace_3927034
  have hstable : (prefixWord ++ tailWord_3927034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927034).length < 2 ^ (prefixWord ++ tailWord_3927034).sum := by decide
  have hdescent : baseEnd_3927034 < baseStart_3927034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927048 : List Nat := [2, 1, 3, 2, 1, 3, 4, 1, 6]
def baseStart_3927048 : Nat := 118140960795 + 3927048 * 2 ^ 59
def prefixEnd_3927048 : Nat := 4983230072969 + 3 ^ 40 * 3927048 * 2
def baseEnd_3927048 : Nat := 224051464141961848926649

theorem tailTrace_3927048 : CollatzResearch.WordTrace tailWord_3927048 prefixEnd_3927048 224051464141961848926649 := by
  unfold tailWord_3927048
  simp only [CollatzResearch.WordTrace]
  refine ⟨71615603738491628623718899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95487471651322171498291865 71615603738491628623718899)
  ·
    refine ⟨107423405607737442935578349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71615603738491628623718899 107423405607737442935578349)
    ·
      refine ⟨40283777102901541100841881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107423405607737442935578349 40283777102901541100841881)
      ·
        refine ⟨30212832827176155825631411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40283777102901541100841881 30212832827176155825631411)
        ·
          refine ⟨45319249240764233738447117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30212832827176155825631411 45319249240764233738447117)
          ·
            refine ⟨16994718465286587651917669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45319249240764233738447117 16994718465286587651917669)
            ·
              refine ⟨3186509712241235184734563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16994718465286587651917669 3186509712241235184734563)
              ·
                refine ⟨4779764568361852777101845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3186509712241235184734563 4779764568361852777101845)
                ·
                  refine ⟨224051464141961848926649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4779764568361852777101845 224051464141961848926649)
                  ·
                    rfl

theorem cell23_3927048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 6].length) (baseStart_3927048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927048 prefixEnd_3927048 := by exact prefixLift 3927048
  have htrace : WordTrace (prefixWord ++ tailWord_3927048) baseStart_3927048 baseEnd_3927048 := by
    simpa [prefixWord, tailWord_3927048, baseEnd_3927048] using wordTrace_append hprefix tailTrace_3927048
  have hstable : (prefixWord ++ tailWord_3927048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927048).length < 2 ^ (prefixWord ++ tailWord_3927048).sum := by decide
  have hdescent : baseEnd_3927048 < baseStart_3927048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927118 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3]
def baseStart_3927118 : Nat := 118140960795 + 3927118 * 2 ^ 59
def prefixEnd_3927118 : Nat := 4983230072969 + 3 ^ 40 * 3927118 * 2
def baseEnd_3927118 : Nat := 2016499120923471366464519

theorem tailTrace_3927118 : CollatzResearch.WordTrace tailWord_3927118 prefixEnd_3927118 2016499120923471366464519 := by
  unfold tailWord_3927118
  simp only [CollatzResearch.WordTrace]
  refine ⟨17904220073341207400310751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95489173724486439468324005 17904220073341207400310751)
  ·
    refine ⟨26856330110011811100466127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17904220073341207400310751 26856330110011811100466127)
    ·
      refine ⟨40284495165017716650699191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26856330110011811100466127 40284495165017716650699191)
      ·
        refine ⟨60426742747526574976048787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40284495165017716650699191 60426742747526574976048787)
        ·
          refine ⟨90640114121289862464073181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60426742747526574976048787 90640114121289862464073181)
          ·
            refine ⟨33990042795483698424027443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90640114121289862464073181 33990042795483698424027443)
            ·
              refine ⟨50985064193225547636041165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33990042795483698424027443 50985064193225547636041165)
              ·
                refine ⟨19119399072459580363515437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50985064193225547636041165 19119399072459580363515437)
                ·
                  refine ⟨7169774652172342636318289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19119399072459580363515437 7169774652172342636318289)
                  ·
                    refine ⟨5377330989129256977238717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7169774652172342636318289 5377330989129256977238717)
                    ·
                      refine ⟨2016499120923471366464519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5377330989129256977238717 2016499120923471366464519)
                      ·
                        rfl

theorem cell23_3927118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_3927118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927118 prefixEnd_3927118 := by exact prefixLift 3927118
  have htrace : WordTrace (prefixWord ++ tailWord_3927118) baseStart_3927118 baseEnd_3927118 := by
    simpa [prefixWord, tailWord_3927118, baseEnd_3927118] using wordTrace_append hprefix tailTrace_3927118
  have hstable : (prefixWord ++ tailWord_3927118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927118).length < 2 ^ (prefixWord ++ tailWord_3927118).sum := by decide
  have hdescent : baseEnd_3927118 < baseStart_3927118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927138 : List Nat := [3, 3, 2, 2, 1, 2, 10]
def baseStart_3927138 : Nat := 118140960795 + 3927138 * 2 ^ 59
def prefixEnd_3927138 : Nat := 4983230072969 + 3 ^ 40 * 3927138 * 2
def baseEnd_3927138 : Nat := 24895177660945201089067

theorem tailTrace_3927138 : CollatzResearch.WordTrace tailWord_3927138 prefixEnd_3927138 24895177660945201089067 := by
  unfold tailWord_3927138
  simp only [CollatzResearch.WordTrace]
  refine ⟨35808622511664300654553517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95489660031104801745476045 35808622511664300654553517)
  ·
    refine ⟨13428233441874112745457569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35808622511664300654553517 13428233441874112745457569)
    ·
      refine ⟨10071175081405584559093177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13428233441874112745457569 10071175081405584559093177)
      ·
        refine ⟨7553381311054188419319883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10071175081405584559093177 7553381311054188419319883)
        ·
          refine ⟨11330071966581282628979825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7553381311054188419319883 11330071966581282628979825)
          ·
            refine ⟨8497553974935961971734869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11330071966581282628979825 8497553974935961971734869)
            ·
              refine ⟨24895177660945201089067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8497553974935961971734869 24895177660945201089067)
              ·
                rfl

theorem cell23_3927138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 10].length) (baseStart_3927138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927138 prefixEnd_3927138 := by exact prefixLift 3927138
  have htrace : WordTrace (prefixWord ++ tailWord_3927138) baseStart_3927138 baseEnd_3927138 := by
    simpa [prefixWord, tailWord_3927138, baseEnd_3927138] using wordTrace_append hprefix tailTrace_3927138
  have hstable : (prefixWord ++ tailWord_3927138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927138).length < 2 ^ (prefixWord ++ tailWord_3927138).sum := by decide
  have hdescent : baseEnd_3927138 < baseStart_3927138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927149 : List Nat := [1, 5, 1, 1, 2, 2, 2, 4, 1, 2, 2]
def baseStart_3927149 : Nat := 118140960795 + 3927149 * 2 ^ 59
def prefixEnd_3927149 : Nat := 4983230072969 + 3 ^ 40 * 3927149 * 2
def baseEnd_3927149 : Nat := 2016515038823760745176877

theorem tailTrace_3927149 : CollatzResearch.WordTrace tailWord_3927149 prefixEnd_3927149 2016515038823760745176877 := by
  unfold tailWord_3927149
  simp only [CollatzResearch.WordTrace]
  refine ⟨143234891249617351496864501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95489927499744900997909667 143234891249617351496864501)
  ·
    refine ⟨13428271054651626702831047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143234891249617351496864501 13428271054651626702831047)
    ·
      refine ⟨20142406581977440054246571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13428271054651626702831047 20142406581977440054246571)
      ·
        refine ⟨30213609872966160081369857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20142406581977440054246571 30213609872966160081369857)
        ·
          refine ⟨22660207404724620061027393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30213609872966160081369857 22660207404724620061027393)
          ·
            refine ⟨16995155553543465045770545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22660207404724620061027393 16995155553543465045770545)
            ·
              refine ⟨12746366665157598784327909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16995155553543465045770545 12746366665157598784327909)
              ·
                refine ⟨2389943749717049772061483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12746366665157598784327909 2389943749717049772061483)
                ·
                  refine ⟨3584915624575574658092225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2389943749717049772061483 3584915624575574658092225)
                  ·
                    refine ⟨2688686718431680993569169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3584915624575574658092225 2688686718431680993569169)
                    ·
                      refine ⟨2016515038823760745176877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2688686718431680993569169 2016515038823760745176877)
                      ·
                        rfl

theorem cell23_3927149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_3927149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927149 prefixEnd_3927149 := by exact prefixLift 3927149
  have htrace : WordTrace (prefixWord ++ tailWord_3927149) baseStart_3927149 baseEnd_3927149 := by
    simpa [prefixWord, tailWord_3927149, baseEnd_3927149] using wordTrace_append hprefix tailTrace_3927149
  have hstable : (prefixWord ++ tailWord_3927149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927149).length < 2 ^ (prefixWord ++ tailWord_3927149).sum := by decide
  have hdescent : baseEnd_3927149 < baseStart_3927149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927166 : List Nat := [4, 2, 4, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3927166 : Nat := 118140960795 + 3927166 * 2 ^ 59
def prefixEnd_3927166 : Nat := 4983230072969 + 3 ^ 40 * 3927166 * 2
def baseEnd_3927166 : Nat := 2016523767994887178664299

theorem tailTrace_3927166 : CollatzResearch.WordTrace tailWord_3927166 prefixEnd_3927166 2016523767994887178664299 := by
  unfold tailWord_3927166
  simp only [CollatzResearch.WordTrace]
  refine ⟨17904438911319470425029169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95490340860370508933488901 17904438911319470425029169)
  ·
    refine ⟨13428329183489602818771877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17904438911319470425029169 13428329183489602818771877)
    ·
      refine ⟨2517811721904300528519727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13428329183489602818771877 2517811721904300528519727)
      ·
        refine ⟨3776717582856450792779591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2517811721904300528519727 3776717582856450792779591)
        ·
          refine ⟨5665076374284676189169387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3776717582856450792779591 5665076374284676189169387)
          ·
            refine ⟨8497614561427014283754081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5665076374284676189169387 8497614561427014283754081)
            ·
              refine ⟨6373210921070260712815561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8497614561427014283754081 6373210921070260712815561)
              ·
                refine ⟨4779908190802695534611671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6373210921070260712815561 4779908190802695534611671)
                ·
                  refine ⟨7169862286204043301917507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4779908190802695534611671 7169862286204043301917507)
                  ·
                    refine ⟨10754793429306064952876261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7169862286204043301917507 10754793429306064952876261)
                    ·
                      refine ⟨2016523767994887178664299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10754793429306064952876261 2016523767994887178664299)
                      ·
                        rfl

theorem cell23_3927166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3927166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927166 prefixEnd_3927166 := by exact prefixLift 3927166
  have htrace : WordTrace (prefixWord ++ tailWord_3927166) baseStart_3927166 baseEnd_3927166 := by
    simpa [prefixWord, tailWord_3927166, baseEnd_3927166] using wordTrace_append hprefix tailTrace_3927166
  have hstable : (prefixWord ++ tailWord_3927166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927166).length < 2 ^ (prefixWord ++ tailWord_3927166).sum := by decide
  have hdescent : baseEnd_3927166 < baseStart_3927166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927192 : List Nat := [2, 1, 2, 4, 2, 1, 2, 3, 1, 3, 2]
def baseStart_3927192 : Nat := 118140960795 + 3927192 * 2 ^ 59
def prefixEnd_3927192 : Nat := 4983230072969 + 3 ^ 40 * 3927192 * 2
def baseEnd_3927192 : Nat := 2016537118491904076939179

theorem tailTrace_3927192 : CollatzResearch.WordTrace tailWord_3927192 prefixEnd_3927192 2016537118491904076939179 := by
  unfold tailWord_3927192
  simp only [CollatzResearch.WordTrace]
  refine ⟨71618229794230784920339915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95490973058974379893786553 71618229794230784920339915)
  ·
    refine ⟨107427344691346177380509873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71618229794230784920339915 107427344691346177380509873)
    ·
      refine ⟨80570508518509633035382405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107427344691346177380509873 80570508518509633035382405)
      ·
        refine ⟨15106970347220556194134201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80570508518509633035382405 15106970347220556194134201)
        ·
          refine ⟨11330227760415417145600651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15106970347220556194134201 11330227760415417145600651)
          ·
            refine ⟨16995341640623125718400977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11330227760415417145600651 16995341640623125718400977)
            ·
              refine ⟨12746506230467344288800733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16995341640623125718400977 12746506230467344288800733)
              ·
                refine ⟨4779939836425254108300275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12746506230467344288800733 4779939836425254108300275)
                ·
                  refine ⟨7169909754637881162450413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4779939836425254108300275 7169909754637881162450413)
                  ·
                    refine ⟨2688716157989205435918905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7169909754637881162450413 2688716157989205435918905)
                    ·
                      refine ⟨2016537118491904076939179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2688716157989205435918905 2016537118491904076939179)
                      ·
                        rfl

theorem cell23_3927192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_3927192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927192 prefixEnd_3927192 := by exact prefixLift 3927192
  have htrace : WordTrace (prefixWord ++ tailWord_3927192) baseStart_3927192 baseEnd_3927192 := by
    simpa [prefixWord, tailWord_3927192, baseEnd_3927192] using wordTrace_append hprefix tailTrace_3927192
  have hstable : (prefixWord ++ tailWord_3927192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927192).length < 2 ^ (prefixWord ++ tailWord_3927192).sum := by decide
  have hdescent : baseEnd_3927192 < baseStart_3927192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927241 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 5, 7]
def baseStart_3927241 : Nat := 118140960795 + 3927241 * 2 ^ 59
def prefixEnd_3927241 : Nat := 4983230072969 + 3 ^ 40 * 3927241 * 2
def baseEnd_3927241 : Nat := 672187426347991461742151

theorem tailTrace_3927241 : CollatzResearch.WordTrace tailWord_3927241 prefixEnd_3927241 672187426347991461742151 := by
  unfold tailWord_3927241
  simp only [CollatzResearch.WordTrace]
  refine ⟨143238246765284051209213577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95492164510189367472809051 143238246765284051209213577)
  ·
    refine ⟨107428685073963038406910183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143238246765284051209213577 107428685073963038406910183)
    ·
      refine ⟨161143027610944557610365275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107428685073963038406910183 161143027610944557610365275)
      ·
        refine ⟨241714541416416836415547913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161143027610944557610365275 241714541416416836415547913)
        ·
          refine ⟨181285906062312627311660935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241714541416416836415547913 181285906062312627311660935)
          ·
            refine ⟨271928859093468940967491403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181285906062312627311660935 271928859093468940967491403)
            ·
              refine ⟨407893288640203411451237105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271928859093468940967491403 407893288640203411451237105)
              ·
                refine ⟨305919966480152558588427829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407893288640203411451237105 305919966480152558588427829)
                ·
                  refine ⟨28679996857514302367665109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 305919966480152558588427829 28679996857514302367665109)
                  ·
                    refine ⟨672187426347991461742151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28679996857514302367665109 672187426347991461742151)
                    ·
                      rfl

theorem cell23_3927241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 7].length) (baseStart_3927241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927241 prefixEnd_3927241 := by exact prefixLift 3927241
  have htrace : WordTrace (prefixWord ++ tailWord_3927241) baseStart_3927241 baseEnd_3927241 := by
    simpa [prefixWord, tailWord_3927241, baseEnd_3927241] using wordTrace_append hprefix tailTrace_3927241
  have hstable : (prefixWord ++ tailWord_3927241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927241).length < 2 ^ (prefixWord ++ tailWord_3927241).sum := by decide
  have hdescent : baseEnd_3927241 < baseStart_3927241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927251 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 7]
def baseStart_3927251 : Nat := 118140960795 + 3927251 * 2 ^ 59
def prefixEnd_3927251 : Nat := 4983230072969 + 3 ^ 40 * 3927251 * 2
def baseEnd_3927251 : Nat := 2016567413850519346101407

theorem tailTrace_3927251 : CollatzResearch.WordTrace tailWord_3927251 prefixEnd_3927251 2016567413850519346101407 := by
  unfold tailWord_3927251
  simp only [CollatzResearch.WordTrace]
  refine ⟨143238611495247822917077607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95492407663498548611385071 143238611495247822917077607)
  ·
    refine ⟨214857917242871734375616411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143238611495247822917077607 214857917242871734375616411)
    ·
      refine ⟨322286875864307601563424617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214857917242871734375616411 322286875864307601563424617)
      ·
        refine ⟨241715156898230701172568463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322286875864307601563424617 241715156898230701172568463)
        ·
          refine ⟨362572735347346051758852695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241715156898230701172568463 362572735347346051758852695)
          ·
            refine ⟨543859103021019077638279043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362572735347346051758852695 543859103021019077638279043)
            ·
              refine ⟨815788654531528616457418565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543859103021019077638279043 815788654531528616457418565)
              ·
                refine ⟨152960372724661615585765981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 815788654531528616457418565 152960372724661615585765981)
                ·
                  refine ⟨57360139771748105844662243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152960372724661615585765981 57360139771748105844662243)
                  ·
                    refine ⟨86040209657622158766993365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57360139771748105844662243 86040209657622158766993365)
                    ·
                      refine ⟨2016567413850519346101407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86040209657622158766993365 2016567413850519346101407)
                      ·
                        rfl

theorem cell23_3927251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_3927251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927251 prefixEnd_3927251 := by exact prefixLift 3927251
  have htrace : WordTrace (prefixWord ++ tailWord_3927251) baseStart_3927251 baseEnd_3927251 := by
    simpa [prefixWord, tailWord_3927251, baseEnd_3927251] using wordTrace_append hprefix tailTrace_3927251
  have hstable : (prefixWord ++ tailWord_3927251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927251).length < 2 ^ (prefixWord ++ tailWord_3927251).sum := by decide
  have hdescent : baseEnd_3927251 < baseStart_3927251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927265 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 2, 5, 2]
def baseStart_3927265 : Nat := 118140960795 + 3927265 * 2 ^ 59
def prefixEnd_3927265 : Nat := 4983230072969 + 3 ^ 40 * 3927265 * 2
def baseEnd_3927265 : Nat := 2016574602579682291326343

theorem tailTrace_3927265 : CollatzResearch.WordTrace tailWord_3927265 prefixEnd_3927265 2016574602579682291326343 := by
  unfold tailWord_3927265
  simp only [CollatzResearch.WordTrace]
  refine ⟨143239122117197103308087249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95492748078131402205391499 143239122117197103308087249)
  ·
    refine ⟨107429341587897827481065437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143239122117197103308087249 107429341587897827481065437)
    ·
      refine ⟨40286003095461685305399539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107429341587897827481065437 40286003095461685305399539)
      ·
        refine ⟨60429004643192527958099309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40286003095461685305399539 60429004643192527958099309)
        ·
          refine ⟨22660876741197197984287241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60429004643192527958099309 22660876741197197984287241)
          ·
            refine ⟨16995657555897898488215431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22660876741197197984287241 16995657555897898488215431)
            ·
              refine ⟨25493486333846847732323147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16995657555897898488215431 25493486333846847732323147)
              ·
                refine ⟨38240229500770271598484721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25493486333846847732323147 38240229500770271598484721)
                ·
                  refine ⟨28680172125577703698863541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38240229500770271598484721 28680172125577703698863541)
                  ·
                    refine ⟨2688766136772909721768457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28680172125577703698863541 2688766136772909721768457)
                    ·
                      refine ⟨2016574602579682291326343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2688766136772909721768457 2016574602579682291326343)
                      ·
                        rfl

theorem cell23_3927265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_3927265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927265 prefixEnd_3927265 := by exact prefixLift 3927265
  have htrace : WordTrace (prefixWord ++ tailWord_3927265) baseStart_3927265 baseEnd_3927265 := by
    simpa [prefixWord, tailWord_3927265, baseEnd_3927265] using wordTrace_append hprefix tailTrace_3927265
  have hstable : (prefixWord ++ tailWord_3927265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927265).length < 2 ^ (prefixWord ++ tailWord_3927265).sum := by decide
  have hdescent : baseEnd_3927265 < baseStart_3927265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927268 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_3927268 : Nat := 118140960795 + 3927268 * 2 ^ 59
def prefixEnd_3927268 : Nat := 4983230072969 + 3 ^ 40 * 3927268 * 2
def baseEnd_3927268 : Nat := 2016576143021645779588829

theorem tailTrace_3927268 : CollatzResearch.WordTrace tailWord_3927268 prefixEnd_3927268 2016576143021645779588829 := by
  unfold tailWord_3927268
  simp only [CollatzResearch.WordTrace]
  refine ⟨71619615768093117410223229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95492821024124156546964305 71619615768093117410223229)
  ·
    refine ⟨26857355913034919028833711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71619615768093117410223229 26857355913034919028833711)
    ·
      refine ⟨40286033869552378543250567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26857355913034919028833711 40286033869552378543250567)
      ·
        refine ⟨60429050804328567814875851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40286033869552378543250567 60429050804328567814875851)
        ·
          refine ⟨90643576206492851722313777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60429050804328567814875851 90643576206492851722313777)
          ·
            refine ⟨67982682154869638791735333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90643576206492851722313777 67982682154869638791735333)
            ·
              refine ⟨12746752904038057273450375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67982682154869638791735333 12746752904038057273450375)
              ·
                refine ⟨19120129356057085910175563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12746752904038057273450375 19120129356057085910175563)
                ·
                  refine ⟨28680194034085628865263345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19120129356057085910175563 28680194034085628865263345)
                  ·
                    refine ⟨21510145525564221648947509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28680194034085628865263345 21510145525564221648947509)
                    ·
                      refine ⟨2016576143021645779588829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21510145525564221648947509 2016576143021645779588829)
                      ·
                        rfl

theorem cell23_3927268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_3927268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927268 prefixEnd_3927268 := by exact prefixLift 3927268
  have htrace : WordTrace (prefixWord ++ tailWord_3927268) baseStart_3927268 baseEnd_3927268 := by
    simpa [prefixWord, tailWord_3927268, baseEnd_3927268] using wordTrace_append hprefix tailTrace_3927268
  have hstable : (prefixWord ++ tailWord_3927268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927268).length < 2 ^ (prefixWord ++ tailWord_3927268).sum := by decide
  have hdescent : baseEnd_3927268 < baseStart_3927268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927292 : List Nat := [2, 2, 2, 1, 5, 2, 1, 1, 2, 5]
def baseStart_3927292 : Nat := 118140960795 + 3927292 * 2 ^ 59
def prefixEnd_3927292 : Nat := 4983230072969 + 3 ^ 40 * 3927292 * 2
def baseEnd_3927292 : Nat := 672196155519117895229573

theorem tailTrace_3927292 : CollatzResearch.WordTrace tailWord_3927292 prefixEnd_3927292 672196155519117895229573 := by
  unfold tailWord_3927292
  simp only [CollatzResearch.WordTrace]
  refine ⟨71620053444049643459660065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95493404592066191279546753 71620053444049643459660065)
  ·
    refine ⟨53715040083037232594745049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71620053444049643459660065 53715040083037232594745049)
    ·
      refine ⟨40286280062277924446058787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53715040083037232594745049 40286280062277924446058787)
      ·
        refine ⟨60429420093416886669088181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40286280062277924446058787 60429420093416886669088181)
        ·
          refine ⟨5665258133757833125227017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60429420093416886669088181 5665258133757833125227017)
          ·
            refine ⟨4248943600318374843920263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5665258133757833125227017 4248943600318374843920263)
            ·
              refine ⟨6373415400477562265880395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4248943600318374843920263 6373415400477562265880395)
              ·
                refine ⟨9560123100716343398820593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6373415400477562265880395 9560123100716343398820593)
                ·
                  refine ⟨7170092325537257549115445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9560123100716343398820593 7170092325537257549115445)
                  ·
                    refine ⟨672196155519117895229573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7170092325537257549115445 672196155519117895229573)
                    ·
                      rfl

theorem cell23_3927292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_3927292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927292 prefixEnd_3927292 := by exact prefixLift 3927292
  have htrace : WordTrace (prefixWord ++ tailWord_3927292) baseStart_3927292 baseEnd_3927292 := by
    simpa [prefixWord, tailWord_3927292, baseEnd_3927292] using wordTrace_append hprefix tailTrace_3927292
  have hstable : (prefixWord ++ tailWord_3927292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927292).length < 2 ^ (prefixWord ++ tailWord_3927292).sum := by decide
  have hdescent : baseEnd_3927292 < baseStart_3927292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927295 : List Nat := [1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 4]
def baseStart_3927295 : Nat := 118140960795 + 3927295 * 2 ^ 59
def prefixEnd_3927295 : Nat := 4983230072969 + 3 ^ 40 * 3927295 * 2
def baseEnd_3927295 : Nat := 2016590006999317173951205

theorem tailTrace_3927295 : CollatzResearch.WordTrace tailWord_3927295 prefixEnd_3927295 2016590006999317173951205 := by
  unfold tailWord_3927295
  simp only [CollatzResearch.WordTrace]
  refine ⟨143240216307088418431679339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95493477538058945621119559 143240216307088418431679339)
  ·
    refine ⟨214860324460632627647519009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143240216307088418431679339 214860324460632627647519009)
    ·
      refine ⟨161145243345474470735639257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214860324460632627647519009 161145243345474470735639257)
      ·
        refine ⟨120858932509105853051729443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161145243345474470735639257 120858932509105853051729443)
        ·
          refine ⟨181288398763658779577594165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120858932509105853051729443 181288398763658779577594165)
          ·
            refine ⟨16995787384093010585399453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181288398763658779577594165 16995787384093010585399453)
            ·
              refine ⟨6373420269034878969524795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16995787384093010585399453 6373420269034878969524795)
              ·
                refine ⟨9560130403552318454287193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6373420269034878969524795 9560130403552318454287193)
                ·
                  refine ⟨7170097802664238840715395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9560130403552318454287193 7170097802664238840715395)
                  ·
                    refine ⟨10755146703996358261073093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7170097802664238840715395 10755146703996358261073093)
                    ·
                      refine ⟨2016590006999317173951205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10755146703996358261073093 2016590006999317173951205)
                      ·
                        rfl

theorem cell23_3927295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_3927295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927295 prefixEnd_3927295 := by exact prefixLift 3927295
  have htrace : WordTrace (prefixWord ++ tailWord_3927295) baseStart_3927295 baseEnd_3927295 := by
    simpa [prefixWord, tailWord_3927295, baseEnd_3927295] using wordTrace_append hprefix tailTrace_3927295
  have hstable : (prefixWord ++ tailWord_3927295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927295).length < 2 ^ (prefixWord ++ tailWord_3927295).sum := by decide
  have hdescent : baseEnd_3927295 < baseStart_3927295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927308 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 2, 1, 6]
def baseStart_3927308 : Nat := 118140960795 + 3927308 * 2 ^ 59
def prefixEnd_3927308 : Nat := 4983230072969 + 3 ^ 40 * 3927308 * 2
def baseEnd_3927308 : Nat := 2016596682247825623088645

theorem tailTrace_3927308 : CollatzResearch.WordTrace tailWord_3927308 prefixEnd_3927308 2016596682247825623088645 := by
  unfold tailWord_3927308
  simp only [CollatzResearch.WordTrace]
  refine ⟨71620345228020660825951289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95493793637360881101268385 71620345228020660825951289)
  ·
    refine ⟨53715258921015495619463467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71620345228020660825951289 53715258921015495619463467)
    ·
      refine ⟨80572888381523243429195201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53715258921015495619463467 80572888381523243429195201)
      ·
        refine ⟨60429666286142432571896401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80572888381523243429195201 60429666286142432571896401)
        ·
          refine ⟨45322249714606824428922301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60429666286142432571896401 45322249714606824428922301)
          ·
            refine ⟨16995843642977559160845863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45322249714606824428922301 16995843642977559160845863)
            ·
              refine ⟨25493765464466338741268795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16995843642977559160845863 25493765464466338741268795)
              ·
                refine ⟨38240648196699508111903193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25493765464466338741268795 38240648196699508111903193)
                ·
                  refine ⟨28680486147524631083927395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38240648196699508111903193 28680486147524631083927395)
                  ·
                    refine ⟨43020729221286946625891093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28680486147524631083927395 43020729221286946625891093)
                    ·
                      refine ⟨2016596682247825623088645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43020729221286946625891093 2016596682247825623088645)
                      ·
                        rfl

theorem cell23_3927308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_3927308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927308 prefixEnd_3927308 := by exact prefixLift 3927308
  have htrace : WordTrace (prefixWord ++ tailWord_3927308) baseStart_3927308 baseEnd_3927308 := by
    simpa [prefixWord, tailWord_3927308, baseEnd_3927308] using wordTrace_append hprefix tailTrace_3927308
  have hstable : (prefixWord ++ tailWord_3927308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927308).length < 2 ^ (prefixWord ++ tailWord_3927308).sum := by decide
  have hdescent : baseEnd_3927308 < baseStart_3927308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927322 : List Nat := [3, 1, 1, 3, 3, 2, 2, 1, 3, 4]
def baseStart_3927322 : Nat := 118140960795 + 3927322 * 2 ^ 59
def prefixEnd_3927322 : Nat := 4983230072969 + 3 ^ 40 * 3927322 * 2
def baseEnd_3927322 : Nat := 672201290325662856104527

theorem tailTrace_3927322 : CollatzResearch.WordTrace tailWord_3927322 prefixEnd_3927322 672201290325662856104527 := by
  unfold tailWord_3927322
  simp only [CollatzResearch.WordTrace]
  refine ⟨35810300269497650510728055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95494134051993734695274813 35810300269497650510728055)
  ·
    refine ⟨53715450404246475766092083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35810300269497650510728055 53715450404246475766092083)
    ·
      refine ⟨80573175606369713649138125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53715450404246475766092083 80573175606369713649138125)
      ·
        refine ⟨30214940852388642618426797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80573175606369713649138125 30214940852388642618426797)
        ·
          refine ⟨11330602819645740981910049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30214940852388642618426797 11330602819645740981910049)
          ·
            refine ⟨8497952114734305736432537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11330602819645740981910049 8497952114734305736432537)
            ·
              refine ⟨6373464086050729302324403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8497952114734305736432537 6373464086050729302324403)
              ·
                refine ⟨9560196129076093953486605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6373464086050729302324403 9560196129076093953486605)
                ·
                  refine ⟨3585073548403535232557477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9560196129076093953486605 3585073548403535232557477)
                  ·
                    refine ⟨672201290325662856104527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3585073548403535232557477 672201290325662856104527)
                    ·
                      rfl

theorem cell23_3927322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 3, 4].length) (baseStart_3927322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927322 prefixEnd_3927322 := by exact prefixLift 3927322
  have htrace : WordTrace (prefixWord ++ tailWord_3927322) baseStart_3927322 baseEnd_3927322 := by
    simpa [prefixWord, tailWord_3927322, baseEnd_3927322] using wordTrace_append hprefix tailTrace_3927322
  have hstable : (prefixWord ++ tailWord_3927322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927322).length < 2 ^ (prefixWord ++ tailWord_3927322).sum := by decide
  have hdescent : baseEnd_3927322 < baseStart_3927322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927372 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 4, 3, 2]
def baseStart_3927372 : Nat := 118140960795 + 3927372 * 2 ^ 59
def prefixEnd_3927372 : Nat := 4983230072969 + 3 ^ 40 * 3927372 * 2
def baseEnd_3927372 : Nat := 2016629545009713372688351

theorem tailTrace_3927372 : CollatzResearch.WordTrace tailWord_3927372 prefixEnd_3927372 2016629545009713372688351 := by
  unfold tailWord_3927372
  simp only [CollatzResearch.WordTrace]
  refine ⟨71621512363904730291116185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95495349818539640388154913 71621512363904730291116185)
  ·
    refine ⟨53716134272928547718337139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71621512363904730291116185 53716134272928547718337139)
    ·
      refine ⟨80574201409392821577505709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53716134272928547718337139 80574201409392821577505709)
      ·
        refine ⟨30215325528522308091564641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80574201409392821577505709 30215325528522308091564641)
        ·
          refine ⟨22661494146391731068673481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30215325528522308091564641 22661494146391731068673481)
          ·
            refine ⟨16996120609793798301505111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22661494146391731068673481 16996120609793798301505111)
            ·
              refine ⟨25494180914690697452257667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16996120609793798301505111 25494180914690697452257667)
              ·
                refine ⟨38241271372036046178386501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25494180914690697452257667 38241271372036046178386501)
                ·
                  refine ⟨7170238382256758658447469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38241271372036046178386501 7170238382256758658447469)
                  ·
                    refine ⟨2688839393346284496917801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7170238382256758658447469 2688839393346284496917801)
                    ·
                      refine ⟨2016629545009713372688351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2688839393346284496917801 2016629545009713372688351)
                      ·
                        rfl

theorem cell23_3927372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_3927372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927372 prefixEnd_3927372 := by exact prefixLift 3927372
  have htrace : WordTrace (prefixWord ++ tailWord_3927372) baseStart_3927372 baseEnd_3927372 := by
    simpa [prefixWord, tailWord_3927372, baseEnd_3927372] using wordTrace_append hprefix tailTrace_3927372
  have hstable : (prefixWord ++ tailWord_3927372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927372).length < 2 ^ (prefixWord ++ tailWord_3927372).sum := by decide
  have hdescent : baseEnd_3927372 < baseStart_3927372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927373 : List Nat := [1, 6, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_3927373 : Nat := 118140960795 + 3927373 * 2 ^ 59
def prefixEnd_3927373 : Nat := 4983230072969 + 3 ^ 40 * 3927373 * 2
def baseEnd_3927373 : Nat := 672210019496789289591949

theorem tailTrace_3927373 : CollatzResearch.WordTrace tailWord_3927373 prefixEnd_3927373 672210019496789289591949 := by
  unfold tailWord_3927373
  simp only [CollatzResearch.WordTrace]
  refine ⟨143243061200805837753018773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95495374133870558502012515 143243061200805837753018773)
  ·
    refine ⟨6714518493787773644672755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143243061200805837753018773 6714518493787773644672755)
    ·
      refine ⟨10071777740681660467009133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6714518493787773644672755 10071777740681660467009133)
      ·
        refine ⟨3776916652755622675128425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10071777740681660467009133 3776916652755622675128425)
        ·
          refine ⟨2832687489566717006346319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3776916652755622675128425 2832687489566717006346319)
          ·
            refine ⟨4249031234350075509519479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2832687489566717006346319 4249031234350075509519479)
            ·
              refine ⟨6373546851525113264279219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4249031234350075509519479 6373546851525113264279219)
              ·
                refine ⟨9560320277287669896418829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6373546851525113264279219 9560320277287669896418829)
                ·
                  refine ⟨3585120103982876211157061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9560320277287669896418829 3585120103982876211157061)
                  ·
                    refine ⟨672210019496789289591949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3585120103982876211157061 672210019496789289591949)
                    ·
                      rfl

theorem cell23_3927373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_3927373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927373 prefixEnd_3927373 := by exact prefixLift 3927373
  have htrace : WordTrace (prefixWord ++ tailWord_3927373) baseStart_3927373 baseEnd_3927373 := by
    simpa [prefixWord, tailWord_3927373, baseEnd_3927373] using wordTrace_append hprefix tailTrace_3927373
  have hstable : (prefixWord ++ tailWord_3927373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927373).length < 2 ^ (prefixWord ++ tailWord_3927373).sum := by decide
  have hdescent : baseEnd_3927373 < baseStart_3927373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927399 : List Nat := [1, 1, 5, 1, 4, 2, 1, 2, 1, 5]
def baseStart_3927399 : Nat := 118140960795 + 3927399 * 2 ^ 59
def prefixEnd_3927399 : Nat := 4983230072969 + 3 ^ 40 * 3927399 * 2
def baseEnd_3927399 : Nat := 672214469662461589016909

theorem tailTrace_3927399 : CollatzResearch.WordTrace tailWord_3927399 prefixEnd_3927399 672214469662461589016909 := by
  unfold tailWord_3927399
  simp only [CollatzResearch.WordTrace]
  refine ⟨143244009498711644193465251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95496006332474429462310167 143244009498711644193465251)
  ·
    refine ⟨214866014248067466290197877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143244009498711644193465251 214866014248067466290197877)
    ·
      refine ⟨20143688835756324964706051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214866014248067466290197877 20143688835756324964706051)
      ·
        refine ⟨30215533253634487447059077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20143688835756324964706051 30215533253634487447059077)
        ·
          refine ⟨5665412485056466396323577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30215533253634487447059077 5665412485056466396323577)
          ·
            refine ⟨4249059363792349797242683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5665412485056466396323577 4249059363792349797242683)
            ·
              refine ⟨6373589045688524695864025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4249059363792349797242683 6373589045688524695864025)
              ·
                refine ⟨4780191784266393521898019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6373589045688524695864025 4780191784266393521898019)
                ·
                  refine ⟨7170287676399590282847029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4780191784266393521898019 7170287676399590282847029)
                  ·
                    refine ⟨672214469662461589016909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7170287676399590282847029 672214469662461589016909)
                    ·
                      rfl

theorem cell23_3927399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_3927399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927399 prefixEnd_3927399 := by exact prefixLift 3927399
  have htrace : WordTrace (prefixWord ++ tailWord_3927399) baseStart_3927399 baseEnd_3927399 := by
    simpa [prefixWord, tailWord_3927399, baseEnd_3927399] using wordTrace_append hprefix tailTrace_3927399
  have hstable : (prefixWord ++ tailWord_3927399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927399).length < 2 ^ (prefixWord ++ tailWord_3927399).sum := by decide
  have hdescent : baseEnd_3927399 < baseStart_3927399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927408 : List Nat := [2, 1, 1, 1, 4, 2, 1, 11]
def baseStart_3927408 : Nat := 118140960795 + 3927408 * 2 ^ 59
def prefixEnd_3927408 : Nat := 4983230072969 + 3 ^ 40 * 3927408 * 2
def baseEnd_3927408 : Nat := 74690667789380564142155

theorem tailTrace_3927408 : CollatzResearch.WordTrace tailWord_3927408 prefixEnd_3927408 74690667789380564142155 := by
  unfold tailWord_3927408
  simp only [CollatzResearch.WordTrace]
  refine ⟨71622168877839519365271439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95496225170452692487028585 71622168877839519365271439)
  ·
    refine ⟨107433253316759279047907159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71622168877839519365271439 107433253316759279047907159)
    ·
      refine ⟨161149879975138918571860739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107433253316759279047907159 161149879975138918571860739)
      ·
        refine ⟨241724819962708377857791109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161149879975138918571860739 241724819962708377857791109)
        ·
          refine ⟨45323403743007820848335833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241724819962708377857791109 45323403743007820848335833)
          ·
            refine ⟨33992552807255865636251875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45323403743007820848335833 33992552807255865636251875)
            ·
              refine ⟨50988829210883798454377813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33992552807255865636251875 50988829210883798454377813)
              ·
                refine ⟨74690667789380564142155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 50988829210883798454377813 74690667789380564142155)
                ·
                  rfl

theorem cell23_3927408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 11].length) (baseStart_3927408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927408 prefixEnd_3927408 := by exact prefixLift 3927408
  have htrace : WordTrace (prefixWord ++ tailWord_3927408) baseStart_3927408 baseEnd_3927408 := by
    simpa [prefixWord, tailWord_3927408, baseEnd_3927408] using wordTrace_append hprefix tailTrace_3927408
  have hstable : (prefixWord ++ tailWord_3927408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927408).length < 2 ^ (prefixWord ++ tailWord_3927408).sum := by decide
  have hdescent : baseEnd_3927408 < baseStart_3927408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927415 : List Nat := [1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 4]
def baseStart_3927415 : Nat := 118140960795 + 3927415 * 2 ^ 59
def prefixEnd_3927415 : Nat := 4983230072969 + 3 ^ 40 * 3927415 * 2
def baseEnd_3927415 : Nat := 2016651624677856704450653

theorem tailTrace_3927415 : CollatzResearch.WordTrace tailWord_3927415 prefixEnd_3927415 2016651624677856704450653 := by
  unfold tailWord_3927415
  simp only [CollatzResearch.WordTrace]
  refine ⟨143244593066653678926047699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95496395377769119284031799 143244593066653678926047699)
  ·
    refine ⟨214866889599980518389071549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143244593066653678926047699 214866889599980518389071549)
    ·
      refine ⟨80575083599992694395901831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214866889599980518389071549 80575083599992694395901831)
      ·
        refine ⟨120862625399989041593852747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80575083599992694395901831 120862625399989041593852747)
        ·
          refine ⟨181293938099983562390779121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120862625399989041593852747 181293938099983562390779121)
          ·
            refine ⟨135970453574987671793084341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181293938099983562390779121 135970453574987671793084341)
            ·
              refine ⟨12747230022655094230601657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135970453574987671793084341 12747230022655094230601657)
              ·
                refine ⟨9560422516991320672951243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12747230022655094230601657 9560422516991320672951243)
                ·
                  refine ⟨14340633775486981009426865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9560422516991320672951243 14340633775486981009426865)
                  ·
                    refine ⟨10755475331615235757070149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14340633775486981009426865 10755475331615235757070149)
                    ·
                      refine ⟨2016651624677856704450653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10755475331615235757070149 2016651624677856704450653)
                      ·
                        rfl

theorem cell23_3927415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_3927415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927415 prefixEnd_3927415 := by exact prefixLift 3927415
  have htrace : WordTrace (prefixWord ++ tailWord_3927415) baseStart_3927415 baseEnd_3927415 := by
    simpa [prefixWord, tailWord_3927415, baseEnd_3927415] using wordTrace_append hprefix tailTrace_3927415
  have hstable : (prefixWord ++ tailWord_3927415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927415).length < 2 ^ (prefixWord ++ tailWord_3927415).sum := by decide
  have hdescent : baseEnd_3927415 < baseStart_3927415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927425 : List Nat := [1, 2, 4, 3, 2, 11]
def baseStart_3927425 : Nat := 118140960795 + 3927425 * 2 ^ 59
def prefixEnd_3927425 : Nat := 4983230072969 + 3 ^ 40 * 3927425 * 2
def baseEnd_3927425 : Nat := 8298999010223875165949

theorem tailTrace_3927425 : CollatzResearch.WordTrace tailWord_3927425 prefixEnd_3927425 8298999010223875165949 := by
  unfold tailWord_3927425
  simp only [CollatzResearch.WordTrace]
  refine ⟨143244957796617450633911729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95496638531078300422607819 143244957796617450633911729)
  ·
    refine ⟨107433718347463087975433797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143244957796617450633911729 107433718347463087975433797)
    ·
      refine ⟨20143822190149328995393837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107433718347463087975433797 20143822190149328995393837)
      ·
        refine ⟨7553933321305998373272689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20143822190149328995393837 7553933321305998373272689)
        ·
          refine ⟨5665449990979498779954517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7553933321305998373272689 5665449990979498779954517)
          ·
            refine ⟨8298999010223875165949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5665449990979498779954517 8298999010223875165949)
            ·
              rfl

theorem cell23_3927425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 11].length) (baseStart_3927425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927425 prefixEnd_3927425 := by exact prefixLift 3927425
  have htrace : WordTrace (prefixWord ++ tailWord_3927425) baseStart_3927425 baseEnd_3927425 := by
    simpa [prefixWord, tailWord_3927425, baseEnd_3927425] using wordTrace_append hprefix tailTrace_3927425
  have hstable : (prefixWord ++ tailWord_3927425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927425).length < 2 ^ (prefixWord ++ tailWord_3927425).sum := by decide
  have hdescent : baseEnd_3927425 < baseStart_3927425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927435 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 3]
def baseStart_3927435 : Nat := 118140960795 + 3927435 * 2 ^ 59
def prefixEnd_3927435 : Nat := 4983230072969 + 3 ^ 40 * 3927435 * 2
def baseEnd_3927435 : Nat := 2016661894290946626200561

theorem tailTrace_3927435 : CollatzResearch.WordTrace tailWord_3927435 prefixEnd_3927435 2016661894290946626200561 := by
  unfold tailWord_3927435
  simp only [CollatzResearch.WordTrace]
  refine ⟨143245322526581222341775759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95496881684387481561183839 143245322526581222341775759)
  ·
    refine ⟨214867983789871833512663639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143245322526581222341775759 214867983789871833512663639)
    ·
      refine ⟨322301975684807750268995459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214867983789871833512663639 322301975684807750268995459)
      ·
        refine ⟨483452963527211625403493189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322301975684807750268995459 483452963527211625403493189)
        ·
          refine ⟨90647430661352179763154973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 483452963527211625403493189 90647430661352179763154973)
          ·
            refine ⟨33992786498007067411183115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90647430661352179763154973 33992786498007067411183115)
            ·
              refine ⟨50989179747010601116774673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33992786498007067411183115 50989179747010601116774673)
              ·
                refine ⟨38241884810257950837581005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50989179747010601116774673 38241884810257950837581005)
                ·
                  refine ⟨14340706803846731564092877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38241884810257950837581005 14340706803846731564092877)
                  ·
                    refine ⟨5377765051442524336534829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14340706803846731564092877 5377765051442524336534829)
                    ·
                      refine ⟨2016661894290946626200561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5377765051442524336534829 2016661894290946626200561)
                      ·
                        rfl

theorem cell23_3927435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 3, 3].length) (baseStart_3927435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927435 prefixEnd_3927435 := by exact prefixLift 3927435
  have htrace : WordTrace (prefixWord ++ tailWord_3927435) baseStart_3927435 baseEnd_3927435 := by
    simpa [prefixWord, tailWord_3927435, baseEnd_3927435] using wordTrace_append hprefix tailTrace_3927435
  have hstable : (prefixWord ++ tailWord_3927435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927435).length < 2 ^ (prefixWord ++ tailWord_3927435).sum := by decide
  have hdescent : baseEnd_3927435 < baseStart_3927435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927436 : List Nat := [2, 2, 1, 2, 1, 3, 3, 4, 1, 2, 2]
def baseStart_3927436 : Nat := 118140960795 + 3927436 * 2 ^ 59
def prefixEnd_3927436 : Nat := 4983230072969 + 3 ^ 40 * 3927436 * 2
def baseEnd_3927436 : Nat := 2016662407771601122288057

theorem tailTrace_3927436 : CollatzResearch.WordTrace tailWord_3927436 prefixEnd_3927436 2016662407771601122288057 := by
  unfold tailWord_3927436
  simp only [CollatzResearch.WordTrace]
  refine ⟨71622679499788799756281081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95496905999718399675041441 71622679499788799756281081)
  ·
    refine ⟨53717009624841599817210811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71622679499788799756281081 53717009624841599817210811)
    ·
      refine ⟨80575514437262399725816217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53717009624841599817210811 80575514437262399725816217)
      ·
        refine ⟨60431635827946799794362163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80575514437262399725816217 60431635827946799794362163)
        ·
          refine ⟨90647453741920199691543245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60431635827946799794362163 90647453741920199691543245)
          ·
            refine ⟨33992795153220074884328717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90647453741920199691543245 33992795153220074884328717)
            ·
              refine ⟨12747298182457528081623269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33992795153220074884328717 12747298182457528081623269)
              ·
                refine ⟨2390118409210786515304363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12747298182457528081623269 2390118409210786515304363)
                ·
                  refine ⟨3585177613816179772956545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2390118409210786515304363 3585177613816179772956545)
                  ·
                    refine ⟨2688883210362134829717409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3585177613816179772956545 2688883210362134829717409)
                    ·
                      refine ⟨2016662407771601122288057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2688883210362134829717409 2016662407771601122288057)
                      ·
                        rfl

theorem cell23_3927436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 1, 2, 2].length) (baseStart_3927436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927436 prefixEnd_3927436 := by exact prefixLift 3927436
  have htrace : WordTrace (prefixWord ++ tailWord_3927436) baseStart_3927436 baseEnd_3927436 := by
    simpa [prefixWord, tailWord_3927436, baseEnd_3927436] using wordTrace_append hprefix tailTrace_3927436
  have hstable : (prefixWord ++ tailWord_3927436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927436).length < 2 ^ (prefixWord ++ tailWord_3927436).sum := by decide
  have hdescent : baseEnd_3927436 < baseStart_3927436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927469 : List Nat := [1, 5, 2, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_3927469 : Nat := 118140960795 + 3927469 * 2 ^ 59
def prefixEnd_3927469 : Nat := 4983230072969 + 3 ^ 40 * 3927469 * 2
def baseEnd_3927469 : Nat := 2016679352633199493175405

theorem tailTrace_3927469 : CollatzResearch.WordTrace tailWord_3927469 prefixEnd_3927469 2016679352633199493175405 := by
  unfold tailWord_3927469
  simp only [CollatzResearch.WordTrace]
  refine ⟨143246562608458046148513461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95497708405638697432342307 143246562608458046148513461)
  ·
    refine ⟨13429365244542941826423137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143246562608458046148513461 13429365244542941826423137)
    ·
      refine ⟨10072023933407206369817353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13429365244542941826423137 10072023933407206369817353)
      ·
        refine ⟨7554017950055404777363015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10072023933407206369817353 7554017950055404777363015)
        ·
          refine ⟨11331026925083107166044523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7554017950055404777363015 11331026925083107166044523)
          ·
            refine ⟨16996540387624660749066785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11331026925083107166044523 16996540387624660749066785)
            ·
              refine ⟨12747405290718495561800089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16996540387624660749066785 12747405290718495561800089)
              ·
                refine ⟨9560553968038871671350067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12747405290718495561800089 9560553968038871671350067)
                ·
                  refine ⟨14340830952058307507025101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9560553968038871671350067 14340830952058307507025101)
                  ·
                    refine ⟨5377811607021865315134413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14340830952058307507025101 5377811607021865315134413)
                    ·
                      refine ⟨2016679352633199493175405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5377811607021865315134413 2016679352633199493175405)
                      ·
                        rfl

theorem cell23_3927469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_3927469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927469 prefixEnd_3927469 := by exact prefixLift 3927469
  have htrace : WordTrace (prefixWord ++ tailWord_3927469) baseStart_3927469 baseEnd_3927469 := by
    simpa [prefixWord, tailWord_3927469, baseEnd_3927469] using wordTrace_append hprefix tailTrace_3927469
  have hstable : (prefixWord ++ tailWord_3927469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927469).length < 2 ^ (prefixWord ++ tailWord_3927469).sum := by decide
  have hdescent : baseEnd_3927469 < baseStart_3927469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927479 : List Nat := [1, 1, 3, 1, 3, 2, 3, 3, 1, 3, 2]
def baseStart_3927479 : Nat := 118140960795 + 3927479 * 2 ^ 59
def prefixEnd_3927479 : Nat := 4983230072969 + 3 ^ 40 * 3927479 * 2
def baseEnd_3927479 : Nat := 2016684487439744454050359

theorem tailTrace_3927479 : CollatzResearch.WordTrace tailWord_3927479 prefixEnd_3927479 2016684487439744454050359 := by
  unfold tailWord_3927479
  simp only [CollatzResearch.WordTrace]
  refine ⟨143246927338421817856377491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95497951558947878570918327 143246927338421817856377491)
  ·
    refine ⟨214870391007632726784566237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143246927338421817856377491 214870391007632726784566237)
    ·
      refine ⟨80576396627862272544212339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214870391007632726784566237 80576396627862272544212339)
      ·
        refine ⟨120864594941793408816318509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80576396627862272544212339 120864594941793408816318509)
        ·
          refine ⟨45324223103172528306119441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120864594941793408816318509 45324223103172528306119441)
          ·
            refine ⟨33993167327379396229589581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45324223103172528306119441 33993167327379396229589581)
            ·
              refine ⟨12747437747767273586096093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33993167327379396229589581 12747437747767273586096093)
              ·
                refine ⟨4780289155412727594786035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12747437747767273586096093 4780289155412727594786035)
                ·
                  refine ⟨7170433733119091392179053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4780289155412727594786035 7170433733119091392179053)
                  ·
                    refine ⟨2688912649919659272067145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7170433733119091392179053 2688912649919659272067145)
                    ·
                      refine ⟨2016684487439744454050359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2688912649919659272067145 2016684487439744454050359)
                      ·
                        rfl

theorem cell23_3927479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 3, 2].length) (baseStart_3927479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927479 prefixEnd_3927479 := by exact prefixLift 3927479
  have htrace : WordTrace (prefixWord ++ tailWord_3927479) baseStart_3927479 baseEnd_3927479 := by
    simpa [prefixWord, tailWord_3927479, baseEnd_3927479] using wordTrace_append hprefix tailTrace_3927479
  have hstable : (prefixWord ++ tailWord_3927479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927479).length < 2 ^ (prefixWord ++ tailWord_3927479).sum := by decide
  have hdescent : baseEnd_3927479 < baseStart_3927479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927485 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 4, 6]
def baseStart_3927485 : Nat := 118140960795 + 3927485 * 2 ^ 59
def prefixEnd_3927485 : Nat := 4983230072969 + 3 ^ 40 * 3927485 * 2
def baseEnd_3927485 : Nat := 672229189441223810191777

theorem tailTrace_3927485 : CollatzResearch.WordTrace tailWord_3927485 prefixEnd_3927485 672229189441223810191777 := by
  unfold tailWord_3927485
  simp only [CollatzResearch.WordTrace]
  refine ⟨143247146176400080881095909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95498097450933387254063939 143247146176400080881095909)
  ·
    refine ⟨26858839908075015165205483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143247146176400080881095909 26858839908075015165205483)
    ·
      refine ⟨40288259862112522747808225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26858839908075015165205483 40288259862112522747808225)
      ·
        refine ⟨30216194896584392060856169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40288259862112522747808225 30216194896584392060856169)
        ·
          refine ⟨22662146172438294045642127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30216194896584392060856169 22662146172438294045642127)
          ·
            refine ⟨33993219258657441068463191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22662146172438294045642127 33993219258657441068463191)
            ·
              refine ⟨50989828887986161602694787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33993219258657441068463191 50989828887986161602694787)
              ·
                refine ⟨76484743331979242404042181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50989828887986161602694787 76484743331979242404042181)
                ·
                  refine ⟨14340889374746107950757909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76484743331979242404042181 14340889374746107950757909)
                  ·
                    refine ⟨672229189441223810191777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14340889374746107950757909 672229189441223810191777)
                    ·
                      rfl

theorem cell23_3927485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_3927485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927485 prefixEnd_3927485 := by exact prefixLift 3927485
  have htrace : WordTrace (prefixWord ++ tailWord_3927485) baseStart_3927485 baseEnd_3927485 := by
    simpa [prefixWord, tailWord_3927485, baseEnd_3927485] using wordTrace_append hprefix tailTrace_3927485
  have hstable : (prefixWord ++ tailWord_3927485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927485).length < 2 ^ (prefixWord ++ tailWord_3927485).sum := by decide
  have hdescent : baseEnd_3927485 < baseStart_3927485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927532 : List Nat := [2, 2, 1, 1, 2, 1, 2, 7, 5]
def baseStart_3927532 : Nat := 118140960795 + 3927532 * 2 ^ 59
def prefixEnd_3927532 : Nat := 4983230072969 + 3 ^ 40 * 3927532 * 2
def baseEnd_3927532 : Nat := 224079077990492527409735

theorem tailTrace_3927532 : CollatzResearch.WordTrace tailWord_3927532 prefixEnd_3927532 224079077990492527409735 := by
  unfold tailWord_3927532
  simp only [CollatzResearch.WordTrace]
  refine ⟨71624430203614903954028425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95499240271486538605371233 71624430203614903954028425)
  ·
    refine ⟨53718322652711177965521319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71624430203614903954028425 53718322652711177965521319)
    ·
      refine ⟨80577483979066766948281979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53718322652711177965521319 80577483979066766948281979)
      ·
        refine ⟨120866225968600150422422969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80577483979066766948281979 120866225968600150422422969)
        ·
          refine ⟨90649669476450112816817227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120866225968600150422422969 90649669476450112816817227)
          ·
            refine ⟨135974504214675169225225841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90649669476450112816817227 135974504214675169225225841)
            ·
              refine ⟨101980878161006376918919381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135974504214675169225225841 101980878161006376918919381)
              ·
                refine ⟨2390176831898586959037173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 101980878161006376918919381 2390176831898586959037173)
                ·
                  refine ⟨224079077990492527409735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2390176831898586959037173 224079077990492527409735)
                  ·
                    rfl

theorem cell23_3927532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 5].length) (baseStart_3927532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927532 prefixEnd_3927532 := by exact prefixLift 3927532
  have htrace : WordTrace (prefixWord ++ tailWord_3927532) baseStart_3927532 baseEnd_3927532 := by
    simpa [prefixWord, tailWord_3927532, baseEnd_3927532] using wordTrace_append hprefix tailTrace_3927532
  have hstable : (prefixWord ++ tailWord_3927532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927532).length < 2 ^ (prefixWord ++ tailWord_3927532).sum := by decide
  have hdescent : baseEnd_3927532 < baseStart_3927532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927602 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3]
def baseStart_3927602 : Nat := 118140960795 + 3927602 * 2 ^ 59
def prefixEnd_3927602 : Nat := 4983230072969 + 3 ^ 40 * 3927602 * 2
def baseEnd_3927602 : Nat := 2016747645560247472812293

theorem tailTrace_3927602 : CollatzResearch.WordTrace tailWord_3927602 prefixEnd_3927602 2016747645560247472812293 := by
  unfold tailWord_3927602
  simp only [CollatzResearch.WordTrace]
  refine ⟨35812853379244052465776265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95500942344650806575403373 35812853379244052465776265)
  ·
    refine ⟨26859640034433039349332199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35812853379244052465776265 26859640034433039349332199)
    ·
      refine ⟨40289460051649559023998299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26859640034433039349332199 40289460051649559023998299)
      ·
        refine ⟨60434190077474338535997449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40289460051649559023998299 60434190077474338535997449)
        ·
          refine ⟨45325642558105753901998087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60434190077474338535997449 45325642558105753901998087)
          ·
            refine ⟨67988463837158630852997131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45325642558105753901998087 67988463837158630852997131)
            ·
              refine ⟨101982695755737946279495697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67988463837158630852997131 101982695755737946279495697)
              ·
                refine ⟨76487021816803459709621773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101982695755737946279495697 76487021816803459709621773)
                ·
                  refine ⟨28682633181301297391108165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76487021816803459709621773 28682633181301297391108165)
                  ·
                    refine ⟨5377993721493993260832781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28682633181301297391108165 5377993721493993260832781)
                    ·
                      refine ⟨2016747645560247472812293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5377993721493993260832781 2016747645560247472812293)
                      ·
                        rfl

theorem cell23_3927602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_3927602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927602 prefixEnd_3927602 := by exact prefixLift 3927602
  have htrace : WordTrace (prefixWord ++ tailWord_3927602) baseStart_3927602 baseEnd_3927602 := by
    simpa [prefixWord, tailWord_3927602, baseEnd_3927602] using wordTrace_append hprefix tailTrace_3927602
  have hstable : (prefixWord ++ tailWord_3927602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927602).length < 2 ^ (prefixWord ++ tailWord_3927602).sum := by decide
  have hdescent : baseEnd_3927602 < baseStart_3927602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927635 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 4, 9]
def baseStart_3927635 : Nat := 118140960795 + 3927635 * 2 ^ 59
def prefixEnd_3927635 : Nat := 4983230072969 + 3 ^ 40 * 3927635 * 2
def baseEnd_3927635 : Nat := 672254863473948614566547

theorem tailTrace_3927635 : CollatzResearch.WordTrace tailWord_3927635 prefixEnd_3927635 672254863473948614566547 := by
  unfold tailWord_3927635
  simp only [CollatzResearch.WordTrace]
  refine ⟨143252617125856656499056359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95501744750571104332704239 143252617125856656499056359)
  ·
    refine ⟨214878925688784984748584539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143252617125856656499056359 214878925688784984748584539)
    ·
      refine ⟨322318388533177477122876809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214878925688784984748584539 322318388533177477122876809)
      ·
        refine ⟨241738791399883107842157607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322318388533177477122876809 241738791399883107842157607)
        ·
          refine ⟨362608187099824661763236411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241738791399883107842157607 362608187099824661763236411)
          ·
            refine ⟨543912280649736992644854617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362608187099824661763236411 543912280649736992644854617)
            ·
              refine ⟨407934210487302744483640963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543912280649736992644854617 407934210487302744483640963)
              ·
                refine ⟨611901315730954116725461445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407934210487302744483640963 611901315730954116725461445)
                ·
                  refine ⟨114731496699553896886024021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 611901315730954116725461445 114731496699553896886024021)
                  ·
                    refine ⟨672254863473948614566547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 114731496699553896886024021 672254863473948614566547)
                    ·
                      rfl

theorem cell23_3927635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 9].length) (baseStart_3927635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927635 prefixEnd_3927635 := by exact prefixLift 3927635
  have htrace : WordTrace (prefixWord ++ tailWord_3927635) baseStart_3927635 baseEnd_3927635 := by
    simpa [prefixWord, tailWord_3927635, baseEnd_3927635] using wordTrace_append hprefix tailTrace_3927635
  have hstable : (prefixWord ++ tailWord_3927635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927635).length < 2 ^ (prefixWord ++ tailWord_3927635).sum := by decide
  have hdescent : baseEnd_3927635 < baseStart_3927635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927649 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 5, 1, 3]
def baseStart_3927649 : Nat := 118140960795 + 3927649 * 2 ^ 59
def prefixEnd_3927649 : Nat := 4983230072969 + 3 ^ 40 * 3927649 * 2
def baseEnd_3927649 : Nat := 2016771779151008788924577

theorem tailTrace_3927649 : CollatzResearch.WordTrace tailWord_3927649 prefixEnd_3927649 2016771779151008788924577 := by
  unfold tailWord_3927649
  simp only [CollatzResearch.WordTrace]
  refine ⟨143253127747805936890066001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95502085165203957926710667 143253127747805936890066001)
  ·
    refine ⟨107439845810854452667549501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143253127747805936890066001 107439845810854452667549501)
    ·
      refine ⟨40289942179070419750331063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107439845810854452667549501 40289942179070419750331063)
      ·
        refine ⟨60434913268605629625496595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40289942179070419750331063 60434913268605629625496595)
        ·
          refine ⟨90652369902908444438244893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60434913268605629625496595 90652369902908444438244893)
          ·
            refine ⟨33994638713590666664341835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90652369902908444438244893 33994638713590666664341835)
            ·
              refine ⟨50991958070385999996512753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33994638713590666664341835 50991958070385999996512753)
              ·
                refine ⟨38243968552789499997384565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50991958070385999996512753 38243968552789499997384565)
                ·
                  refine ⟨3585372051824015624754803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38243968552789499997384565 3585372051824015624754803)
                  ·
                    refine ⟨5378058077736023437132205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3585372051824015624754803 5378058077736023437132205)
                    ·
                      refine ⟨2016771779151008788924577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5378058077736023437132205 2016771779151008788924577)
                      ·
                        rfl

theorem cell23_3927649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_3927649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927649 prefixEnd_3927649 := by exact prefixLift 3927649
  have htrace : WordTrace (prefixWord ++ tailWord_3927649) baseStart_3927649 baseEnd_3927649 := by
    simpa [prefixWord, tailWord_3927649, baseEnd_3927649] using wordTrace_append hprefix tailTrace_3927649
  have hstable : (prefixWord ++ tailWord_3927649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927649).length < 2 ^ (prefixWord ++ tailWord_3927649).sum := by decide
  have hdescent : baseEnd_3927649 < baseStart_3927649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927656 : List Nat := [2, 1, 4, 3, 1, 3, 1, 2, 6]
def baseStart_3927656 : Nat := 118140960795 + 3927656 * 2 ^ 59
def prefixEnd_3927656 : Nat := 4983230072969 + 3 ^ 40 * 3927656 * 2
def baseEnd_3927656 : Nat := 224086152612843362393005

theorem tailTrace_3927656 : CollatzResearch.WordTrace tailWord_3927656 prefixEnd_3927656 224086152612843362393005 := by
  unfold tailWord_3927656
  simp only [CollatzResearch.WordTrace]
  refine ⟨71626691529390288542785411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95502255372520384723713881 71626691529390288542785411)
  ·
    refine ⟨107440037294085432814178117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71626691529390288542785411 107440037294085432814178117)
    ·
      refine ⟨20145006992641018652658397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107440037294085432814178117 20145006992641018652658397)
      ·
        refine ⟨7554377622240381994746899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20145006992641018652658397 7554377622240381994746899)
        ·
          refine ⟨11331566433360572992120349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7554377622240381994746899 11331566433360572992120349)
          ·
            refine ⟨4249337412510214872045131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11331566433360572992120349 4249337412510214872045131)
            ·
              refine ⟨6374006118765322308067697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4249337412510214872045131 6374006118765322308067697)
              ·
                refine ⟨4780504589073991731050773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6374006118765322308067697 4780504589073991731050773)
                ·
                  refine ⟨224086152612843362393005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4780504589073991731050773 224086152612843362393005)
                  ·
                    rfl

theorem cell23_3927656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 6].length) (baseStart_3927656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927656 prefixEnd_3927656 := by exact prefixLift 3927656
  have htrace : WordTrace (prefixWord ++ tailWord_3927656) baseStart_3927656 baseEnd_3927656 := by
    simpa [prefixWord, tailWord_3927656, baseEnd_3927656] using wordTrace_append hprefix tailTrace_3927656
  have hstable : (prefixWord ++ tailWord_3927656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927656).length < 2 ^ (prefixWord ++ tailWord_3927656).sum := by decide
  have hdescent : baseEnd_3927656 < baseStart_3927656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927666 : List Nat := [3, 2, 1, 2, 3, 1, 1, 3, 3, 1, 3]
def baseStart_3927666 : Nat := 118140960795 + 3927666 * 2 ^ 59
def prefixEnd_3927666 : Nat := 4983230072969 + 3 ^ 40 * 3927666 * 2
def baseEnd_3927666 : Nat := 2016780508322135222411999

theorem tailTrace_3927666 : CollatzResearch.WordTrace tailWord_3927666 prefixEnd_3927666 2016780508322135222411999 := by
  unfold tailWord_3927666
  simp only [CollatzResearch.WordTrace]
  refine ⟨35813436947186087198358713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95502498525829565862289901 35813436947186087198358713)
  ·
    refine ⟨26860077710389565398769035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35813436947186087198358713 26860077710389565398769035)
    ·
      refine ⟨40290116565584348098153553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26860077710389565398769035 40290116565584348098153553)
      ·
        refine ⟨30217587424188261073615165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40290116565584348098153553 30217587424188261073615165)
        ·
          refine ⟨11331595284070597902605687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30217587424188261073615165 11331595284070597902605687)
          ·
            refine ⟨16997392926105896853908531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11331595284070597902605687 16997392926105896853908531)
            ·
              refine ⟨25496089389158845280862797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16997392926105896853908531 25496089389158845280862797)
              ·
                refine ⟨9561033520934566980323549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25496089389158845280862797 9561033520934566980323549)
                ·
                  refine ⟨3585387570350462617621331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9561033520934566980323549 3585387570350462617621331)
                  ·
                    refine ⟨5378081355525693926431997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3585387570350462617621331 5378081355525693926431997)
                    ·
                      refine ⟨2016780508322135222411999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5378081355525693926431997 2016780508322135222411999)
                      ·
                        rfl

theorem cell23_3927666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_3927666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927666 prefixEnd_3927666 := by exact prefixLift 3927666
  have htrace : WordTrace (prefixWord ++ tailWord_3927666) baseStart_3927666 baseEnd_3927666 := by
    simpa [prefixWord, tailWord_3927666, baseEnd_3927666] using wordTrace_append hprefix tailTrace_3927666
  have hstable : (prefixWord ++ tailWord_3927666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927666).length < 2 ^ (prefixWord ++ tailWord_3927666).sum := by decide
  have hdescent : baseEnd_3927666 < baseStart_3927666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927689 : List Nat := [1, 2, 1, 1, 4, 1, 3, 4, 1, 1, 4]
def baseStart_3927689 : Nat := 118140960795 + 3927689 * 2 ^ 59
def prefixEnd_3927689 : Nat := 4983230072969 + 3 ^ 40 * 3927689 * 2
def baseEnd_3927689 : Nat := 2016792318377188632424393

theorem tailTrace_3927689 : CollatzResearch.WordTrace tailWord_3927689 prefixEnd_3927689 2016792318377188632424393 := by
  unfold tailWord_3927689
  simp only [CollatzResearch.WordTrace]
  refine ⟨143254586667661023721522121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95503057778440682481014747 143254586667661023721522121)
  ·
    refine ⟨107440940000745767791141591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143254586667661023721522121 107440940000745767791141591)
    ·
      refine ⟨161161410001118651686712387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107440940000745767791141591 161161410001118651686712387)
      ·
        refine ⟨241742115001677977530068581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161161410001118651686712387 241742115001677977530068581)
        ·
          refine ⟨45326646562814620786887859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241742115001677977530068581 45326646562814620786887859)
          ·
            refine ⟨67989969844221931180331789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45326646562814620786887859 67989969844221931180331789)
            ·
              refine ⟨25496238691583224192624421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67989969844221931180331789 25496238691583224192624421)
              ·
                refine ⟨4780544754671854536117079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25496238691583224192624421 4780544754671854536117079)
                ·
                  refine ⟨7170817132007781804175619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4780544754671854536117079 7170817132007781804175619)
                  ·
                    refine ⟨10756225698011672706263429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7170817132007781804175619 10756225698011672706263429)
                    ·
                      refine ⟨2016792318377188632424393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10756225698011672706263429 2016792318377188632424393)
                      ·
                        rfl

theorem cell23_3927689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 1, 4].length) (baseStart_3927689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927689 prefixEnd_3927689 := by exact prefixLift 3927689
  have htrace : WordTrace (prefixWord ++ tailWord_3927689) baseStart_3927689 baseEnd_3927689 := by
    simpa [prefixWord, tailWord_3927689, baseEnd_3927689] using wordTrace_append hprefix tailTrace_3927689
  have hstable : (prefixWord ++ tailWord_3927689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927689).length < 2 ^ (prefixWord ++ tailWord_3927689).sum := by decide
  have hdescent : baseEnd_3927689 < baseStart_3927689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927692 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 3, 1, 5]
def baseStart_3927692 : Nat := 118140960795 + 3927692 * 2 ^ 59
def prefixEnd_3927692 : Nat := 4983230072969 + 3 ^ 40 * 3927692 * 2
def baseEnd_3927692 : Nat := 2016793858819152120686879

theorem tailTrace_3927692 : CollatzResearch.WordTrace tailWord_3927692 prefixEnd_3927692 2016793858819152120686879 := by
  unfold tailWord_3927692
  simp only [CollatzResearch.WordTrace]
  refine ⟨71627348043325077616940665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95503130724433436822587553 71627348043325077616940665)
  ·
    refine ⟨53720511032493808212705499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71627348043325077616940665 53720511032493808212705499)
    ·
      refine ⟨80580766548740712319058249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53720511032493808212705499 80580766548740712319058249)
      ·
        refine ⟨60435574911555534239293687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80580766548740712319058249 60435574911555534239293687)
        ·
          refine ⟨90653362367333301358940531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60435574911555534239293687 90653362367333301358940531)
          ·
            refine ⟨135980043550999952038410797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90653362367333301358940531 135980043550999952038410797)
            ·
              refine ⟨50992516331624982014404049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135980043550999952038410797 50992516331624982014404049)
              ·
                refine ⟨38244387248718736510803037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50992516331624982014404049 38244387248718736510803037)
                ·
                  refine ⟨14341645218269526191551139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38244387248718736510803037 14341645218269526191551139)
                  ·
                    refine ⟨21512467827404289287326709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14341645218269526191551139 21512467827404289287326709)
                    ·
                      refine ⟨2016793858819152120686879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21512467827404289287326709 2016793858819152120686879)
                      ·
                        rfl

theorem cell23_3927692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_3927692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927692 prefixEnd_3927692 := by exact prefixLift 3927692
  have htrace : WordTrace (prefixWord ++ tailWord_3927692) baseStart_3927692 baseEnd_3927692 := by
    simpa [prefixWord, tailWord_3927692, baseEnd_3927692] using wordTrace_append hprefix tailTrace_3927692
  have hstable : (prefixWord ++ tailWord_3927692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927692).length < 2 ^ (prefixWord ++ tailWord_3927692).sum := by decide
  have hdescent : baseEnd_3927692 < baseStart_3927692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927709 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_3927709 : Nat := 118140960795 + 3927709 * 2 ^ 59
def prefixEnd_3927709 : Nat := 4983230072969 + 3 ^ 40 * 3927709 * 2
def baseEnd_3927709 : Nat := 2016802587990278554174301

theorem tailTrace_3927709 : CollatzResearch.WordTrace tailWord_3927709 prefixEnd_3927709 2016802587990278554174301 := by
  unfold tailWord_3927709
  simp only [CollatzResearch.WordTrace]
  refine ⟨143255316127588567137250181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95503544085059044758166787 143255316127588567137250181)
  ·
    refine ⟨26860371773922856338234409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143255316127588567137250181 26860371773922856338234409)
    ·
      refine ⟨20145278830442142253675807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26860371773922856338234409 20145278830442142253675807)
      ·
        refine ⟨30217918245663213380513711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20145278830442142253675807 30217918245663213380513711)
        ·
          refine ⟨45326877368494820070770567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30217918245663213380513711 45326877368494820070770567)
          ·
            refine ⟨67990316052742230106155851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45326877368494820070770567 67990316052742230106155851)
            ·
              refine ⟨101985474079113345159233777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67990316052742230106155851 101985474079113345159233777)
              ·
                refine ⟨76489105559335008869425333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101985474079113345159233777 76489105559335008869425333)
                ·
                  refine ⟨7170853646187657081508625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76489105559335008869425333 7170853646187657081508625)
                  ·
                    refine ⟨5378140234640742811131469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7170853646187657081508625 5378140234640742811131469)
                    ·
                      refine ⟨2016802587990278554174301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5378140234640742811131469 2016802587990278554174301)
                      ·
                        rfl

theorem cell23_3927709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_3927709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927709 prefixEnd_3927709 := by exact prefixLift 3927709
  have htrace : WordTrace (prefixWord ++ tailWord_3927709) baseStart_3927709 baseEnd_3927709 := by
    simpa [prefixWord, tailWord_3927709, baseEnd_3927709] using wordTrace_append hprefix tailTrace_3927709
  have hstable : (prefixWord ++ tailWord_3927709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927709).length < 2 ^ (prefixWord ++ tailWord_3927709).sum := by decide
  have hdescent : baseEnd_3927709 < baseStart_3927709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927712 : List Nat := [2, 1, 1, 4, 3, 1, 11]
def baseStart_3927712 : Nat := 118140960795 + 3927712 * 2 ^ 59
def prefixEnd_3927712 : Nat := 4983230072969 + 3 ^ 40 * 3927712 * 2
def baseEnd_3927712 : Nat := 24898816400398049906627

theorem tailTrace_3927712 : CollatzResearch.WordTrace tailWord_3927712 prefixEnd_3927712 24898816400398049906627 := by
  unfold tailWord_3927712
  simp only [CollatzResearch.WordTrace]
  refine ⟨71627712773288849324804695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95503617031051799099739593 71627712773288849324804695)
  ·
    refine ⟨107441569159933273987207043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71627712773288849324804695 107441569159933273987207043)
    ·
      refine ⟨161162353739899910980810565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107441569159933273987207043 161162353739899910980810565)
      ·
        refine ⟨30217941326231233308901981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161162353739899910980810565 30217941326231233308901981)
        ·
          refine ⟨11331727997336712490838243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30217941326231233308901981 11331727997336712490838243)
          ·
            refine ⟨16997591996005068736257365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11331727997336712490838243 16997591996005068736257365)
            ·
              refine ⟨24898816400398049906627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16997591996005068736257365 24898816400398049906627)
              ·
                rfl

theorem cell23_3927712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 11].length) (baseStart_3927712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927712 prefixEnd_3927712 := by exact prefixLift 3927712
  have htrace : WordTrace (prefixWord ++ tailWord_3927712) baseStart_3927712 baseEnd_3927712 := by
    simpa [prefixWord, tailWord_3927712, baseEnd_3927712] using wordTrace_append hprefix tailTrace_3927712
  have hstable : (prefixWord ++ tailWord_3927712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927712).length < 2 ^ (prefixWord ++ tailWord_3927712).sum := by decide
  have hdescent : baseEnd_3927712 < baseStart_3927712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927733 : List Nat := [1, 3, 3, 3, 2, 1, 1, 3, 2, 4]
def baseStart_3927733 : Nat := 118140960795 + 3927733 * 2 ^ 59
def prefixEnd_3927733 : Nat := 4983230072969 + 3 ^ 40 * 3927733 * 2
def baseEnd_3927733 : Nat := 672271637175328820091397

theorem tailTrace_3927733 : CollatzResearch.WordTrace tailWord_3927733 prefixEnd_3927733 672271637175328820091397 := by
  unfold tailWord_3927733
  simp only [CollatzResearch.WordTrace]
  refine ⟨143256191479501619236123853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95504127653001079490749235 143256191479501619236123853)
  ·
    refine ⟨53721071804813107213546445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143256191479501619236123853 53721071804813107213546445)
    ·
      refine ⟨20145401926804915205079917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53721071804813107213546445 20145401926804915205079917)
      ·
        refine ⟨7554525722551843201904969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20145401926804915205079917 7554525722551843201904969)
        ·
          refine ⟨5665894291913882401428727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7554525722551843201904969 5665894291913882401428727)
          ·
            refine ⟨8498841437870823602143091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5665894291913882401428727 8498841437870823602143091)
            ·
              refine ⟨12748262156806235403214637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8498841437870823602143091 12748262156806235403214637)
              ·
                refine ⟨4780598308802338276205489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12748262156806235403214637 4780598308802338276205489)
                ·
                  refine ⟨3585448731601753707154117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4780598308802338276205489 3585448731601753707154117)
                  ·
                    refine ⟨672271637175328820091397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3585448731601753707154117 672271637175328820091397)
                    ·
                      rfl

theorem cell23_3927733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_3927733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927733 prefixEnd_3927733 := by exact prefixLift 3927733
  have htrace : WordTrace (prefixWord ++ tailWord_3927733) baseStart_3927733 baseEnd_3927733 := by
    simpa [prefixWord, tailWord_3927733, baseEnd_3927733] using wordTrace_append hprefix tailTrace_3927733
  have hstable : (prefixWord ++ tailWord_3927733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927733).length < 2 ^ (prefixWord ++ tailWord_3927733).sum := by decide
  have hdescent : baseEnd_3927733 < baseStart_3927733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927749 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 2, 7, 2]
def baseStart_3927749 : Nat := 118140960795 + 3927749 * 2 ^ 59
def prefixEnd_3927749 : Nat := 4983230072969 + 3 ^ 40 * 3927749 * 2
def baseEnd_3927749 : Nat := 2016823127216458397674117

theorem tailTrace_3927749 : CollatzResearch.WordTrace tailWord_3927749 prefixEnd_3927749 2016823127216458397674117 := by
  unfold tailWord_3927749
  simp only [CollatzResearch.WordTrace]
  refine ⟨143256775047443653968706301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95504516698295769312470867 143256775047443653968706301)
  ·
    refine ⟨53721290642791370238264863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143256775047443653968706301 53721290642791370238264863)
    ·
      refine ⟨80581935964187055357397295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53721290642791370238264863 80581935964187055357397295)
      ·
        refine ⟨120872903946280583036095943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80581935964187055357397295 120872903946280583036095943)
        ·
          refine ⟨181309355919420874554143915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120872903946280583036095943 181309355919420874554143915)
          ·
            refine ⟨271964033879131311831215873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181309355919420874554143915 271964033879131311831215873)
            ·
              refine ⟨203973025409348483873411905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271964033879131311831215873 203973025409348483873411905)
              ·
                refine ⟨152979769057011362905058929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203973025409348483873411905 152979769057011362905058929)
                ·
                  refine ⟨114734826792758522178794197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152979769057011362905058929 114734826792758522178794197)
                  ·
                    refine ⟨2689097502955277863565489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 114734826792758522178794197 2689097502955277863565489)
                    ·
                      refine ⟨2016823127216458397674117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2689097502955277863565489 2016823127216458397674117)
                      ·
                        rfl

theorem cell23_3927749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 7, 2].length) (baseStart_3927749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927749 prefixEnd_3927749 := by exact prefixLift 3927749
  have htrace : WordTrace (prefixWord ++ tailWord_3927749) baseStart_3927749 baseEnd_3927749 := by
    simpa [prefixWord, tailWord_3927749, baseEnd_3927749] using wordTrace_append hprefix tailTrace_3927749
  have hstable : (prefixWord ++ tailWord_3927749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927749).length < 2 ^ (prefixWord ++ tailWord_3927749).sum := by decide
  have hdescent : baseEnd_3927749 < baseStart_3927749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927789 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_3927789 : Nat := 118140960795 + 3927789 * 2 ^ 59
def prefixEnd_3927789 : Nat := 4983230072969 + 3 ^ 40 * 3927789 * 2
def baseEnd_3927789 : Nat := 672281222147546080391311

theorem tailTrace_3927789 : CollatzResearch.WordTrace tailWord_3927789 prefixEnd_3927789 672281222147546080391311 := by
  unfold tailWord_3927789
  simp only [CollatzResearch.WordTrace]
  refine ⟨143258233967298740800162421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95505489311532493866774947 143258233967298740800162421)
  ·
    refine ⟨13430459434434256950015227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143258233967298740800162421 13430459434434256950015227)
    ·
      refine ⟨20145689151651385425022841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13430459434434256950015227 20145689151651385425022841)
      ·
        refine ⟨15109266863738539068767131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20145689151651385425022841 15109266863738539068767131)
        ·
          refine ⟨22663900295607808603150697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15109266863738539068767131 22663900295607808603150697)
          ·
            refine ⟨16997925221705856452363023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22663900295607808603150697 16997925221705856452363023)
            ·
              refine ⟨25496887832558784678544535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16997925221705856452363023 25496887832558784678544535)
              ·
                refine ⟨38245331748838177017816803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25496887832558784678544535 38245331748838177017816803)
                ·
                  refine ⟨57367997623257265526725205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38245331748838177017816803 57367997623257265526725205)
                  ·
                    refine ⟨672281222147546080391311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57367997623257265526725205 672281222147546080391311)
                    ·
                      rfl

theorem cell23_3927789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_3927789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927789 prefixEnd_3927789 := by exact prefixLift 3927789
  have htrace : WordTrace (prefixWord ++ tailWord_3927789) baseStart_3927789 baseEnd_3927789 := by
    simpa [prefixWord, tailWord_3927789, baseEnd_3927789] using wordTrace_append hprefix tailTrace_3927789
  have hstable : (prefixWord ++ tailWord_3927789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927789).length < 2 ^ (prefixWord ++ tailWord_3927789).sum := by decide
  have hdescent : baseEnd_3927789 < baseStart_3927789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927836 : List Nat := [2, 2, 3, 1, 1, 2, 1, 6, 5]
def baseStart_3927836 : Nat := 118140960795 + 3927836 * 2 ^ 59
def prefixEnd_3927836 : Nat := 4983230072969 + 3 ^ 40 * 3927836 * 2
def baseEnd_3927836 : Nat := 224096422225933284142913

theorem tailTrace_3927836 : CollatzResearch.WordTrace tailWord_3927836 prefixEnd_3927836 224096422225933284142913 := by
  unfold tailWord_3927836
  simp only [CollatzResearch.WordTrace]
  refine ⟨71629974099064233913561681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95506632132085645218082241 71629974099064233913561681)
  ·
    refine ⟨53722480574298175435171261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71629974099064233913561681 53722480574298175435171261)
    ·
      refine ⟨20145930215361815788189223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53722480574298175435171261 20145930215361815788189223)
      ·
        refine ⟨30218895323042723682283835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20145930215361815788189223 30218895323042723682283835)
        ·
          refine ⟨45328342984564085523425753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30218895323042723682283835 45328342984564085523425753)
          ·
            refine ⟨33996257238423064142569315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45328342984564085523425753 33996257238423064142569315)
            ·
              refine ⟨50994385857634596213853973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33996257238423064142569315 50994385857634596213853973)
              ·
                refine ⟨2390361837076621697524405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50994385857634596213853973 2390361837076621697524405)
                ·
                  refine ⟨224096422225933284142913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2390361837076621697524405 224096422225933284142913)
                  ·
                    rfl

theorem cell23_3927836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 5].length) (baseStart_3927836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927836 prefixEnd_3927836 := by exact prefixLift 3927836
  have htrace : WordTrace (prefixWord ++ tailWord_3927836) baseStart_3927836 baseEnd_3927836 := by
    simpa [prefixWord, tailWord_3927836, baseEnd_3927836] using wordTrace_append hprefix tailTrace_3927836
  have hstable : (prefixWord ++ tailWord_3927836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927836).length < 2 ^ (prefixWord ++ tailWord_3927836).sum := by decide
  have hdescent : baseEnd_3927836 < baseStart_3927836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927870 : List Nat := [4, 2, 1, 2, 2, 3, 1, 3, 5]
def baseStart_3927870 : Nat := 118140960795 + 3927870 * 2 ^ 59
def prefixEnd_3927870 : Nat := 4983230072969 + 3 ^ 40 * 3927870 * 2
def baseEnd_3927870 : Nat := 224098362041739158251229

theorem tailTrace_3927870 : CollatzResearch.WordTrace tailWord_3927870 prefixEnd_3927870 224098362041739158251229 := by
  unfold tailWord_3927870
  simp only [CollatzResearch.WordTrace]
  refine ⟨17907648535000661454232633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95507458853336861089240709 17907648535000661454232633)
  ·
    refine ⟨13430736401250496090674475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17907648535000661454232633 13430736401250496090674475)
    ·
      refine ⟨20146104601875744136011713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13430736401250496090674475 20146104601875744136011713)
      ·
        refine ⟨15109578451406808102008785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20146104601875744136011713 15109578451406808102008785)
        ·
          refine ⟨11332183838555106076506589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15109578451406808102008785 11332183838555106076506589)
          ·
            refine ⟨4249568939458164778689971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11332183838555106076506589 4249568939458164778689971)
            ·
              refine ⟨6374353409187247168034957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4249568939458164778689971 6374353409187247168034957)
              ·
                refine ⟨2390382528445217688013109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6374353409187247168034957 2390382528445217688013109)
                ·
                  refine ⟨224098362041739158251229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2390382528445217688013109 224098362041739158251229)
                  ·
                    rfl

theorem cell23_3927870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_3927870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927870 prefixEnd_3927870 := by exact prefixLift 3927870
  have htrace : WordTrace (prefixWord ++ tailWord_3927870) baseStart_3927870 baseEnd_3927870 := by
    simpa [prefixWord, tailWord_3927870, baseEnd_3927870] using wordTrace_append hprefix tailTrace_3927870
  have hstable : (prefixWord ++ tailWord_3927870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927870).length < 2 ^ (prefixWord ++ tailWord_3927870).sum := by decide
  have hdescent : baseEnd_3927870 < baseStart_3927870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927943 : List Nat := [1, 1, 4, 2, 4, 1, 2, 2, 6]
def baseStart_3927943 : Nat := 118140960795 + 3927943 * 2 ^ 59
def prefixEnd_3927943 : Nat := 4983230072969 + 3 ^ 40 * 3927943 * 2
def baseEnd_3927943 : Nat := 224102526940381182072025

theorem tailTrace_3927943 : CollatzResearch.WordTrace tailWord_3927943 prefixEnd_3927943 224102526940381182072025 := by
  unfold tailWord_3927943
  simp only [CollatzResearch.WordTrace]
  refine ⟨143263850808740825101268483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95509233872493883400845655 143263850808740825101268483)
  ·
    refine ⟨214895776213111237651902725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143263850808740825101268483 214895776213111237651902725)
    ·
      refine ⟨40292958039958357059731761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214895776213111237651902725 40292958039958357059731761)
      ·
        refine ⟨30219718529968767794798821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40292958039958357059731761 30219718529968767794798821)
        ·
          refine ⟨5666197224369143961524779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30219718529968767794798821 5666197224369143961524779)
          ·
            refine ⟨8499295836553715942287169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5666197224369143961524779 8499295836553715942287169)
            ·
              refine ⟨6374471877415286956715377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8499295836553715942287169 6374471877415286956715377)
              ·
                refine ⟨4780853908061465217536533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6374471877415286956715377 4780853908061465217536533)
                ·
                  refine ⟨224102526940381182072025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4780853908061465217536533 224102526940381182072025)
                  ·
                    rfl

theorem cell23_3927943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 6].length) (baseStart_3927943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927943 prefixEnd_3927943 := by exact prefixLift 3927943
  have htrace : WordTrace (prefixWord ++ tailWord_3927943) baseStart_3927943 baseEnd_3927943 := by
    simpa [prefixWord, tailWord_3927943, baseEnd_3927943] using wordTrace_append hprefix tailTrace_3927943
  have hstable : (prefixWord ++ tailWord_3927943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927943).length < 2 ^ (prefixWord ++ tailWord_3927943).sum := by decide
  have hdescent : baseEnd_3927943 < baseStart_3927943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927979 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 5]
def baseStart_3927979 : Nat := 118140960795 + 3927979 * 2 ^ 59
def prefixEnd_3927979 : Nat := 4983230072969 + 3 ^ 40 * 3927979 * 2
def baseEnd_3927979 : Nat := 2016941227766992497798059

theorem tailTrace_3927979 : CollatzResearch.WordTrace tailWord_3927979 prefixEnd_3927979 2016941227766992497798059 := by
  unfold tailWord_3927979
  simp only [CollatzResearch.WordTrace]
  refine ⟨143265163836610403249578991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95510109224406935499719327 143265163836610403249578991)
  ·
    refine ⟨214897745754915604874368487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143265163836610403249578991 214897745754915604874368487)
    ·
      refine ⟨322346618632373407311552731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214897745754915604874368487 322346618632373407311552731)
      ·
        refine ⟨483519927948560110967329097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322346618632373407311552731 483519927948560110967329097)
        ·
          refine ⟨362639945961420083225496823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483519927948560110967329097 362639945961420083225496823)
          ·
            refine ⟨543959918942130124838245235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362639945961420083225496823 543959918942130124838245235)
            ·
              refine ⟨815939878413195187257367853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543959918942130124838245235 815939878413195187257367853)
              ·
                refine ⟨305977454404948195221512945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 815939878413195187257367853 305977454404948195221512945)
                ·
                  refine ⟨229483090803711146416134709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305977454404948195221512945 229483090803711146416134709)
                  ·
                    refine ⟨21514039762847919976512629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 229483090803711146416134709 21514039762847919976512629)
                    ·
                      refine ⟨2016941227766992497798059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21514039762847919976512629 2016941227766992497798059)
                      ·
                        rfl

theorem cell23_3927979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 5].length) (baseStart_3927979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927979 prefixEnd_3927979 := by exact prefixLift 3927979
  have htrace : WordTrace (prefixWord ++ tailWord_3927979) baseStart_3927979 baseEnd_3927979 := by
    simpa [prefixWord, tailWord_3927979, baseEnd_3927979] using wordTrace_append hprefix tailTrace_3927979
  have hstable : (prefixWord ++ tailWord_3927979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927979).length < 2 ^ (prefixWord ++ tailWord_3927979).sum := by decide
  have hdescent : baseEnd_3927979 < baseStart_3927979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927993 : List Nat := [1, 2, 1, 4, 2, 1, 3, 3, 1, 1, 4]
def baseStart_3927993 : Nat := 118140960795 + 3927993 * 2 ^ 59
def prefixEnd_3927993 : Nat := 4983230072969 + 3 ^ 40 * 3927993 * 2
def baseEnd_3927993 : Nat := 2016948416496155443022995

theorem tailTrace_3927993 : CollatzResearch.WordTrace tailWord_3927993 prefixEnd_3927993 2016948416496155443022995 := by
  unfold tailWord_3927993
  simp only [CollatzResearch.WordTrace]
  refine ⟨143265674458559683640588633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95510449639039789093725755 143265674458559683640588633)
  ·
    refine ⟨107449255843919762730441475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143265674458559683640588633 107449255843919762730441475)
    ·
      refine ⟨161173883765879644095662213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107449255843919762730441475 161173883765879644095662213)
      ·
        refine ⟨30220103206102433267936665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161173883765879644095662213 30220103206102433267936665)
        ·
          refine ⟨22665077404576824950952499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30220103206102433267936665 22665077404576824950952499)
          ·
            refine ⟨33997616106865237426428749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22665077404576824950952499 33997616106865237426428749)
            ·
              refine ⟨12749106040074464034910781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33997616106865237426428749 12749106040074464034910781)
              ·
                refine ⟨4780914765027924013091543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12749106040074464034910781 4780914765027924013091543)
                ·
                  refine ⟨7171372147541886019637315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4780914765027924013091543 7171372147541886019637315)
                  ·
                    refine ⟨10757058221312829029455973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7171372147541886019637315 10757058221312829029455973)
                    ·
                      refine ⟨2016948416496155443022995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10757058221312829029455973 2016948416496155443022995)
                      ·
                        rfl

theorem cell23_3927993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_3927993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927993 prefixEnd_3927993 := by exact prefixLift 3927993
  have htrace : WordTrace (prefixWord ++ tailWord_3927993) baseStart_3927993 baseEnd_3927993 := by
    simpa [prefixWord, tailWord_3927993, baseEnd_3927993] using wordTrace_append hprefix tailTrace_3927993
  have hstable : (prefixWord ++ tailWord_3927993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927993).length < 2 ^ (prefixWord ++ tailWord_3927993).sum := by decide
  have hdescent : baseEnd_3927993 < baseStart_3927993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3927999 : List Nat := [1, 1, 2, 2, 2, 1, 14]
def baseStart_3927999 : Nat := 118140960795 + 3927999 * 2 ^ 59
def prefixEnd_3927999 : Nat := 4983230072969 + 3 ^ 40 * 3927999 * 2
def baseEnd_3927999 : Nat := 24900635770124474315407

theorem tailTrace_3927999 : CollatzResearch.WordTrace tailWord_3927999 prefixEnd_3927999 24900635770124474315407 := by
  unfold tailWord_3927999
  simp only [CollatzResearch.WordTrace]
  refine ⟨143265893296537946665307051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95510595531025297776871367 143265893296537946665307051)
  ·
    refine ⟨214898839944806919997960577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143265893296537946665307051 214898839944806919997960577)
    ·
      refine ⟨161174129958605189998470433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214898839944806919997960577 161174129958605189998470433)
      ·
        refine ⟨120880597468953892498852825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161174129958605189998470433 120880597468953892498852825)
        ·
          refine ⟨90660448101715419374139619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120880597468953892498852825 90660448101715419374139619)
          ·
            refine ⟨135990672152573129061209429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90660448101715419374139619 135990672152573129061209429)
            ·
              refine ⟨24900635770124474315407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 135990672152573129061209429 24900635770124474315407)
              ·
                rfl

theorem cell23_3927999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 14].length) (baseStart_3927999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3927999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3927999 prefixEnd_3927999 := by exact prefixLift 3927999
  have htrace : WordTrace (prefixWord ++ tailWord_3927999) baseStart_3927999 baseEnd_3927999 := by
    simpa [prefixWord, tailWord_3927999, baseEnd_3927999] using wordTrace_append hprefix tailTrace_3927999
  have hstable : (prefixWord ++ tailWord_3927999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3927999).length < 2 ^ (prefixWord ++ tailWord_3927999).sum := by decide
  have hdescent : baseEnd_3927999 < baseStart_3927999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3927999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928010 : List Nat := [3, 1, 2, 1, 2, 1, 3, 3, 3, 2, 2]
def baseStart_3928010 : Nat := 118140960795 + 3928010 * 2 ^ 59
def prefixEnd_3928010 : Nat := 4983230072969 + 3 ^ 40 * 3928010 * 2
def baseEnd_3928010 : Nat := 2016957145667281876510417

theorem tailTrace_3928010 : CollatzResearch.WordTrace tailWord_3928010 prefixEnd_3928010 2016957145667281876510417 := by
  unfold tailWord_3928010
  simp only [CollatzResearch.WordTrace]
  refine ⟨35816573624874523885989371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95510862999665397029304989 35816573624874523885989371)
  ·
    refine ⟨53724860437311785828984057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35816573624874523885989371 53724860437311785828984057)
    ·
      refine ⟨40293645327983839371738043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53724860437311785828984057 40293645327983839371738043)
      ·
        refine ⟨60440467991975759057607065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40293645327983839371738043 60440467991975759057607065)
        ·
          refine ⟨45330350993981819293205299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60440467991975759057607065 45330350993981819293205299)
          ·
            refine ⟨67995526490972728939807949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45330350993981819293205299 67995526490972728939807949)
            ·
              refine ⟨25498322434114773352427981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67995526490972728939807949 25498322434114773352427981)
              ·
                refine ⟨9561870912793040007160493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25498322434114773352427981 9561870912793040007160493)
                ·
                  refine ⟨3585701592297390002685185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9561870912793040007160493 3585701592297390002685185)
                  ·
                    refine ⟨2689276194223042502013889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3585701592297390002685185 2689276194223042502013889)
                    ·
                      refine ⟨2016957145667281876510417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2689276194223042502013889 2016957145667281876510417)
                      ·
                        rfl

theorem cell23_3928010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_3928010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928010 prefixEnd_3928010 := by exact prefixLift 3928010
  have htrace : WordTrace (prefixWord ++ tailWord_3928010) baseStart_3928010 baseEnd_3928010 := by
    simpa [prefixWord, tailWord_3928010, baseEnd_3928010] using wordTrace_append hprefix tailTrace_3928010
  have hstable : (prefixWord ++ tailWord_3928010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928010).length < 2 ^ (prefixWord ++ tailWord_3928010).sum := by decide
  have hdescent : baseEnd_3928010 < baseStart_3928010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928060 : List Nat := [2, 2, 2, 1, 2, 2, 2, 4, 2, 1, 3]
def baseStart_3928060 : Nat := 118140960795 + 3928060 * 2 ^ 59
def prefixEnd_3928060 : Nat := 4983230072969 + 3 ^ 40 * 3928060 * 2
def baseEnd_3928060 : Nat := 2016982819700006680885187

theorem tailTrace_3928060 : CollatzResearch.WordTrace tailWord_3928060 prefixEnd_3928060 2016982819700006680885187 := by
  unfold tailWord_3928060
  simp only [CollatzResearch.WordTrace]
  refine ⟨71634059074658477041638817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95512078766211302722185089 71634059074658477041638817)
  ·
    refine ⟨53725544305993857781229113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71634059074658477041638817 53725544305993857781229113)
    ·
      refine ⟨40294158229495393335921835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53725544305993857781229113 40294158229495393335921835)
      ·
        refine ⟨60441237344243090003882753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40294158229495393335921835 60441237344243090003882753)
        ·
          refine ⟨45330928008182317502912065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60441237344243090003882753 45330928008182317502912065)
          ·
            refine ⟨33998196006136738127184049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45330928008182317502912065 33998196006136738127184049)
            ·
              refine ⟨25498647004602553595388037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33998196006136738127184049 25498647004602553595388037)
              ·
                refine ⟨4780996313362978799135257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25498647004602553595388037 4780996313362978799135257)
                ·
                  refine ⟨3585747235022234099351443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4780996313362978799135257 3585747235022234099351443)
                  ·
                    refine ⟨5378620852533351149027165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3585747235022234099351443 5378620852533351149027165)
                    ·
                      refine ⟨2016982819700006680885187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5378620852533351149027165 2016982819700006680885187)
                      ·
                        rfl

theorem cell23_3928060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_3928060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928060 prefixEnd_3928060 := by exact prefixLift 3928060
  have htrace : WordTrace (prefixWord ++ tailWord_3928060) baseStart_3928060 baseEnd_3928060 := by
    simpa [prefixWord, tailWord_3928060, baseEnd_3928060] using wordTrace_append hprefix tailTrace_3928060
  have hstable : (prefixWord ++ tailWord_3928060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928060).length < 2 ^ (prefixWord ++ tailWord_3928060).sum := by decide
  have hdescent : baseEnd_3928060 < baseStart_3928060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928076 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 1, 8]
def baseStart_3928076 : Nat := 118140960795 + 3928076 * 2 ^ 59
def prefixEnd_3928076 : Nat := 4983230072969 + 3 ^ 40 * 3928076 * 2
def baseEnd_3928076 : Nat := 672330345130159539428371

theorem tailTrace_3928076 : CollatzResearch.WordTrace tailWord_3928076 prefixEnd_3928076 672330345130159539428371 := by
  unfold tailWord_3928076
  simp only [CollatzResearch.WordTrace]
  refine ⟨71634350858629494407930041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95512467811505992543906721 71634350858629494407930041)
  ·
    refine ⟨53725763143972120805947531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71634350858629494407930041 53725763143972120805947531)
    ·
      refine ⟨80588644715958181208921297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53725763143972120805947531 80588644715958181208921297)
      ·
        refine ⟨60441483536968635906690973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80588644715958181208921297 60441483536968635906690973)
        ·
          refine ⟨22665556326363238465009115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60441483536968635906690973 22665556326363238465009115)
          ·
            refine ⟨33998334489544857697513673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22665556326363238465009115 33998334489544857697513673)
            ·
              refine ⟨25498750867158643273135255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33998334489544857697513673 25498750867158643273135255)
              ·
                refine ⟨38248126300737964909702883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25498750867158643273135255 38248126300737964909702883)
                ·
                  refine ⟨57372189451106947364554325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38248126300737964909702883 57372189451106947364554325)
                  ·
                    refine ⟨672330345130159539428371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57372189451106947364554325 672330345130159539428371)
                    ·
                      rfl

theorem cell23_3928076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_3928076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928076 prefixEnd_3928076 := by exact prefixLift 3928076
  have htrace : WordTrace (prefixWord ++ tailWord_3928076) baseStart_3928076 baseEnd_3928076 := by
    simpa [prefixWord, tailWord_3928076, baseEnd_3928076] using wordTrace_append hprefix tailTrace_3928076
  have hstable : (prefixWord ++ tailWord_3928076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928076).length < 2 ^ (prefixWord ++ tailWord_3928076).sum := by decide
  have hdescent : baseEnd_3928076 < baseStart_3928076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928087 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 3, 3, 2]
def baseStart_3928087 : Nat := 118140960795 + 3928087 * 2 ^ 59
def prefixEnd_3928087 : Nat := 4983230072969 + 3 ^ 40 * 3928087 * 2
def baseEnd_3928087 : Nat := 2016996683677678075247563

theorem tailTrace_3928087 : CollatzResearch.WordTrace tailWord_3928087 prefixEnd_3928087 2016996683677678075247563 := by
  unfold tailWord_3928087
  simp only [CollatzResearch.WordTrace]
  refine ⟨143269102920219137694510515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95512735280146091796340343 143269102920219137694510515)
  ·
    refine ⟨214903654380328706541765773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143269102920219137694510515 214903654380328706541765773)
    ·
      refine ⟨80588870392623264953162165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214903654380328706541765773 80588870392623264953162165)
      ·
        refine ⟨7555206599308431089358953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80588870392623264953162165 7555206599308431089358953)
        ·
          refine ⟨5666404949481323317019215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7555206599308431089358953 5666404949481323317019215)
          ·
            refine ⟨8499607424221984975528823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5666404949481323317019215 8499607424221984975528823)
            ·
              refine ⟨12749411136332977463293235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8499607424221984975528823 12749411136332977463293235)
              ·
                refine ⟨19124116704499466194939853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12749411136332977463293235 19124116704499466194939853)
                ·
                  refine ⟨7171543764187299823102445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19124116704499466194939853 7171543764187299823102445)
                  ·
                    refine ⟨2689328911570237433663417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7171543764187299823102445 2689328911570237433663417)
                    ·
                      refine ⟨2016996683677678075247563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2689328911570237433663417 2016996683677678075247563)
                      ·
                        rfl

theorem cell23_3928087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_3928087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928087 prefixEnd_3928087 := by exact prefixLift 3928087
  have htrace : WordTrace (prefixWord ++ tailWord_3928087) baseStart_3928087 baseEnd_3928087 := by
    simpa [prefixWord, tailWord_3928087, baseEnd_3928087] using wordTrace_append hprefix tailTrace_3928087
  have hstable : (prefixWord ++ tailWord_3928087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928087).length < 2 ^ (prefixWord ++ tailWord_3928087).sum := by decide
  have hdescent : baseEnd_3928087 < baseStart_3928087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928117 : List Nat := [1, 3, 3, 1, 1, 1, 3, 4, 2, 2, 2]
def baseStart_3928117 : Nat := 118140960795 + 3928117 * 2 ^ 59
def prefixEnd_3928117 : Nat := 4983230072969 + 3 ^ 40 * 3928117 * 2
def baseEnd_3928117 : Nat := 2017012088097312957872425

theorem tailTrace_3928117 : CollatzResearch.WordTrace tailWord_3928117 prefixEnd_3928117 2017012088097312957872425 := by
  unfold tailWord_3928117
  simp only [CollatzResearch.WordTrace]
  refine ⟨143270197110110452818102605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95513464740073635212068403 143270197110110452818102605)
  ·
    refine ⟨53726323916291419806788477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143270197110110452818102605 53726323916291419806788477)
    ·
      refine ⟨20147371468609282427545679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53726323916291419806788477 20147371468609282427545679)
      ·
        refine ⟨30221057202913923641318519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20147371468609282427545679 30221057202913923641318519)
        ·
          refine ⟨45331585804370885461977779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30221057202913923641318519 45331585804370885461977779)
          ·
            refine ⟨67997378706556328192966669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45331585804370885461977779 67997378706556328192966669)
            ·
              refine ⟨25499017014958623072362501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67997378706556328192966669 25499017014958623072362501)
              ·
                refine ⟨4781065690304741826067969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25499017014958623072362501 4781065690304741826067969)
                ·
                  refine ⟨3585799267728556369550977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4781065690304741826067969 3585799267728556369550977)
                  ·
                    refine ⟨2689349450796417277163233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3585799267728556369550977 2689349450796417277163233)
                    ·
                      refine ⟨2017012088097312957872425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2689349450796417277163233 2017012088097312957872425)
                      ·
                        rfl

theorem cell23_3928117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_3928117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928117 prefixEnd_3928117 := by exact prefixLift 3928117
  have htrace : WordTrace (prefixWord ++ tailWord_3928117) baseStart_3928117 baseEnd_3928117 := by
    simpa [prefixWord, tailWord_3928117, baseEnd_3928117] using wordTrace_append hprefix tailTrace_3928117
  have hstable : (prefixWord ++ tailWord_3928117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928117).length < 2 ^ (prefixWord ++ tailWord_3928117).sum := by decide
  have hdescent : baseEnd_3928117 < baseStart_3928117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928123 : List Nat := [1, 1, 1, 1, 1, 2, 1, 10, 5]
def baseStart_3928123 : Nat := 118140960795 + 3928123 * 2 ^ 59
def prefixEnd_3928123 : Nat := 4983230072969 + 3 ^ 40 * 3928123 * 2
def baseEnd_3928123 : Nat := 224112796553471103821933

theorem tailTrace_3928123 : CollatzResearch.WordTrace tailWord_3928123 prefixEnd_3928123 224112796553471103821933 := by
  unfold tailWord_3928123
  simp only [CollatzResearch.WordTrace]
  refine ⟨143270415948088715842821023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95513610632059143895214015 143270415948088715842821023)
  ·
    refine ⟨214905623922133073764231535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143270415948088715842821023 214905623922133073764231535)
    ·
      refine ⟨322358435883199610646347303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214905623922133073764231535 322358435883199610646347303)
      ·
        refine ⟨483537653824799415969520955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322358435883199610646347303 483537653824799415969520955)
        ·
          refine ⟨725306480737199123954281433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483537653824799415969520955 725306480737199123954281433)
          ·
            refine ⟨543979860552899342965711075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 725306480737199123954281433 543979860552899342965711075)
            ·
              refine ⟨815969790829349014448566613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543979860552899342965711075 815969790829349014448566613)
              ·
                refine ⟨2390536496570358440767285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 815969790829349014448566613 2390536496570358440767285)
                ·
                  refine ⟨224112796553471103821933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2390536496570358440767285 224112796553471103821933)
                  ·
                    rfl

theorem cell23_3928123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 5].length) (baseStart_3928123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928123 prefixEnd_3928123 := by exact prefixLift 3928123
  have htrace : WordTrace (prefixWord ++ tailWord_3928123) baseStart_3928123 baseEnd_3928123 := by
    simpa [prefixWord, tailWord_3928123, baseEnd_3928123] using wordTrace_append hprefix tailTrace_3928123
  have hstable : (prefixWord ++ tailWord_3928123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928123).length < 2 ^ (prefixWord ++ tailWord_3928123).sum := by decide
  have hdescent : baseEnd_3928123 < baseStart_3928123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928134 : List Nat := [6, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_3928134 : Nat := 118140960795 + 3928134 * 2 ^ 59
def prefixEnd_3928134 : Nat := 4983230072969 + 3 ^ 40 * 3928134 * 2
def baseEnd_3928134 : Nat := 2017020817268439391359847

theorem tailTrace_3928134 : CollatzResearch.WordTrace tailWord_3928134 prefixEnd_3928134 2017020817268439391359847 := by
  unfold tailWord_3928134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4477213035970277022545983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95513878100699243147647637 4477213035970277022545983)
  ·
    refine ⟨6715819553955415533818975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4477213035970277022545983 6715819553955415533818975)
    ·
      refine ⟨10073729330933123300728463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6715819553955415533818975 10073729330933123300728463)
      ·
        refine ⟨15110593996399684951092695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10073729330933123300728463 15110593996399684951092695)
        ·
          refine ⟨22665890994599527426639043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15110593996399684951092695 22665890994599527426639043)
          ·
            refine ⟨33998836491899291139958565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22665890994599527426639043 33998836491899291139958565)
            ·
              refine ⟨6374781842231117088742231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33998836491899291139958565 6374781842231117088742231)
              ·
                refine ⟨9562172763346675633113347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6374781842231117088742231 9562172763346675633113347)
                ·
                  refine ⟨14343259145020013449670021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9562172763346675633113347 14343259145020013449670021)
                  ·
                    refine ⟨2689361089691252521813129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14343259145020013449670021 2689361089691252521813129)
                    ·
                      refine ⟨2017020817268439391359847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2689361089691252521813129 2017020817268439391359847)
                      ·
                        rfl

theorem cell23_3928134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_3928134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928134 prefixEnd_3928134 := by exact prefixLift 3928134
  have htrace : WordTrace (prefixWord ++ tailWord_3928134) baseStart_3928134 baseEnd_3928134 := by
    simpa [prefixWord, tailWord_3928134, baseEnd_3928134] using wordTrace_append hprefix tailTrace_3928134
  have hstable : (prefixWord ++ tailWord_3928134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928134).length < 2 ^ (prefixWord ++ tailWord_3928134).sum := by decide
  have hdescent : baseEnd_3928134 < baseStart_3928134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928157 : List Nat := [1, 4, 4, 1, 1, 1, 1, 5, 5]
def baseStart_3928157 : Nat := 118140960795 + 3928157 * 2 ^ 59
def prefixEnd_3928157 : Nat := 4983230072969 + 3 ^ 40 * 3928157 * 2
def baseEnd_3928157 : Nat := 224114736369276977930249

theorem tailTrace_3928157 : CollatzResearch.WordTrace tailWord_3928157 prefixEnd_3928157 224114736369276977930249 := by
  unfold tailWord_3928157
  simp only [CollatzResearch.WordTrace]
  refine ⟨143271656029965539649558725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95514437353310359766372483 143271656029965539649558725)
  ·
    refine ⟨26863435505618538684292261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143271656029965539649558725 26863435505618538684292261)
    ·
      refine ⟨5036894157303476003304799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26863435505618538684292261 5036894157303476003304799)
      ·
        refine ⟨7555341235955214004957199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5036894157303476003304799 7555341235955214004957199)
        ·
          refine ⟨11333011853932821007435799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7555341235955214004957199 11333011853932821007435799)
          ·
            refine ⟨16999517780899231511153699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11333011853932821007435799 16999517780899231511153699)
            ·
              refine ⟨25499276671348847266730549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16999517780899231511153699 25499276671348847266730549)
              ·
                refine ⟨2390557187938954431255989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25499276671348847266730549 2390557187938954431255989)
                ·
                  refine ⟨224114736369276977930249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2390557187938954431255989 224114736369276977930249)
                  ·
                    rfl

theorem cell23_3928157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_3928157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928157 prefixEnd_3928157 := by exact prefixLift 3928157
  have htrace : WordTrace (prefixWord ++ tailWord_3928157) baseStart_3928157 baseEnd_3928157 := by
    simpa [prefixWord, tailWord_3928157, baseEnd_3928157] using wordTrace_append hprefix tailTrace_3928157
  have hstable : (prefixWord ++ tailWord_3928157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928157).length < 2 ^ (prefixWord ++ tailWord_3928157).sum := by decide
  have hdescent : baseEnd_3928157 < baseStart_3928157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928210 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_3928210 : Nat := 118140960795 + 3928210 * 2 ^ 59
def prefixEnd_3928210 : Nat := 4983230072969 + 3 ^ 40 * 3928210 * 2
def baseEnd_3928210 : Nat := 2017059841798181094009497

theorem tailTrace_3928210 : CollatzResearch.WordTrace tailWord_3928210 prefixEnd_3928210 2017059841798181094009497 := by
  unfold tailWord_3928210
  simp only [CollatzResearch.WordTrace]
  refine ⟨35818397274693382425309521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95515726065849019800825389 35818397274693382425309521)
  ·
    refine ⟨26863797956020036818982141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35818397274693382425309521 26863797956020036818982141)
    ·
      refine ⟨10073924233507513807118303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26863797956020036818982141 10073924233507513807118303)
      ·
        refine ⟨15110886350261270710677455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10073924233507513807118303 15110886350261270710677455)
        ·
          refine ⟨22666329525391906066016183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15110886350261270710677455 22666329525391906066016183)
          ·
            refine ⟨33999494288087859099024275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22666329525391906066016183 33999494288087859099024275)
            ·
              refine ⟨50999241432131788648536413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33999494288087859099024275 50999241432131788648536413)
              ·
                refine ⟨19124715537049420743201155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50999241432131788648536413 19124715537049420743201155)
                ·
                  refine ⟨28687073305574131114801733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19124715537049420743201155 28687073305574131114801733)
                  ·
                    refine ⟨5378826244795149584025325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28687073305574131114801733 5378826244795149584025325)
                    ·
                      refine ⟨2017059841798181094009497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5378826244795149584025325 2017059841798181094009497)
                      ·
                        rfl

theorem cell23_3928210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_3928210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928210 prefixEnd_3928210 := by exact prefixLift 3928210
  have htrace : WordTrace (prefixWord ++ tailWord_3928210) baseStart_3928210 baseEnd_3928210 := by
    simpa [prefixWord, tailWord_3928210, baseEnd_3928210] using wordTrace_append hprefix tailTrace_3928210
  have hstable : (prefixWord ++ tailWord_3928210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928210).length < 2 ^ (prefixWord ++ tailWord_3928210).sum := by decide
  have hdescent : baseEnd_3928210 < baseStart_3928210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928243 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 3, 5]
def baseStart_3928243 : Nat := 118140960795 + 3928243 * 2 ^ 59
def prefixEnd_3928243 : Nat := 4983230072969 + 3 ^ 40 * 3928243 * 2
def baseEnd_3928243 : Nat := 672358928886593154965615

theorem tailTrace_3928243 : CollatzResearch.WordTrace tailWord_3928243 prefixEnd_3928243 672358928886593154965615 := by
  unfold tailWord_3928243
  simp only [CollatzResearch.WordTrace]
  refine ⟨143274792707653976337189383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95516528471769317558126255 143274792707653976337189383)
  ·
    refine ⟨214912189061480964505784075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143274792707653976337189383 214912189061480964505784075)
    ·
      refine ⟨322368283592221446758676113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214912189061480964505784075 322368283592221446758676113)
      ·
        refine ⟨241776212694166085069007085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322368283592221446758676113 241776212694166085069007085)
        ·
          refine ⟨90666079760312281900877657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241776212694166085069007085 90666079760312281900877657)
          ·
            refine ⟨67999559820234211425658243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90666079760312281900877657 67999559820234211425658243)
            ·
              refine ⟨101999339730351317138487365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67999559820234211425658243 101999339730351317138487365)
              ·
                refine ⟨19124876199440871963466381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101999339730351317138487365 19124876199440871963466381)
                ·
                  refine ⟨7171828574790326986299893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19124876199440871963466381 7171828574790326986299893)
                  ·
                    refine ⟨672358928886593154965615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7171828574790326986299893 672358928886593154965615)
                    ·
                      rfl

theorem cell23_3928243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 5].length) (baseStart_3928243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928243 prefixEnd_3928243 := by exact prefixLift 3928243
  have htrace : WordTrace (prefixWord ++ tailWord_3928243) baseStart_3928243 baseEnd_3928243 := by
    simpa [prefixWord, tailWord_3928243, baseEnd_3928243] using wordTrace_append hprefix tailTrace_3928243
  have hstable : (prefixWord ++ tailWord_3928243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928243).length < 2 ^ (prefixWord ++ tailWord_3928243).sum := by decide
  have hdescent : baseEnd_3928243 < baseStart_3928243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928247 : List Nat := [1, 1, 3, 1, 4, 4, 2, 1, 6]
def baseStart_3928247 : Nat := 118140960795 + 3928247 * 2 ^ 59
def prefixEnd_3928247 : Nat := 4983230072969 + 3 ^ 40 * 3928247 * 2
def baseEnd_3928247 : Nat := 224119871175821938805203

theorem tailTrace_3928247 : CollatzResearch.WordTrace tailWord_3928247 prefixEnd_3928247 224119871175821938805203 := by
  unfold tailWord_3928247
  simp only [CollatzResearch.WordTrace]
  refine ⟨143274938599639485020334995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95516625733092990013556663 143274938599639485020334995)
  ·
    refine ⟨214912407899459227530502493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143274938599639485020334995 214912407899459227530502493)
    ·
      refine ⟨80592152962297210323938435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214912407899459227530502493 80592152962297210323938435)
      ·
        refine ⟨120888229443445815485907653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80592152962297210323938435 120888229443445815485907653)
        ·
          refine ⟨22666543020646090403607685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120888229443445815485907653 22666543020646090403607685)
          ·
            refine ⟨4249976816371141950676441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22666543020646090403607685 4249976816371141950676441)
            ·
              refine ⟨3187482612278356463007331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4249976816371141950676441 3187482612278356463007331)
              ·
                refine ⟨4781223918417534694510997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3187482612278356463007331 4781223918417534694510997)
                ·
                  refine ⟨224119871175821938805203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4781223918417534694510997 224119871175821938805203)
                  ·
                    rfl

theorem cell23_3928247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 6].length) (baseStart_3928247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928247 prefixEnd_3928247 := by exact prefixLift 3928247
  have htrace : WordTrace (prefixWord ++ tailWord_3928247) baseStart_3928247 baseEnd_3928247 := by
    simpa [prefixWord, tailWord_3928247, baseEnd_3928247] using wordTrace_append hprefix tailTrace_3928247
  have hstable : (prefixWord ++ tailWord_3928247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928247).length < 2 ^ (prefixWord ++ tailWord_3928247).sum := by decide
  have hdescent : baseEnd_3928247 < baseStart_3928247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928250 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2]
def baseStart_3928250 : Nat := 118140960795 + 3928250 * 2 ^ 59
def prefixEnd_3928250 : Nat := 4983230072969 + 3 ^ 40 * 3928250 * 2
def baseEnd_3928250 : Nat := 2017080381024360937509313

theorem tailTrace_3928250 : CollatzResearch.WordTrace tailWord_3928250 prefixEnd_3928250 2017080381024360937509313 := by
  unfold tailWord_3928250
  simp only [CollatzResearch.WordTrace]
  refine ⟨35818762004657154133173551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95516698679085744355129469 35818762004657154133173551)
  ·
    refine ⟨53728143006985731199760327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35818762004657154133173551 53728143006985731199760327)
    ·
      refine ⟨80592214510478596799640491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53728143006985731199760327 80592214510478596799640491)
      ·
        refine ⟨120888321765717895199460737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80592214510478596799640491 120888321765717895199460737)
        ·
          refine ⟨90666241324288421399595553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120888321765717895199460737 90666241324288421399595553)
          ·
            refine ⟨67999680993216316049696665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90666241324288421399595553 67999680993216316049696665)
            ·
              refine ⟨50999760744912237037272499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67999680993216316049696665 50999760744912237037272499)
              ·
                refine ⟨76499641117368355555908749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50999760744912237037272499 76499641117368355555908749)
                ·
                  refine ⟨28687365419013133333465781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76499641117368355555908749 28687365419013133333465781)
                  ·
                    refine ⟨2689440508032481250012417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28687365419013133333465781 2689440508032481250012417)
                    ·
                      refine ⟨2017080381024360937509313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2689440508032481250012417 2017080381024360937509313)
                      ·
                        rfl

theorem cell23_3928250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2].length) (baseStart_3928250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928250 prefixEnd_3928250 := by exact prefixLift 3928250
  have htrace : WordTrace (prefixWord ++ tailWord_3928250) baseStart_3928250 baseEnd_3928250 := by
    simpa [prefixWord, tailWord_3928250, baseEnd_3928250] using wordTrace_append hprefix tailTrace_3928250
  have hstable : (prefixWord ++ tailWord_3928250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928250).length < 2 ^ (prefixWord ++ tailWord_3928250).sum := by decide
  have hdescent : baseEnd_3928250 < baseStart_3928250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928267 : List Nat := [1, 1, 1, 1, 3, 2, 6, 1, 2, 3, 2]
def baseStart_3928267 : Nat := 118140960795 + 3928267 * 2 ^ 59
def prefixEnd_3928267 : Nat := 4983230072969 + 3 ^ 40 * 3928267 * 2
def baseEnd_3928267 : Nat := 2017089110195487370996735

theorem tailTrace_3928267 : CollatzResearch.WordTrace tailWord_3928267 prefixEnd_3928267 2017089110195487370996735 := by
  unfold tailWord_3928267
  simp only [CollatzResearch.WordTrace]
  refine ⟨143275668059567028436063055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95517112039711352290708703 143275668059567028436063055)
  ·
    refine ⟨214913502089350542654094583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143275668059567028436063055 214913502089350542654094583)
    ·
      refine ⟨322370253134025813981141875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214913502089350542654094583 322370253134025813981141875)
      ·
        refine ⟨483555379701038720971712813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322370253134025813981141875 483555379701038720971712813)
        ·
          refine ⟨181333267387889520364392305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 483555379701038720971712813 181333267387889520364392305)
          ·
            refine ⟨135999950540917140273294229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181333267387889520364392305 135999950540917140273294229)
            ·
              refine ⟨6374997681605490950310667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135999950540917140273294229 6374997681605490950310667)
              ·
                refine ⟨9562496522408236425466001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6374997681605490950310667 9562496522408236425466001)
                ·
                  refine ⟨7171872391806177319099501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9562496522408236425466001 7171872391806177319099501)
                  ·
                    refine ⟨2689452146927316494662313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7171872391806177319099501 2689452146927316494662313)
                    ·
                      refine ⟨2017089110195487370996735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2689452146927316494662313 2017089110195487370996735)
                      ·
                        rfl

theorem cell23_3928267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 3, 2].length) (baseStart_3928267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928267 prefixEnd_3928267 := by exact prefixLift 3928267
  have htrace : WordTrace (prefixWord ++ tailWord_3928267) baseStart_3928267 baseEnd_3928267 := by
    simpa [prefixWord, tailWord_3928267, baseEnd_3928267] using wordTrace_append hprefix tailTrace_3928267
  have hstable : (prefixWord ++ tailWord_3928267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928267).length < 2 ^ (prefixWord ++ tailWord_3928267).sum := by decide
  have hdescent : baseEnd_3928267 < baseStart_3928267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928273 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 3, 6]
def baseStart_3928273 : Nat := 118140960795 + 3928273 * 2 ^ 59
def prefixEnd_3928273 : Nat := 4983230072969 + 3 ^ 40 * 3928273 * 2
def baseEnd_3928273 : Nat := 672364063693138115840569

theorem tailTrace_3928273 : CollatzResearch.WordTrace tailWord_3928273 prefixEnd_3928273 672364063693138115840569 := by
  unfold tailWord_3928273
  simp only [CollatzResearch.WordTrace]
  refine ⟨143275886897545291460781473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95517257931696860973854315 143275886897545291460781473)
  ·
    refine ⟨107456915173158968595586105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143275886897545291460781473 107456915173158968595586105)
    ·
      refine ⟨80592686379869226446689579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107456915173158968595586105 80592686379869226446689579)
      ·
        refine ⟨120889029569803839670034369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80592686379869226446689579 120889029569803839670034369)
        ·
          refine ⟨90666772177352879752525777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120889029569803839670034369 90666772177352879752525777)
          ·
            refine ⟨68000079133014659814394333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90666772177352879752525777 68000079133014659814394333)
            ·
              refine ⟨25500029674880497430397875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68000079133014659814394333 25500029674880497430397875)
              ·
                refine ⟨38250044512320746145596813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25500029674880497430397875 38250044512320746145596813)
                ·
                  refine ⟨14343766692120279804598805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38250044512320746145596813 14343766692120279804598805)
                  ·
                    refine ⟨672364063693138115840569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14343766692120279804598805 672364063693138115840569)
                    ·
                      rfl

theorem cell23_3928273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_3928273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928273 prefixEnd_3928273 := by exact prefixLift 3928273
  have htrace : WordTrace (prefixWord ++ tailWord_3928273) baseStart_3928273 baseEnd_3928273 := by
    simpa [prefixWord, tailWord_3928273, baseEnd_3928273] using wordTrace_append hprefix tailTrace_3928273
  have hstable : (prefixWord ++ tailWord_3928273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928273).length < 2 ^ (prefixWord ++ tailWord_3928273).sum := by decide
  have hdescent : baseEnd_3928273 < baseStart_3928273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928300 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 3]
def baseStart_3928300 : Nat := 118140960795 + 3928300 * 2 ^ 59
def prefixEnd_3928300 : Nat := 4983230072969 + 3 ^ 40 * 3928300 * 2
def baseEnd_3928300 : Nat := 2017106055057085741884083

theorem tailTrace_3928300 : CollatzResearch.WordTrace tailWord_3928300 prefixEnd_3928300 2017106055057085741884083 := by
  unfold tailWord_3928300
  simp only [CollatzResearch.WordTrace]
  refine ⟨71638435834223737536007177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95517914445631650048009569 71638435834223737536007177)
  ·
    refine ⟨53728826875667803152005383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71638435834223737536007177 53728826875667803152005383)
    ·
      refine ⟨80593240313501704728008075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53728826875667803152005383 80593240313501704728008075)
      ·
        refine ⟨120889860470252557092012113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80593240313501704728008075 120889860470252557092012113)
        ·
          refine ⟨90667395352689417819009085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120889860470252557092012113 90667395352689417819009085)
          ·
            refine ⟨34000273257258531682128407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90667395352689417819009085 34000273257258531682128407)
            ·
              refine ⟨51000409885887797523192611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34000273257258531682128407 51000409885887797523192611)
              ·
                refine ⟨76500614828831696284788917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51000409885887797523192611 76500614828831696284788917)
                ·
                  refine ⟨7171932640202971526698961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76500614828831696284788917 7171932640202971526698961)
                  ·
                    refine ⟨5378949480152228645024221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7171932640202971526698961 5378949480152228645024221)
                    ·
                      refine ⟨2017106055057085741884083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5378949480152228645024221 2017106055057085741884083)
                      ·
                        rfl

theorem cell23_3928300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_3928300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928300 prefixEnd_3928300 := by exact prefixLift 3928300
  have htrace : WordTrace (prefixWord ++ tailWord_3928300) baseStart_3928300 baseEnd_3928300 := by
    simpa [prefixWord, tailWord_3928300, baseEnd_3928300] using wordTrace_append hprefix tailTrace_3928300
  have hstable : (prefixWord ++ tailWord_3928300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928300).length < 2 ^ (prefixWord ++ tailWord_3928300).sum := by decide
  have hdescent : baseEnd_3928300 < baseStart_3928300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928310 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_3928310 : Nat := 118140960795 + 3928310 * 2 ^ 59
def prefixEnd_3928310 : Nat := 4983230072969 + 3 ^ 40 * 3928310 * 2
def baseEnd_3928310 : Nat := 2017111189863630702759037

theorem tailTrace_3928310 : CollatzResearch.WordTrace tailWord_3928310 prefixEnd_3928310 2017111189863630702759037 := by
  unfold tailWord_3928310
  simp only [CollatzResearch.WordTrace]
  refine ⟨8954827274900702923742399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95518157598940831186585589 8954827274900702923742399)
  ·
    refine ⟨13432240912351054385613599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8954827274900702923742399 13432240912351054385613599)
    ·
      refine ⟨20148361368526581578420399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13432240912351054385613599 20148361368526581578420399)
      ·
        refine ⟨30222542052789872367630599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20148361368526581578420399 30222542052789872367630599)
        ·
          refine ⟨45333813079184808551445899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30222542052789872367630599 45333813079184808551445899)
          ·
            refine ⟨68000719618777212827168849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45333813079184808551445899 68000719618777212827168849)
            ·
              refine ⟨51000539714082909620376637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68000719618777212827168849 51000539714082909620376637)
              ·
                refine ⟨19125202392781091107641239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51000539714082909620376637 19125202392781091107641239)
                ·
                  refine ⟨28687803589171636661461859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19125202392781091107641239 28687803589171636661461859)
                  ·
                    refine ⟨43031705383757454992192789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28687803589171636661461859 43031705383757454992192789)
                    ·
                      refine ⟨2017111189863630702759037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43031705383757454992192789 2017111189863630702759037)
                      ·
                        rfl

theorem cell23_3928310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_3928310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928310 prefixEnd_3928310 := by exact prefixLift 3928310
  have htrace : WordTrace (prefixWord ++ tailWord_3928310) baseStart_3928310 baseEnd_3928310 := by
    simpa [prefixWord, tailWord_3928310, baseEnd_3928310] using wordTrace_append hprefix tailTrace_3928310
  have hstable : (prefixWord ++ tailWord_3928310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928310).length < 2 ^ (prefixWord ++ tailWord_3928310).sum := by decide
  have hdescent : baseEnd_3928310 < baseStart_3928310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928314 : List Nat := [3, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2]
def baseStart_3928314 : Nat := 118140960795 + 3928314 * 2 ^ 59
def prefixEnd_3928314 : Nat := 4983230072969 + 3 ^ 40 * 3928314 * 2
def baseEnd_3928314 : Nat := 2017113243786248687109019

theorem tailTrace_3928314 : CollatzResearch.WordTrace tailWord_3928314 prefixEnd_3928314 2017113243786248687109019 := by
  unfold tailWord_3928314
  simp only [CollatzResearch.WordTrace]
  refine ⟨35819345572599188865755999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95518254860264503642015997 35819345572599188865755999)
  ·
    refine ⟨53729018358898783298633999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35819345572599188865755999 53729018358898783298633999)
    ·
      refine ⟨80593527538348174947950999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53729018358898783298633999 80593527538348174947950999)
      ·
        refine ⟨120890291307522262421926499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80593527538348174947950999 120890291307522262421926499)
        ·
          refine ⟨181335436961283393632889749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120890291307522262421926499 181335436961283393632889749)
          ·
            refine ⟨8500098607560159076541707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 181335436961283393632889749 8500098607560159076541707)
            ·
              refine ⟨12750147911340238614812561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8500098607560159076541707 12750147911340238614812561)
              ·
                refine ⟨9562610933505178961109421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12750147911340238614812561 9562610933505178961109421)
                ·
                  refine ⟨3585979100064442110416033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9562610933505178961109421 3585979100064442110416033)
                  ·
                    refine ⟨2689484325048331582812025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3585979100064442110416033 2689484325048331582812025)
                    ·
                      refine ⟨2017113243786248687109019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2689484325048331582812025 2017113243786248687109019)
                      ·
                        rfl

theorem cell23_3928314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2].length) (baseStart_3928314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928314 prefixEnd_3928314 := by exact prefixLift 3928314
  have htrace : WordTrace (prefixWord ++ tailWord_3928314) baseStart_3928314 baseEnd_3928314 := by
    simpa [prefixWord, tailWord_3928314, baseEnd_3928314] using wordTrace_append hprefix tailTrace_3928314
  have hstable : (prefixWord ++ tailWord_3928314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928314).length < 2 ^ (prefixWord ++ tailWord_3928314).sum := by decide
  have hdescent : baseEnd_3928314 < baseStart_3928314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928331 : List Nat := [1, 1, 1, 1, 5, 2, 4, 3, 1, 2, 2]
def baseStart_3928331 : Nat := 118140960795 + 3928331 * 2 ^ 59
def prefixEnd_3928331 : Nat := 4983230072969 + 3 ^ 40 * 3928331 * 2
def baseEnd_3928331 : Nat := 2017121972957375120596441

theorem tailTrace_3928331 : CollatzResearch.WordTrace tailWord_3928331 prefixEnd_3928331 2017121972957375120596441 := by
  unfold tailWord_3928331
  simp only [CollatzResearch.WordTrace]
  refine ⟨143278002331335167366392847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95518668220890111577595231 143278002331335167366392847)
  ·
    refine ⟨214917003497002751049589271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143278002331335167366392847 214917003497002751049589271)
    ·
      refine ⟨322375505245504126574383907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214917003497002751049589271 322375505245504126574383907)
      ·
        refine ⟨483563257868256189861575861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322375505245504126574383907 483563257868256189861575861)
        ·
          refine ⟨45334055425149017799522737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 483563257868256189861575861 45334055425149017799522737)
          ·
            refine ⟨34000541568861763349642053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45334055425149017799522737 34000541568861763349642053)
            ·
              refine ⟨6375101544161580628057885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34000541568861763349642053 6375101544161580628057885)
              ·
                refine ⟨2390663079060592735521707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6375101544161580628057885 2390663079060592735521707)
                ·
                  refine ⟨3585994618590889103282561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2390663079060592735521707 3585994618590889103282561)
                  ·
                    refine ⟨2689495963943166827461921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3585994618590889103282561 2689495963943166827461921)
                    ·
                      refine ⟨2017121972957375120596441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2689495963943166827461921 2017121972957375120596441)
                      ·
                        rfl

theorem cell23_3928331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 1, 2, 2].length) (baseStart_3928331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928331 prefixEnd_3928331 := by exact prefixLift 3928331
  have htrace : WordTrace (prefixWord ++ tailWord_3928331) baseStart_3928331 baseEnd_3928331 := by
    simpa [prefixWord, tailWord_3928331, baseEnd_3928331] using wordTrace_append hprefix tailTrace_3928331
  have hstable : (prefixWord ++ tailWord_3928331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928331).length < 2 ^ (prefixWord ++ tailWord_3928331).sum := by decide
  have hdescent : baseEnd_3928331 < baseStart_3928331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928387 : List Nat := [1, 1, 1, 3, 1, 3, 2, 4, 1, 4, 2]
def baseStart_3928387 : Nat := 118140960795 + 3928387 * 2 ^ 59
def prefixEnd_3928387 : Nat := 4983230072969 + 3 ^ 40 * 3928387 * 2
def baseEnd_3928387 : Nat := 2017150727874026901496183

theorem tailTrace_3928387 : CollatzResearch.WordTrace tailWord_3928387 prefixEnd_3928387 2017150727874026901496183 := by
  unfold tailWord_3928387
  simp only [CollatzResearch.WordTrace]
  refine ⟨143280044819132288930431415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95520029879421525953620943 143280044819132288930431415)
  ·
    refine ⟨214920067228698433395647123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143280044819132288930431415 214920067228698433395647123)
    ·
      refine ⟨322380100843047650093470685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214920067228698433395647123 322380100843047650093470685)
      ·
        refine ⟨120892537816142868785051507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322380100843047650093470685 120892537816142868785051507)
        ·
          refine ⟨181338806724214303177577261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120892537816142868785051507 181338806724214303177577261)
          ·
            refine ⟨68002052521580363691591473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181338806724214303177577261 68002052521580363691591473)
            ·
              refine ⟨51001539391185272768693605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68002052521580363691591473 51001539391185272768693605)
              ·
                refine ⟨9562788635847238644130051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51001539391185272768693605 9562788635847238644130051)
                ·
                  refine ⟨14344182953770857966195077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9562788635847238644130051 14344182953770857966195077)
                  ·
                    refine ⟨2689534303832035868661577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14344182953770857966195077 2689534303832035868661577)
                    ·
                      refine ⟨2017150727874026901496183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2689534303832035868661577 2017150727874026901496183)
                      ·
                        rfl

theorem cell23_3928387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 4, 2].length) (baseStart_3928387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928387 prefixEnd_3928387 := by exact prefixLift 3928387
  have htrace : WordTrace (prefixWord ++ tailWord_3928387) baseStart_3928387 baseEnd_3928387 := by
    simpa [prefixWord, tailWord_3928387, baseEnd_3928387] using wordTrace_append hprefix tailTrace_3928387
  have hstable : (prefixWord ++ tailWord_3928387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928387).length < 2 ^ (prefixWord ++ tailWord_3928387).sum := by decide
  have hdescent : baseEnd_3928387 < baseStart_3928387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928421 : List Nat := [1, 3, 1, 3, 1, 4, 1, 3, 2, 2, 2]
def baseStart_3928421 : Nat := 118140960795 + 3928421 * 2 ^ 59
def prefixEnd_3928421 : Nat := 4983230072969 + 3 ^ 40 * 3928421 * 2
def baseEnd_3928421 : Nat := 2017168186216279768471027

theorem tailTrace_3928421 : CollatzResearch.WordTrace tailWord_3928421 prefixEnd_3928421 2017168186216279768471027 := by
  unfold tailWord_3928421
  simp only [CollatzResearch.WordTrace]
  refine ⟨143281284901009112737169117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95520856600672741824779411 143281284901009112737169117)
  ·
    refine ⟨53730481837878417276438419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143281284901009112737169117 53730481837878417276438419)
    ·
      refine ⟨80595722756817625914657629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53730481837878417276438419 80595722756817625914657629)
      ·
        refine ⟨30223396033806609717996611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80595722756817625914657629 30223396033806609717996611)
        ·
          refine ⟨45335094050709914576994917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30223396033806609717996611 45335094050709914576994917)
          ·
            refine ⟨8500330134508108983186547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45335094050709914576994917 8500330134508108983186547)
            ·
              refine ⟨12750495201762163474779821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8500330134508108983186547 12750495201762163474779821)
              ·
                refine ⟨4781435700660811303042433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12750495201762163474779821 4781435700660811303042433)
                ·
                  refine ⟨3586076775495608477281825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4781435700660811303042433 3586076775495608477281825)
                  ·
                    refine ⟨2689557581621706357961369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3586076775495608477281825 2689557581621706357961369)
                    ·
                      refine ⟨2017168186216279768471027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2689557581621706357961369 2017168186216279768471027)
                      ·
                        rfl

theorem cell23_3928421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_3928421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928421 prefixEnd_3928421 := by exact prefixLift 3928421
  have htrace : WordTrace (prefixWord ++ tailWord_3928421) baseStart_3928421 baseEnd_3928421 := by
    simpa [prefixWord, tailWord_3928421, baseEnd_3928421] using wordTrace_append hprefix tailTrace_3928421
  have hstable : (prefixWord ++ tailWord_3928421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928421).length < 2 ^ (prefixWord ++ tailWord_3928421).sum := by decide
  have hdescent : baseEnd_3928421 < baseStart_3928421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928438 : List Nat := [5, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2]
def baseStart_3928438 : Nat := 118140960795 + 3928438 * 2 ^ 59
def prefixEnd_3928438 : Nat := 4983230072969 + 3 ^ 40 * 3928438 * 2
def baseEnd_3928438 : Nat := 2017176915387406201958449

theorem tailTrace_3928438 : CollatzResearch.WordTrace tailWord_3928438 prefixEnd_3928438 2017176915387406201958449 := by
  unfold tailWord_3928438
  simp only [CollatzResearch.WordTrace]
  refine ⟨8955119058871720290033623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95521269961298349760358645 8955119058871720290033623)
  ·
    refine ⟨13432678588307580435050435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8955119058871720290033623 13432678588307580435050435)
    ·
      refine ⟨20149017882461370652575653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13432678588307580435050435 20149017882461370652575653)
      ·
        refine ⟨3777940852961506997357935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20149017882461370652575653 3777940852961506997357935)
        ·
          refine ⟨5666911279442260496036903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3777940852961506997357935 5666911279442260496036903)
          ·
            refine ⟨8500366919163390744055355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5666911279442260496036903 8500366919163390744055355)
            ·
              refine ⟨12750550378745086116083033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8500366919163390744055355 12750550378745086116083033)
              ·
                refine ⟨9562912784058814587062275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12750550378745086116083033 9562912784058814587062275)
                ·
                  refine ⟨14344369176088221880593413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9562912784058814587062275 14344369176088221880593413)
                  ·
                    refine ⟨2689569220516541602611265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14344369176088221880593413 2689569220516541602611265)
                    ·
                      refine ⟨2017176915387406201958449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2689569220516541602611265 2017176915387406201958449)
                      ·
                        rfl

theorem cell23_3928438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_3928438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928438 prefixEnd_3928438 := by exact prefixLift 3928438
  have htrace : WordTrace (prefixWord ++ tailWord_3928438) baseStart_3928438 baseEnd_3928438 := by
    simpa [prefixWord, tailWord_3928438, baseEnd_3928438] using wordTrace_append hprefix tailTrace_3928438
  have hstable : (prefixWord ++ tailWord_3928438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928438).length < 2 ^ (prefixWord ++ tailWord_3928438).sum := by decide
  have hdescent : baseEnd_3928438 < baseStart_3928438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928457 : List Nat := [1, 2, 1, 1, 6, 1, 2, 2, 2, 5]
def baseStart_3928457 : Nat := 118140960795 + 3928457 * 2 ^ 59
def prefixEnd_3928457 : Nat := 4983230072969 + 3 ^ 40 * 3928457 * 2
def baseEnd_3928457 : Nat := 672395557173280542540287

theorem tailTrace_3928457 : CollatzResearch.WordTrace tailWord_3928457 prefixEnd_3928457 672395557173280542540287 := by
  unfold tailWord_3928457
  simp only [CollatzResearch.WordTrace]
  refine ⟨143282597928878690885479625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95521731952585793923653083 143282597928878690885479625)
  ·
    refine ⟨107461948446659018164109719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143282597928878690885479625 107461948446659018164109719)
    ·
      refine ⟨161192922669988527246164579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107461948446659018164109719 161192922669988527246164579)
      ·
        refine ⟨241789384004982790869246869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161192922669988527246164579 241789384004982790869246869)
        ·
          refine ⟨11333877375233568321995947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 241789384004982790869246869 11333877375233568321995947)
          ·
            refine ⟨17000816062850352482993921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11333877375233568321995947 17000816062850352482993921)
            ·
              refine ⟨12750612047137764362245441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17000816062850352482993921 12750612047137764362245441)
              ·
                refine ⟨9562959035353323271684081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12750612047137764362245441 9562959035353323271684081)
                ·
                  refine ⟨7172219276514992453763061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9562959035353323271684081 7172219276514992453763061)
                  ·
                    refine ⟨672395557173280542540287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7172219276514992453763061 672395557173280542540287)
                    ·
                      rfl

theorem cell23_3928457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 5].length) (baseStart_3928457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928457 prefixEnd_3928457 := by exact prefixLift 3928457
  have htrace : WordTrace (prefixWord ++ tailWord_3928457) baseStart_3928457 baseEnd_3928457 := by
    simpa [prefixWord, tailWord_3928457, baseEnd_3928457] using wordTrace_append hprefix tailTrace_3928457
  have hstable : (prefixWord ++ tailWord_3928457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928457).length < 2 ^ (prefixWord ++ tailWord_3928457).sum := by decide
  have hdescent : baseEnd_3928457 < baseStart_3928457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928544 : List Nat := [2, 1, 1, 3, 1, 1, 3, 4, 3, 1, 3]
def baseStart_3928544 : Nat := 118140960795 + 3928544 * 2 ^ 59
def prefixEnd_3928544 : Nat := 4983230072969 + 3 ^ 40 * 3928544 * 2
def baseEnd_3928544 : Nat := 2017231344336782787232961

theorem tailTrace_3928544 : CollatzResearch.WordTrace tailWord_3928544 prefixEnd_3928544 2017231344336782787232961 := by
  unfold tailWord_3928544
  simp only [CollatzResearch.WordTrace]
  refine ⟨71642885539781752371948343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95523847386375669829264457 71642885539781752371948343)
  ·
    refine ⟨107464328309672628557922515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71642885539781752371948343 107464328309672628557922515)
    ·
      refine ⟨161196492464508942836883773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107464328309672628557922515 161196492464508942836883773)
      ·
        refine ⟨60448684674190853563831415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161196492464508942836883773 60448684674190853563831415)
        ·
          refine ⟨90673027011286280345747123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60448684674190853563831415 90673027011286280345747123)
          ·
            refine ⟨136009540516929420518620685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90673027011286280345747123 136009540516929420518620685)
            ·
              refine ⟨51003577693848532694482757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136009540516929420518620685 51003577693848532694482757)
              ·
                refine ⟨9563170817596599880215517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51003577693848532694482757 9563170817596599880215517)
                ·
                  refine ⟨3586189056598724955080819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9563170817596599880215517 3586189056598724955080819)
                  ·
                    refine ⟨5379283584898087432621229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3586189056598724955080819 5379283584898087432621229)
                    ·
                      refine ⟨2017231344336782787232961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5379283584898087432621229 2017231344336782787232961)
                      ·
                        rfl

theorem cell23_3928544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_3928544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928544 prefixEnd_3928544 := by exact prefixLift 3928544
  have htrace : WordTrace (prefixWord ++ tailWord_3928544) baseStart_3928544 baseEnd_3928544 := by
    simpa [prefixWord, tailWord_3928544, baseEnd_3928544] using wordTrace_append hprefix tailTrace_3928544
  have hstable : (prefixWord ++ tailWord_3928544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928544).length < 2 ^ (prefixWord ++ tailWord_3928544).sum := by decide
  have hdescent : baseEnd_3928544 < baseStart_3928544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928597 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_3928597 : Nat := 118140960795 + 3928597 * 2 ^ 59
def prefixEnd_3928597 : Nat := 4983230072969 + 3 ^ 40 * 3928597 * 2
def baseEnd_3928597 : Nat := 2017258558811471079870217

theorem tailTrace_3928597 : CollatzResearch.WordTrace tailWord_3928597 prefixEnd_3928597 2017258558811471079870217 := by
  unfold tailWord_3928597
  simp only [CollatzResearch.WordTrace]
  refine ⟨143287704148371494795576045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95525136098914329863717363 143287704148371494795576045)
  ·
    refine ⟨53732889055639310548341017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143287704148371494795576045 53732889055639310548341017)
    ·
      refine ⟨40299666791729482911255763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53732889055639310548341017 40299666791729482911255763)
      ·
        refine ⟨60449500187594224366883645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40299666791729482911255763 60449500187594224366883645)
        ·
          refine ⟨22668562570347834137581367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60449500187594224366883645 22668562570347834137581367)
          ·
            refine ⟨34002843855521751206372051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22668562570347834137581367 34002843855521751206372051)
            ·
              refine ⟨51004265783282626809558077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34002843855521751206372051 51004265783282626809558077)
              ·
                refine ⟨19126599668730985053584279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51004265783282626809558077 19126599668730985053584279)
                ·
                  refine ⟨28689899503096477580376419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19126599668730985053584279 28689899503096477580376419)
                  ·
                    refine ⟨43034849254644716370564629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28689899503096477580376419 43034849254644716370564629)
                    ·
                      refine ⟨2017258558811471079870217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43034849254644716370564629 2017258558811471079870217)
                      ·
                        rfl

theorem cell23_3928597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_3928597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928597 prefixEnd_3928597 := by exact prefixLift 3928597
  have htrace : WordTrace (prefixWord ++ tailWord_3928597) baseStart_3928597 baseEnd_3928597 := by
    simpa [prefixWord, tailWord_3928597, baseEnd_3928597] using wordTrace_append hprefix tailTrace_3928597
  have hstable : (prefixWord ++ tailWord_3928597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928597).length < 2 ^ (prefixWord ++ tailWord_3928597).sum := by decide
  have hdescent : baseEnd_3928597 < baseStart_3928597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928615 : List Nat := [1, 1, 7, 2, 1, 1, 3, 1, 1, 5]
def baseStart_3928615 : Nat := 118140960795 + 3928615 * 2 ^ 59
def prefixEnd_3928615 : Nat := 4983230072969 + 3 ^ 40 * 3928615 * 2
def baseEnd_3928615 : Nat := 672422600487750669815045

theorem tailTrace_3928615 : CollatzResearch.WordTrace tailWord_3928615 prefixEnd_3928615 672422600487750669815045 := by
  unfold tailWord_3928615
  simp only [CollatzResearch.WordTrace]
  refine ⟨143288360662306283869731299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95525573774870855913154199 143288360662306283869731299)
  ·
    refine ⟨214932540993459425804596949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143288360662306283869731299 214932540993459425804596949)
    ·
      refine ⟨5037481429534205292295241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 214932540993459425804596949 5037481429534205292295241)
      ·
        refine ⟨3778111072150653969221431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5037481429534205292295241 3778111072150653969221431)
        ·
          refine ⟨5667166608225980953832147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3778111072150653969221431 5667166608225980953832147)
          ·
            refine ⟨8500749912338971430748221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5667166608225980953832147 8500749912338971430748221)
            ·
              refine ⟨3187781217127114286530583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8500749912338971430748221 3187781217127114286530583)
              ·
                refine ⟨4781671825690671429795875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3187781217127114286530583 4781671825690671429795875)
                ·
                  refine ⟨7172507738536007144693813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4781671825690671429795875 7172507738536007144693813)
                  ·
                    refine ⟨672422600487750669815045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7172507738536007144693813 672422600487750669815045)
                    ·
                      rfl

theorem cell23_3928615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_3928615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928615 prefixEnd_3928615 := by exact prefixLift 3928615
  have htrace : WordTrace (prefixWord ++ tailWord_3928615) baseStart_3928615 baseEnd_3928615 := by
    simpa [prefixWord, tailWord_3928615, baseEnd_3928615] using wordTrace_append hprefix tailTrace_3928615
  have hstable : (prefixWord ++ tailWord_3928615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928615).length < 2 ^ (prefixWord ++ tailWord_3928615).sum := by decide
  have hdescent : baseEnd_3928615 < baseStart_3928615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928618 : List Nat := [3, 1, 4, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_3928618 : Nat := 118140960795 + 3928618 * 2 ^ 59
def prefixEnd_3928618 : Nat := 4983230072969 + 3 ^ 40 * 3928618 * 2
def baseEnd_3928618 : Nat := 2017269341905215497707621

theorem tailTrace_3928618 : CollatzResearch.WordTrace tailWord_3928618 prefixEnd_3928618 2017269341905215497707621 := by
  unfold tailWord_3928618
  simp only [CollatzResearch.WordTrace]
  refine ⟨35822117520323853845522627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95525646720863610254727005 35822117520323853845522627)
  ·
    refine ⟨53733176280485780768283941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35822117520323853845522627 53733176280485780768283941)
    ·
      refine ⟨10074970552591083894053239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53733176280485780768283941 10074970552591083894053239)
      ·
        refine ⟨15112455828886625841079859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10074970552591083894053239 15112455828886625841079859)
        ·
          refine ⟨22668683743329938761619789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15112455828886625841079859 22668683743329938761619789)
          ·
            refine ⟨8500756403748727035607421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22668683743329938761619789 8500756403748727035607421)
            ·
              refine ⟨3187783651405772638352783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8500756403748727035607421 3187783651405772638352783)
              ·
                refine ⟨4781675477108658957529175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3187783651405772638352783 4781675477108658957529175)
                ·
                  refine ⟨7172513215662988436293763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4781675477108658957529175 7172513215662988436293763)
                  ·
                    refine ⟨10758769823494482654440645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7172513215662988436293763 10758769823494482654440645)
                    ·
                      refine ⟨2017269341905215497707621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10758769823494482654440645 2017269341905215497707621)
                      ·
                        rfl

theorem cell23_3928618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_3928618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928618 prefixEnd_3928618 := by exact prefixLift 3928618
  have htrace : WordTrace (prefixWord ++ tailWord_3928618) baseStart_3928618 baseEnd_3928618 := by
    simpa [prefixWord, tailWord_3928618, baseEnd_3928618] using wordTrace_append hprefix tailTrace_3928618
  have hstable : (prefixWord ++ tailWord_3928618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928618).length < 2 ^ (prefixWord ++ tailWord_3928618).sum := by decide
  have hdescent : baseEnd_3928618 < baseStart_3928618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928651 : List Nat := [1, 1, 1, 1, 3, 1, 6, 3, 2, 1, 3]
def baseStart_3928651 : Nat := 118140960795 + 3928651 * 2 ^ 59
def prefixEnd_3928651 : Nat := 4983230072969 + 3 ^ 40 * 3928651 * 2
def baseEnd_3928651 : Nat := 2017286286766813868594969

theorem tailTrace_3928651 : CollatzResearch.WordTrace tailWord_3928651 prefixEnd_3928651 2017286286766813868594969 := by
  unfold tailWord_3928651
  simp only [CollatzResearch.WordTrace]
  refine ⟨143289673690175862018041807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95526449126783908012027871 143289673690175862018041807)
  ·
    refine ⟨214934510535263793027062711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143289673690175862018041807 214934510535263793027062711)
    ·
      refine ⟨322401765802895689540594067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214934510535263793027062711 322401765802895689540594067)
      ·
        refine ⟨483602648704343534310891101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322401765802895689540594067 483602648704343534310891101)
        ·
          refine ⟨181350993264128825366584163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 483602648704343534310891101 181350993264128825366584163)
          ·
            refine ⟨272026489896193238049876245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181350993264128825366584163 272026489896193238049876245)
            ·
              refine ⟨12751241713884058033587949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 272026489896193238049876245 12751241713884058033587949)
              ·
                refine ⟨4781715642706521762595481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12751241713884058033587949 4781715642706521762595481)
                ·
                  refine ⟨3586286732029891321946611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4781715642706521762595481 3586286732029891321946611)
                  ·
                    refine ⟨5379430098044836982919917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3586286732029891321946611 5379430098044836982919917)
                    ·
                      refine ⟨2017286286766813868594969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5379430098044836982919917 2017286286766813868594969)
                      ·
                        rfl

theorem cell23_3928651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 1, 3].length) (baseStart_3928651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928651 prefixEnd_3928651 := by exact prefixLift 3928651
  have htrace : WordTrace (prefixWord ++ tailWord_3928651) baseStart_3928651 baseEnd_3928651 := by
    simpa [prefixWord, tailWord_3928651, baseEnd_3928651] using wordTrace_append hprefix tailTrace_3928651
  have hstable : (prefixWord ++ tailWord_3928651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928651).length < 2 ^ (prefixWord ++ tailWord_3928651).sum := by decide
  have hdescent : baseEnd_3928651 < baseStart_3928651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928661 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 3, 3, 2]
def baseStart_3928661 : Nat := 118140960795 + 3928661 * 2 ^ 59
def prefixEnd_3928661 : Nat := 4983230072969 + 3 ^ 40 * 3928661 * 2
def baseEnd_3928661 : Nat := 2017291421573358829469923

theorem tailTrace_3928661 : CollatzResearch.WordTrace tailWord_3928661 prefixEnd_3928661 2017291421573358829469923 := by
  unfold tailWord_3928661
  simp only [CollatzResearch.WordTrace]
  refine ⟨143290038420139633725905837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95526692280093089150603891 143290038420139633725905837)
  ·
    refine ⟨53733764407552362647214689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143290038420139633725905837 53733764407552362647214689)
    ·
      refine ⟨40300323305664271985411017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53733764407552362647214689 40300323305664271985411017)
      ·
        refine ⟨30225242479248203989058263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40300323305664271985411017 30225242479248203989058263)
        ·
          refine ⟨45337863718872305983587395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30225242479248203989058263 45337863718872305983587395)
          ·
            refine ⟨68006795578308458975381093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45337863718872305983587395 68006795578308458975381093)
            ·
              refine ⟨12751274170932836057883955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68006795578308458975381093 12751274170932836057883955)
              ·
                refine ⟨19126911256399254086825933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12751274170932836057883955 19126911256399254086825933)
                ·
                  refine ⟨7172591721149720282559725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19126911256399254086825933 7172591721149720282559725)
                  ·
                    refine ⟨2689721895431145105959897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7172591721149720282559725 2689721895431145105959897)
                    ·
                      refine ⟨2017291421573358829469923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2689721895431145105959897 2017291421573358829469923)
                      ·
                        rfl

theorem cell23_3928661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_3928661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928661 prefixEnd_3928661 := by exact prefixLift 3928661
  have htrace : WordTrace (prefixWord ++ tailWord_3928661) baseStart_3928661 baseEnd_3928661 := by
    simpa [prefixWord, tailWord_3928661, baseEnd_3928661] using wordTrace_append hprefix tailTrace_3928661
  have hstable : (prefixWord ++ tailWord_3928661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928661).length < 2 ^ (prefixWord ++ tailWord_3928661).sum := by decide
  have hdescent : baseEnd_3928661 < baseStart_3928661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928685 : List Nat := [1, 5, 1, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_3928685 : Nat := 118140960795 + 3928685 * 2 ^ 59
def prefixEnd_3928685 : Nat := 4983230072969 + 3 ^ 40 * 3928685 * 2
def baseEnd_3928685 : Nat := 2017303745109066735569813

theorem tailTrace_3928685 : CollatzResearch.WordTrace tailWord_3928685 prefixEnd_3928685 2017303745109066735569813 := by
  unfold tailWord_3928685
  simp only [CollatzResearch.WordTrace]
  refine ⟨143290913772052685824779509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95527275848035123883186339 143290913772052685824779509)
  ·
    refine ⟨13433523166129939296073079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143290913772052685824779509 13433523166129939296073079)
    ·
      refine ⟨20150284749194908944109619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13433523166129939296073079 20150284749194908944109619)
      ·
        refine ⟨30225427123792363416164429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20150284749194908944109619 30225427123792363416164429)
        ·
          refine ⟨11334535171422136281061661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30225427123792363416164429 11334535171422136281061661)
          ·
            refine ⟨4250450689283301105398123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11334535171422136281061661 4250450689283301105398123)
            ·
              refine ⟨6375676033924951658097185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4250450689283301105398123 6375676033924951658097185)
              ·
                refine ⟨4781757025443713743572889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6375676033924951658097185 4781757025443713743572889)
                ·
                  refine ⟨3586317769082785307679667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4781757025443713743572889 3586317769082785307679667)
                  ·
                    refine ⟨5379476653624177961519501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3586317769082785307679667 5379476653624177961519501)
                    ·
                      refine ⟨2017303745109066735569813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5379476653624177961519501 2017303745109066735569813)
                      ·
                        rfl

theorem cell23_3928685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_3928685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928685 prefixEnd_3928685 := by exact prefixLift 3928685
  have htrace : WordTrace (prefixWord ++ tailWord_3928685) baseStart_3928685 baseEnd_3928685 := by
    simpa [prefixWord, tailWord_3928685, baseEnd_3928685] using wordTrace_append hprefix tailTrace_3928685
  have hstable : (prefixWord ++ tailWord_3928685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928685).length < 2 ^ (prefixWord ++ tailWord_3928685).sum := by decide
  have hdescent : baseEnd_3928685 < baseStart_3928685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928704 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 4]
def baseStart_3928704 : Nat := 118140960795 + 3928704 * 2 ^ 59
def prefixEnd_3928704 : Nat := 4983230072969 + 3 ^ 40 * 3928704 * 2
def baseEnd_3928704 : Nat := 2017313501241502161232225

theorem tailTrace_3928704 : CollatzResearch.WordTrace tailWord_3928704 prefixEnd_3928704 2017313501241502161232225 := by
  unfold tailWord_3928704
  simp only [CollatzResearch.WordTrace]
  refine ⟨71645803379491926034860583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95527737839322568046480777 71645803379491926034860583)
  ·
    refine ⟨107468705069237889052290875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71645803379491926034860583 107468705069237889052290875)
    ·
      refine ⟨161203057603856833578436313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107468705069237889052290875 161203057603856833578436313)
      ·
        refine ⟨120902293202892625183827235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161203057603856833578436313 120902293202892625183827235)
        ·
          refine ⟨181353439804338937775740853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120902293202892625183827235 181353439804338937775740853)
          ·
            refine ⟨17001884981656775416475705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181353439804338937775740853 17001884981656775416475705)
            ·
              refine ⟨12751413736242581562356779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17001884981656775416475705 12751413736242581562356779)
              ·
                refine ⟨19127120604363872343535169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12751413736242581562356779 19127120604363872343535169)
                ·
                  refine ⟨14345340453272904257651377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19127120604363872343535169 14345340453272904257651377)
                  ·
                    refine ⟨10759005339954678193238533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14345340453272904257651377 10759005339954678193238533)
                    ·
                      refine ⟨2017313501241502161232225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10759005339954678193238533 2017313501241502161232225)
                      ·
                        rfl

theorem cell23_3928704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_3928704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928704 prefixEnd_3928704 := by exact prefixLift 3928704
  have htrace : WordTrace (prefixWord ++ tailWord_3928704) baseStart_3928704 baseEnd_3928704 := by
    simpa [prefixWord, tailWord_3928704, baseEnd_3928704] using wordTrace_append hprefix tailTrace_3928704
  have hstable : (prefixWord ++ tailWord_3928704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928704).length < 2 ^ (prefixWord ++ tailWord_3928704).sum := by decide
  have hdescent : baseEnd_3928704 < baseStart_3928704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928708 : List Nat := [2, 3, 2, 1, 3, 1, 3, 1, 1, 4, 2]
def baseStart_3928708 : Nat := 118140960795 + 3928708 * 2 ^ 59
def prefixEnd_3928708 : Nat := 4983230072969 + 3 ^ 40 * 3928708 * 2
def baseEnd_3928708 : Nat := 2017315555164120145582207

theorem tailTrace_3928708 : CollatzResearch.WordTrace tailWord_3928708 prefixEnd_3928708 2017315555164120145582207 := by
  unfold tailWord_3928708
  simp only [CollatzResearch.WordTrace]
  refine ⟨71645876325484680376433389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95527835100646240501911185 71645876325484680376433389)
  ·
    refine ⟨26867203622056755141162521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71645876325484680376433389 26867203622056755141162521)
    ·
      refine ⟨20150402716542566355871891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26867203622056755141162521 20150402716542566355871891)
      ·
        refine ⟨30225604074813849533807837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20150402716542566355871891 30225604074813849533807837)
        ·
          refine ⟨11334601528055193575177939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30225604074813849533807837 11334601528055193575177939)
          ·
            refine ⟨17001902292082790362766909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11334601528055193575177939 17001902292082790362766909)
            ·
              refine ⟨6375713359531046386037591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17001902292082790362766909 6375713359531046386037591)
              ·
                refine ⟨9563570039296569579056387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6375713359531046386037591 9563570039296569579056387)
                ·
                  refine ⟨14345355058944854368584581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9563570039296569579056387 14345355058944854368584581)
                  ·
                    refine ⟨2689754073552160194109609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14345355058944854368584581 2689754073552160194109609)
                    ·
                      refine ⟨2017315555164120145582207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2689754073552160194109609 2017315555164120145582207)
                      ·
                        rfl

theorem cell23_3928708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_3928708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928708 prefixEnd_3928708 := by exact prefixLift 3928708
  have htrace : WordTrace (prefixWord ++ tailWord_3928708) baseStart_3928708 baseEnd_3928708 := by
    simpa [prefixWord, tailWord_3928708, baseEnd_3928708] using wordTrace_append hprefix tailTrace_3928708
  have hstable : (prefixWord ++ tailWord_3928708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928708).length < 2 ^ (prefixWord ++ tailWord_3928708).sum := by decide
  have hdescent : baseEnd_3928708 < baseStart_3928708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928759 : List Nat := [1, 1, 3, 1, 7, 1, 2, 1, 2, 2, 2]
def baseStart_3928759 : Nat := 118140960795 + 3928759 * 2 ^ 59
def prefixEnd_3928759 : Nat := 4983230072969 + 3 ^ 40 * 3928759 * 2
def baseEnd_3928759 : Nat := 2017341742677499446044473

theorem tailTrace_3928759 : CollatzResearch.WordTrace tailWord_3928759 prefixEnd_3928759 2017341742677499446044473 := by
  unfold tailWord_3928759
  simp only [CollatzResearch.WordTrace]
  refine ⟨143293612773784596462973331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95529075182523064308648887 143293612773784596462973331)
  ·
    refine ⟨214940419160676894694459997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143293612773784596462973331 214940419160676894694459997)
    ·
      refine ⟨80602657185253835510422499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214940419160676894694459997 80602657185253835510422499)
      ·
        refine ⟨120903985777880753265633749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80602657185253835510422499 120903985777880753265633749)
        ·
          refine ⟨2833687166669080154663291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 120903985777880753265633749 2833687166669080154663291)
          ·
            refine ⟨4250530750003620231994937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2833687166669080154663291 4250530750003620231994937)
            ·
              refine ⟨3187898062502715173996203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4250530750003620231994937 3187898062502715173996203)
              ·
                refine ⟨4781847093754072760994305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3187898062502715173996203 4781847093754072760994305)
                ·
                  refine ⟨3586385320315554570745729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4781847093754072760994305 3586385320315554570745729)
                  ·
                    refine ⟨2689788990236665928059297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3586385320315554570745729 2689788990236665928059297)
                    ·
                      refine ⟨2017341742677499446044473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2689788990236665928059297 2017341742677499446044473)
                      ·
                        rfl

theorem cell23_3928759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 2, 2, 2].length) (baseStart_3928759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928759 prefixEnd_3928759 := by exact prefixLift 3928759
  have htrace : WordTrace (prefixWord ++ tailWord_3928759) baseStart_3928759 baseEnd_3928759 := by
    simpa [prefixWord, tailWord_3928759, baseEnd_3928759] using wordTrace_append hprefix tailTrace_3928759
  have hstable : (prefixWord ++ tailWord_3928759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928759).length < 2 ^ (prefixWord ++ tailWord_3928759).sum := by decide
  have hdescent : baseEnd_3928759 < baseStart_3928759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928784 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 3]
def baseStart_3928784 : Nat := 118140960795 + 3928784 * 2 ^ 59
def prefixEnd_3928784 : Nat := 4983230072969 + 3 ^ 40 * 3928784 * 2
def baseEnd_3928784 : Nat := 2017354579693861848231857

theorem tailTrace_3928784 : CollatzResearch.WordTrace tailWord_3928784 prefixEnd_3928784 2017354579693861848231857 := by
  unfold tailWord_3928784
  simp only [CollatzResearch.WordTrace]
  refine ⟨71647262299347012866316703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95529683065796017155088937 71647262299347012866316703)
  ·
    refine ⟨107470893449020519299475055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71647262299347012866316703 107470893449020519299475055)
    ·
      refine ⟨161206340173530778949212583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107470893449020519299475055 161206340173530778949212583)
      ·
        refine ⟨241809510260296168423818875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161206340173530778949212583 241809510260296168423818875)
        ·
          refine ⟨362714265390444252635728313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241809510260296168423818875 362714265390444252635728313)
          ·
            refine ⟨272035699042833189476796235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362714265390444252635728313 272035699042833189476796235)
            ·
              refine ⟨408053548564249784215194353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272035699042833189476796235 408053548564249784215194353)
              ·
                refine ⟨306040161423187338161395765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408053548564249784215194353 306040161423187338161395765)
                ·
                  refine ⟨28691265133423812952630853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 306040161423187338161395765 28691265133423812952630853)
                  ·
                    refine ⟨5379612212516964928618285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28691265133423812952630853 5379612212516964928618285)
                    ·
                      refine ⟨2017354579693861848231857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5379612212516964928618285 2017354579693861848231857)
                      ·
                        rfl

theorem cell23_3928784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 3].length) (baseStart_3928784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928784 prefixEnd_3928784 := by exact prefixLift 3928784
  have htrace : WordTrace (prefixWord ++ tailWord_3928784) baseStart_3928784 baseEnd_3928784 := by
    simpa [prefixWord, tailWord_3928784, baseEnd_3928784] using wordTrace_append hprefix tailTrace_3928784
  have hstable : (prefixWord ++ tailWord_3928784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928784).length < 2 ^ (prefixWord ++ tailWord_3928784).sum := by decide
  have hdescent : baseEnd_3928784 < baseStart_3928784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928794 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6]
def baseStart_3928794 : Nat := 118140960795 + 3928794 * 2 ^ 59
def prefixEnd_3928794 : Nat := 4983230072969 + 3 ^ 40 * 3928794 * 2
def baseEnd_3928794 : Nat := 2017359714500406809106811

theorem tailTrace_3928794 : CollatzResearch.WordTrace tailWord_3928794 prefixEnd_3928794 2017359714500406809106811 := by
  unfold tailWord_3928794
  simp only [CollatzResearch.WordTrace]
  refine ⟨35823722332164449360124359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95529926219105198293664957 35823722332164449360124359)
  ·
    refine ⟨53735583498246674040186539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35823722332164449360124359 53735583498246674040186539)
    ·
      refine ⟨80603375247370011060279809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53735583498246674040186539 80603375247370011060279809)
      ·
        refine ⟨60452531435527508295209857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80603375247370011060279809 60452531435527508295209857)
        ·
          refine ⟨45339398576645631221407393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60452531435527508295209857 45339398576645631221407393)
          ·
            refine ⟨34004548932484223416055545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45339398576645631221407393 34004548932484223416055545)
            ·
              refine ⟨25503411699363167562041659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34004548932484223416055545 25503411699363167562041659)
              ·
                refine ⟨38255117549044751343062489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25503411699363167562041659 38255117549044751343062489)
                ·
                  refine ⟨28691338161783563507296867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38255117549044751343062489 28691338161783563507296867)
                  ·
                    refine ⟨43037007242675345260945301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28691338161783563507296867 43037007242675345260945301)
                    ·
                      refine ⟨2017359714500406809106811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43037007242675345260945301 2017359714500406809106811)
                      ·
                        rfl

theorem cell23_3928794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_3928794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928794 prefixEnd_3928794 := by exact prefixLift 3928794
  have htrace : WordTrace (prefixWord ++ tailWord_3928794) baseStart_3928794 baseEnd_3928794 := by
    simpa [prefixWord, tailWord_3928794, baseEnd_3928794] using wordTrace_append hprefix tailTrace_3928794
  have hstable : (prefixWord ++ tailWord_3928794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928794).length < 2 ^ (prefixWord ++ tailWord_3928794).sum := by decide
  have hdescent : baseEnd_3928794 < baseStart_3928794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928844 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 2, 4, 5]
def baseStart_3928844 : Nat := 118140960795 + 3928844 * 2 ^ 59
def prefixEnd_3928844 : Nat := 4983230072969 + 3 ^ 40 * 3928844 * 2
def baseEnd_3928844 : Nat := 2017385388533131613481581

theorem tailTrace_3928844 : CollatzResearch.WordTrace tailWord_3928844 prefixEnd_3928844 2017385388533131613481581 := by
  unfold tailWord_3928844
  simp only [CollatzResearch.WordTrace]
  refine ⟨71648356489238327989908793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95531141985651103986545057 71648356489238327989908793)
  ·
    refine ⟨53736267366928745992431595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71648356489238327989908793 53736267366928745992431595)
    ·
      refine ⟨80604401050393118988647393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53736267366928745992431595 80604401050393118988647393)
      ·
        refine ⟨60453300787794839241485545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80604401050393118988647393 60453300787794839241485545)
        ·
          refine ⟨45339975590846129431114159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60453300787794839241485545 45339975590846129431114159)
          ·
            refine ⟨68009963386269194146671239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45339975590846129431114159 68009963386269194146671239)
            ·
              refine ⟨102014945079403791220006859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68009963386269194146671239 102014945079403791220006859)
              ·
                refine ⟨153022417619105686830010289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102014945079403791220006859 153022417619105686830010289)
                ·
                  refine ⟨114766813214329265122507717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153022417619105686830010289 114766813214329265122507717)
                  ·
                    refine ⟨21518777477686737210470197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114766813214329265122507717 21518777477686737210470197)
                    ·
                      refine ⟨2017385388533131613481581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21518777477686737210470197 2017385388533131613481581)
                      ·
                        rfl

theorem cell23_3928844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_3928844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928844 prefixEnd_3928844 := by exact prefixLift 3928844
  have htrace : WordTrace (prefixWord ++ tailWord_3928844) baseStart_3928844 baseEnd_3928844 := by
    simpa [prefixWord, tailWord_3928844, baseEnd_3928844] using wordTrace_append hprefix tailTrace_3928844
  have hstable : (prefixWord ++ tailWord_3928844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928844).length < 2 ^ (prefixWord ++ tailWord_3928844).sum := by decide
  have hdescent : baseEnd_3928844 < baseStart_3928844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928851 : List Nat := [1, 1, 1, 2, 1, 3, 5, 3, 1, 5]
def baseStart_3928851 : Nat := 118140960795 + 3928851 * 2 ^ 59
def prefixEnd_3928851 : Nat := 4983230072969 + 3 ^ 40 * 3928851 * 2
def baseEnd_3928851 : Nat := 672462994299237695364683

theorem tailTrace_3928851 : CollatzResearch.WordTrace tailWord_3928851 prefixEnd_3928851 672462994299237695364683 := by
  unfold tailWord_3928851
  simp only [CollatzResearch.WordTrace]
  refine ⟨143296968289451296175322407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95531312192967530783548271 143296968289451296175322407)
  ·
    refine ⟨214945452434176944262983611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143296968289451296175322407 214945452434176944262983611)
    ·
      refine ⟨322418178651265416394475417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214945452434176944262983611 322418178651265416394475417)
      ·
        refine ⟨241813633988449062295856563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322418178651265416394475417 241813633988449062295856563)
        ·
          refine ⟨362720450982673593443784845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241813633988449062295856563 362720450982673593443784845)
          ·
            refine ⟨136020169118502597541419317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 362720450982673593443784845 136020169118502597541419317)
            ·
              refine ⟨12751890854859618519508061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 136020169118502597541419317 12751890854859618519508061)
              ·
                refine ⟨4781959070572356944815523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12751890854859618519508061 4781959070572356944815523)
                ·
                  refine ⟨7172938605858535417223285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4781959070572356944815523 7172938605858535417223285)
                  ·
                    refine ⟨672462994299237695364683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7172938605858535417223285 672462994299237695364683)
                    ·
                      rfl

theorem cell23_3928851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 5].length) (baseStart_3928851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928851 prefixEnd_3928851 := by exact prefixLift 3928851
  have htrace : WordTrace (prefixWord ++ tailWord_3928851) baseStart_3928851 baseEnd_3928851 := by
    simpa [prefixWord, tailWord_3928851, baseEnd_3928851] using wordTrace_append hprefix tailTrace_3928851
  have hstable : (prefixWord ++ tailWord_3928851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928851).length < 2 ^ (prefixWord ++ tailWord_3928851).sum := by decide
  have hdescent : baseEnd_3928851 < baseStart_3928851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928855 : List Nat := [1, 1, 3, 4, 4, 1, 1, 2, 6]
def baseStart_3928855 : Nat := 118140960795 + 3928855 * 2 ^ 59
def prefixEnd_3928855 : Nat := 4983230072969 + 3 ^ 40 * 3928855 * 2
def baseEnd_3928855 : Nat := 224154559646703452271559

theorem tailTrace_3928855 : CollatzResearch.WordTrace tailWord_3928855 prefixEnd_3928855 224154559646703452271559 := by
  unfold tailWord_3928855
  simp only [CollatzResearch.WordTrace]
  refine ⟨143297114181436804858468019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95531409454291203238978679 143297114181436804858468019)
  ·
    refine ⟨214945671272155207287702029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143297114181436804858468019 214945671272155207287702029)
    ·
      refine ⟨80604626727058202732888261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214945671272155207287702029 80604626727058202732888261)
      ·
        refine ⟨15113367511323413012416549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80604626727058202732888261 15113367511323413012416549)
        ·
          refine ⟨2833756408373139939828103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15113367511323413012416549 2833756408373139939828103)
          ·
            refine ⟨4250634612559709909742155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2833756408373139939828103 4250634612559709909742155)
            ·
              refine ⟨6375951918839564864613233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4250634612559709909742155 6375951918839564864613233)
              ·
                refine ⟨4781963939129673648459925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6375951918839564864613233 4781963939129673648459925)
                ·
                  refine ⟨224154559646703452271559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4781963939129673648459925 224154559646703452271559)
                  ·
                    rfl

theorem cell23_3928855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 6].length) (baseStart_3928855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928855 prefixEnd_3928855 := by exact prefixLift 3928855
  have htrace : WordTrace (prefixWord ++ tailWord_3928855) baseStart_3928855 baseEnd_3928855 := by
    simpa [prefixWord, tailWord_3928855, baseEnd_3928855] using wordTrace_append hprefix tailTrace_3928855
  have hstable : (prefixWord ++ tailWord_3928855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928855).length < 2 ^ (prefixWord ++ tailWord_3928855).sum := by decide
  have hdescent : baseEnd_3928855 < baseStart_3928855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928858 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2]
def baseStart_3928858 : Nat := 118140960795 + 3928858 * 2 ^ 59
def prefixEnd_3928858 : Nat := 4983230072969 + 3 ^ 40 * 3928858 * 2
def baseEnd_3928858 : Nat := 2017392577262294558706517

theorem tailTrace_3928858 : CollatzResearch.WordTrace tailWord_3928858 prefixEnd_3928858 2017392577262294558706517 := by
  unfold tailWord_3928858
  simp only [CollatzResearch.WordTrace]
  refine ⟨35824305900106484092706807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95531482400283957580551485 35824305900106484092706807)
  ·
    refine ⟨53736458850159726139060211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35824305900106484092706807 53736458850159726139060211)
    ·
      refine ⟨80604688275239589208590317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53736458850159726139060211 80604688275239589208590317)
      ·
        refine ⟨30226758103214845953221369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80604688275239589208590317 30226758103214845953221369)
        ·
          refine ⟨22670068577411134464916027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30226758103214845953221369 22670068577411134464916027)
          ·
            refine ⟨34005102866116701697374041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22670068577411134464916027 34005102866116701697374041)
            ·
              refine ⟨25503827149587526273030531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34005102866116701697374041 25503827149587526273030531)
              ·
                refine ⟨38255740724381289409545797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25503827149587526273030531 38255740724381289409545797)
                ·
                  refine ⟨7172951385821491764289837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38255740724381289409545797 7172951385821491764289837)
                  ·
                    refine ⟨2689856769683059411608689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7172951385821491764289837 2689856769683059411608689)
                    ·
                      refine ⟨2017392577262294558706517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2689856769683059411608689 2017392577262294558706517)
                      ·
                        rfl

theorem cell23_3928858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_3928858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928858 prefixEnd_3928858 := by exact prefixLift 3928858
  have htrace : WordTrace (prefixWord ++ tailWord_3928858) baseStart_3928858 baseEnd_3928858 := by
    simpa [prefixWord, tailWord_3928858, baseEnd_3928858] using wordTrace_append hprefix tailTrace_3928858
  have hstable : (prefixWord ++ tailWord_3928858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928858).length < 2 ^ (prefixWord ++ tailWord_3928858).sum := by decide
  have hdescent : baseEnd_3928858 < baseStart_3928858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928865 : List Nat := [1, 2, 3, 2, 1, 2, 1, 6, 1, 1, 3]
def baseStart_3928865 : Nat := 118140960795 + 3928865 * 2 ^ 59
def prefixEnd_3928865 : Nat := 4983230072969 + 3 ^ 40 * 3928865 * 2
def baseEnd_3928865 : Nat := 2017396171626876031318985

theorem tailTrace_3928865 : CollatzResearch.WordTrace tailWord_3928865 prefixEnd_3928865 2017396171626876031318985 := by
  unfold tailWord_3928865
  simp only [CollatzResearch.WordTrace]
  refine ⟨143297478911400576566332049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95531652607600384377554699 143297478911400576566332049)
  ·
    refine ⟨107473109183550432424749037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143297478911400576566332049 107473109183550432424749037)
    ·
      refine ⟨40302415943831412159280889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107473109183550432424749037 40302415943831412159280889)
      ·
        refine ⟨30226811957873559119460667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40302415943831412159280889 30226811957873559119460667)
        ·
          refine ⟨45340217936810338679191001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30226811957873559119460667 45340217936810338679191001)
          ·
            refine ⟨34005163452607754009393251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45340217936810338679191001 34005163452607754009393251)
            ·
              refine ⟨51007745178911631014089877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34005163452607754009393251 51007745178911631014089877)
              ·
                refine ⟨2390988055261482703785463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51007745178911631014089877 2390988055261482703785463)
                ·
                  refine ⟨3586482082892224055678195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2390988055261482703785463 3586482082892224055678195)
                  ·
                    refine ⟨5379723124338336083517293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3586482082892224055678195 5379723124338336083517293)
                    ·
                      refine ⟨2017396171626876031318985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5379723124338336083517293 2017396171626876031318985)
                      ·
                        rfl

theorem cell23_3928865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_3928865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928865 prefixEnd_3928865 := by exact prefixLift 3928865
  have htrace : WordTrace (prefixWord ++ tailWord_3928865) baseStart_3928865 baseEnd_3928865 := by
    simpa [prefixWord, tailWord_3928865, baseEnd_3928865] using wordTrace_append hprefix tailTrace_3928865
  have hstable : (prefixWord ++ tailWord_3928865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928865).length < 2 ^ (prefixWord ++ tailWord_3928865).sum := by decide
  have hdescent : baseEnd_3928865 < baseStart_3928865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928888 : List Nat := [2, 1, 2, 1, 3, 2, 4, 2, 1, 1, 4]
def baseStart_3928888 : Nat := 118140960795 + 3928888 * 2 ^ 59
def prefixEnd_3928888 : Nat := 4983230072969 + 3 ^ 40 * 3928888 * 2
def baseEnd_3928888 : Nat := 2017407981681929441331379

theorem tailTrace_3928888 : CollatzResearch.WordTrace tailWord_3928888 prefixEnd_3928888 2017407981681929441331379 := by
  unfold tailWord_3928888
  simp only [CollatzResearch.WordTrace]
  refine ⟨71649158895158625747209659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95532211860211500996279545 71649158895158625747209659)
  ·
    refine ⟨107473738342737938620814489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71649158895158625747209659 107473738342737938620814489)
    ·
      refine ⟨80605303757053453965610867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107473738342737938620814489 80605303757053453965610867)
      ·
        refine ⟨120907955635580180948416301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80605303757053453965610867 120907955635580180948416301)
        ·
          refine ⟨45340483363342567855656113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120907955635580180948416301 45340483363342567855656113)
          ·
            refine ⟨34005362522506925891742085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45340483363342567855656113 34005362522506925891742085)
            ·
              refine ⟨6376005472970048604701641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34005362522506925891742085 6376005472970048604701641)
              ·
                refine ⟨4782004104727536453526231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6376005472970048604701641 4782004104727536453526231)
                ·
                  refine ⟨7173006157091304680289347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4782004104727536453526231 7173006157091304680289347)
                  ·
                    refine ⟨10759509235636957020434021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7173006157091304680289347 10759509235636957020434021)
                    ·
                      refine ⟨2017407981681929441331379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10759509235636957020434021 2017407981681929441331379)
                      ·
                        rfl

theorem cell23_3928888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 1, 1, 4].length) (baseStart_3928888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928888 prefixEnd_3928888 := by exact prefixLift 3928888
  have htrace : WordTrace (prefixWord ++ tailWord_3928888) baseStart_3928888 baseEnd_3928888 := by
    simpa [prefixWord, tailWord_3928888, baseEnd_3928888] using wordTrace_append hprefix tailTrace_3928888
  have hstable : (prefixWord ++ tailWord_3928888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928888).length < 2 ^ (prefixWord ++ tailWord_3928888).sum := by decide
  have hdescent : baseEnd_3928888 < baseStart_3928888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928908 : List Nat := [2, 2, 1, 3, 3, 2, 2, 1, 1, 1, 5]
def baseStart_3928908 : Nat := 118140960795 + 3928908 * 2 ^ 59
def prefixEnd_3928908 : Nat := 4983230072969 + 3 ^ 40 * 3928908 * 2
def baseEnd_3928908 : Nat := 2017418251295019363081287

theorem tailTrace_3928908 : CollatzResearch.WordTrace tailWord_3928908 prefixEnd_3928908 2017418251295019363081287 := by
  unfold tailWord_3928908
  simp only [CollatzResearch.WordTrace]
  refine ⟨71649523625122397455073689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95532698166829863273431585 71649523625122397455073689)
  ·
    refine ⟨53737142718841798091305267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71649523625122397455073689 53737142718841798091305267)
    ·
      refine ⟨80605714078262697136957901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53737142718841798091305267 80605714078262697136957901)
      ·
        refine ⟨30227142779348511426359213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80605714078262697136957901 30227142779348511426359213)
        ·
          refine ⟨11335178542255691784884705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30227142779348511426359213 11335178542255691784884705)
          ·
            refine ⟨8501383906691768838663529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11335178542255691784884705 8501383906691768838663529)
            ·
              refine ⟨6376037930018826628997647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8501383906691768838663529 6376037930018826628997647)
              ·
                refine ⟨9564056895028239943496471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6376037930018826628997647 9564056895028239943496471)
                ·
                  refine ⟨14346085342542359915244707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9564056895028239943496471 14346085342542359915244707)
                  ·
                    refine ⟨21519128013813539872867061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14346085342542359915244707 21519128013813539872867061)
                    ·
                      refine ⟨2017418251295019363081287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21519128013813539872867061 2017418251295019363081287)
                      ·
                        rfl

theorem cell23_3928908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_3928908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928908 prefixEnd_3928908 := by exact prefixLift 3928908
  have htrace : WordTrace (prefixWord ++ tailWord_3928908) baseStart_3928908 baseEnd_3928908 := by
    simpa [prefixWord, tailWord_3928908, baseEnd_3928908] using wordTrace_append hprefix tailTrace_3928908
  have hstable : (prefixWord ++ tailWord_3928908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928908).length < 2 ^ (prefixWord ++ tailWord_3928908).sum := by decide
  have hdescent : baseEnd_3928908 < baseStart_3928908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928922 : List Nat := [3, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2]
def baseStart_3928922 : Nat := 118140960795 + 3928922 * 2 ^ 59
def prefixEnd_3928922 : Nat := 4983230072969 + 3 ^ 40 * 3928922 * 2
def baseEnd_3928922 : Nat := 2017425440024182308306223

theorem tailTrace_3928922 : CollatzResearch.WordTrace tailWord_3928922 prefixEnd_3928922 2017425440024182308306223 := by
  unfold tailWord_3928922
  simp only [CollatzResearch.WordTrace]
  refine ⟨35824889468048518825289255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95533038581462716867438013 35824889468048518825289255)
  ·
    refine ⟨53737334202072778237933883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35824889468048518825289255 53737334202072778237933883)
    ·
      refine ⟨80606001303109167356900825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53737334202072778237933883 80606001303109167356900825)
      ·
        refine ⟨60454500977331875517675619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80606001303109167356900825 60454500977331875517675619)
        ·
          refine ⟨90681751465997813276513429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60454500977331875517675619 90681751465997813276513429)
          ·
            refine ⟨4250707099968647497336567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90681751465997813276513429 4250707099968647497336567)
            ·
              refine ⟨6376060649952971246004851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4250707099968647497336567 6376060649952971246004851)
              ·
                refine ⟨9564090974929456869007277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6376060649952971246004851 9564090974929456869007277)
                ·
                  refine ⟨3586534115598546325877729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9564090974929456869007277 3586534115598546325877729)
                  ·
                    refine ⟨2689900586698909744408297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3586534115598546325877729 2689900586698909744408297)
                    ·
                      refine ⟨2017425440024182308306223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2689900586698909744408297 2017425440024182308306223)
                      ·
                        rfl

theorem cell23_3928922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_3928922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928922 prefixEnd_3928922 := by exact prefixLift 3928922
  have htrace : WordTrace (prefixWord ++ tailWord_3928922) baseStart_3928922 baseEnd_3928922 := by
    simpa [prefixWord, tailWord_3928922, baseEnd_3928922] using wordTrace_append hprefix tailTrace_3928922
  have hstable : (prefixWord ++ tailWord_3928922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928922).length < 2 ^ (prefixWord ++ tailWord_3928922).sum := by decide
  have hdescent : baseEnd_3928922 < baseStart_3928922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3928932 : List Nat := [2, 3, 1, 1, 4, 3, 2, 1, 2, 4]
def baseStart_3928932 : Nat := 118140960795 + 3928932 * 2 ^ 59
def prefixEnd_3928932 : Nat := 4983230072969 + 3 ^ 40 * 3928932 * 2
def baseEnd_3928932 : Nat := 672476858276909089727059

theorem tailTrace_3928932 : CollatzResearch.WordTrace tailWord_3928932 prefixEnd_3928932 672476858276909089727059 := by
  unfold tailWord_3928932
  simp only [CollatzResearch.WordTrace]
  refine ⟨71649961301078923504510525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95533281734771898006014033 71649961301078923504510525)
  ·
    refine ⟨26868735487904596314191447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71649961301078923504510525 26868735487904596314191447)
    ·
      refine ⟨40303103231856894471287171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26868735487904596314191447 40303103231856894471287171)
      ·
        refine ⟨60454654847785341706930757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40303103231856894471287171 60454654847785341706930757)
        ·
          refine ⟨11335247783959751570049517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60454654847785341706930757 11335247783959751570049517)
          ·
            refine ⟨4250717918984906838768569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11335247783959751570049517 4250717918984906838768569)
            ·
              refine ⟨3188038439238680129076427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4250717918984906838768569 3188038439238680129076427)
              ·
                refine ⟨4782057658858020193614641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3188038439238680129076427 4782057658858020193614641)
                ·
                  refine ⟨3586543244143515145210981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4782057658858020193614641 3586543244143515145210981)
                  ·
                    refine ⟨672476858276909089727059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3586543244143515145210981 672476858276909089727059)
                    ·
                      rfl

theorem cell23_3928932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_3928932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3928932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3928932 prefixEnd_3928932 := by exact prefixLift 3928932
  have htrace : WordTrace (prefixWord ++ tailWord_3928932) baseStart_3928932 baseEnd_3928932 := by
    simpa [prefixWord, tailWord_3928932, baseEnd_3928932] using wordTrace_append hprefix tailTrace_3928932
  have hstable : (prefixWord ++ tailWord_3928932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3928932).length < 2 ^ (prefixWord ++ tailWord_3928932).sum := by decide
  have hdescent : baseEnd_3928932 < baseStart_3928932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3928932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929001 : List Nat := [1, 2, 1, 1, 1, 1, 7, 2, 7]
def baseStart_3929001 : Nat := 118140960795 + 3929001 * 2 ^ 59
def prefixEnd_3929001 : Nat := 4983230072969 + 3 ^ 40 * 3929001 * 2
def baseEnd_3929001 : Nat := 224162889443987499913151

theorem tailTrace_3929001 : CollatzResearch.WordTrace tailWord_3929001 prefixEnd_3929001 224162889443987499913151 := by
  unfold tailWord_3929001
  simp only [CollatzResearch.WordTrace]
  refine ⟨143302439238907871793282857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95534959492605247862188571 143302439238907871793282857)
  ·
    refine ⟨107476829429180903844962143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143302439238907871793282857 107476829429180903844962143)
    ·
      refine ⟨161215244143771355767443215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107476829429180903844962143 161215244143771355767443215)
      ·
        refine ⟨241822866215657033651164823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161215244143771355767443215 241822866215657033651164823)
        ·
          refine ⟨362734299323485550476747235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241822866215657033651164823 362734299323485550476747235)
          ·
            refine ⟨544101448985228325715120853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362734299323485550476747235 544101448985228325715120853)
            ·
              refine ⟨12752377710591288883948145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 544101448985228325715120853 12752377710591288883948145)
              ·
                refine ⟨9564283282943466662961109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12752377710591288883948145 9564283282943466662961109)
                ·
                  refine ⟨224162889443987499913151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9564283282943466662961109 224162889443987499913151)
                  ·
                    rfl

theorem cell23_3929001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 7].length) (baseStart_3929001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929001 prefixEnd_3929001 := by exact prefixLift 3929001
  have htrace : WordTrace (prefixWord ++ tailWord_3929001) baseStart_3929001 baseEnd_3929001 := by
    simpa [prefixWord, tailWord_3929001, baseEnd_3929001] using wordTrace_append hprefix tailTrace_3929001
  have hstable : (prefixWord ++ tailWord_3929001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929001).length < 2 ^ (prefixWord ++ tailWord_3929001).sum := by decide
  have hdescent : baseEnd_3929001 < baseStart_3929001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929041 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 1, 1, 7]
def baseStart_3929041 : Nat := 118140960795 + 3929041 * 2 ^ 59
def prefixEnd_3929041 : Nat := 4983230072969 + 3 ^ 40 * 3929041 * 2
def baseEnd_3929041 : Nat := 2017486544222067342718175

theorem tailTrace_3929041 : CollatzResearch.WordTrace tailWord_3929041 prefixEnd_3929041 2017486544222067342718175 := by
  unfold tailWord_3929041
  simp only [CollatzResearch.WordTrace]
  refine ⟨143303898158762958624738977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95535932105841972416492651 143303898158762958624738977)
  ·
    refine ⟨107477923619072218968554233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143303898158762958624738977 107477923619072218968554233)
    ·
      refine ⟨80608442714304164226415675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107477923619072218968554233 80608442714304164226415675)
      ·
        refine ⟨120912664071456246339623513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80608442714304164226415675 120912664071456246339623513)
        ·
          refine ⟨90684498053592184754717635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120912664071456246339623513 90684498053592184754717635)
          ·
            refine ⟨136026747080388277132076453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90684498053592184754717635 136026747080388277132076453)
            ·
              refine ⟨25505015077572801962264335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136026747080388277132076453 25505015077572801962264335)
              ·
                refine ⟨38257522616359202943396503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25505015077572801962264335 38257522616359202943396503)
                ·
                  refine ⟨57386283924538804415094755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38257522616359202943396503 57386283924538804415094755)
                  ·
                    refine ⟨86079425886808206622642133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57386283924538804415094755 86079425886808206622642133)
                    ·
                      refine ⟨2017486544222067342718175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 86079425886808206622642133 2017486544222067342718175)
                      ·
                        rfl

theorem cell23_3929041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_3929041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929041 prefixEnd_3929041 := by exact prefixLift 3929041
  have htrace : WordTrace (prefixWord ++ tailWord_3929041) baseStart_3929041 baseEnd_3929041 := by
    simpa [prefixWord, tailWord_3929041, baseEnd_3929041] using wordTrace_append hprefix tailTrace_3929041
  have hstable : (prefixWord ++ tailWord_3929041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929041).length < 2 ^ (prefixWord ++ tailWord_3929041).sum := by decide
  have hdescent : baseEnd_3929041 < baseStart_3929041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929122 : List Nat := [3, 3, 1, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_3929122 : Nat := 118140960795 + 3929122 * 2 ^ 59
def prefixEnd_3929122 : Nat := 4983230072969 + 3 ^ 40 * 3929122 * 2
def baseEnd_3929122 : Nat := 2017528136155081525805303

theorem tailTrace_3929122 : CollatzResearch.WordTrace tailWord_3929122 prefixEnd_3929122 2017528136155081525805303 := by
  unfold tailWord_3929122
  simp only [CollatzResearch.WordTrace]
  refine ⟨35826713117867377364609405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95537901647646339638958413 35826713117867377364609405)
  ·
    refine ⟨13435017419200266511728527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35826713117867377364609405 13435017419200266511728527)
    ·
      refine ⟨20152526128800399767592791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13435017419200266511728527 20152526128800399767592791)
      ·
        refine ⟨30228789193200599651389187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20152526128800399767592791 30228789193200599651389187)
        ·
          refine ⟨45343183789800899477083781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30228789193200599651389187 45343183789800899477083781)
          ·
            refine ⟨8501846960587668651953209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45343183789800899477083781 8501846960587668651953209)
            ·
              refine ⟨6376385220440751488964907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8501846960587668651953209 6376385220440751488964907)
              ·
                refine ⟨9564577830661127233447361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6376385220440751488964907 9564577830661127233447361)
                ·
                  refine ⟨7173433372995845425085521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9564577830661127233447361 7173433372995845425085521)
                  ·
                    refine ⟨5380075029746884068814141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7173433372995845425085521 5380075029746884068814141)
                    ·
                      refine ⟨2017528136155081525805303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5380075029746884068814141 2017528136155081525805303)
                      ·
                        rfl

theorem cell23_3929122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_3929122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929122 prefixEnd_3929122 := by exact prefixLift 3929122
  have htrace : WordTrace (prefixWord ++ tailWord_3929122) baseStart_3929122 baseEnd_3929122 := by
    simpa [prefixWord, tailWord_3929122, baseEnd_3929122] using wordTrace_append hprefix tailTrace_3929122
  have hstable : (prefixWord ++ tailWord_3929122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929122).length < 2 ^ (prefixWord ++ tailWord_3929122).sum := by decide
  have hdescent : baseEnd_3929122 < baseStart_3929122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929142 : List Nat := [5, 1, 2, 1, 1, 3, 2, 2, 6]
def baseStart_3929142 : Nat := 118140960795 + 3929142 * 2 ^ 59
def prefixEnd_3929142 : Nat := 4983230072969 + 3 ^ 40 * 3929142 * 2
def baseEnd_3929142 : Nat := 224170933974241271950579

theorem tailTrace_3929142 : CollatzResearch.WordTrace tailWord_3929142 prefixEnd_3929142 224170933974241271950579 := by
  unfold tailWord_3929142
  simp only [CollatzResearch.WordTrace]
  refine ⟨8956723870712315804635355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95538387954264701916110453 8956723870712315804635355)
  ·
    refine ⟨13435085806068473706953033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8956723870712315804635355 13435085806068473706953033)
    ·
      refine ⟨10076314354551355280214775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13435085806068473706953033 10076314354551355280214775)
      ·
        refine ⟨15114471531827032920322163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10076314354551355280214775 15114471531827032920322163)
        ·
          refine ⟨22671707297740549380483245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15114471531827032920322163 22671707297740549380483245)
          ·
            refine ⟨8501890236652706017681217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22671707297740549380483245 8501890236652706017681217)
            ·
              refine ⟨6376417677489529513260913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8501890236652706017681217 6376417677489529513260913)
              ·
                refine ⟨4782313258117147134945685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6376417677489529513260913 4782313258117147134945685)
                ·
                  refine ⟨224170933974241271950579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4782313258117147134945685 224170933974241271950579)
                  ·
                    rfl

theorem cell23_3929142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_3929142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929142 prefixEnd_3929142 := by exact prefixLift 3929142
  have htrace : WordTrace (prefixWord ++ tailWord_3929142) baseStart_3929142 baseEnd_3929142 := by
    simpa [prefixWord, tailWord_3929142, baseEnd_3929142] using wordTrace_append hprefix tailTrace_3929142
  have hstable : (prefixWord ++ tailWord_3929142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929142).length < 2 ^ (prefixWord ++ tailWord_3929142).sum := by decide
  have hdescent : baseEnd_3929142 < baseStart_3929142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929175 : List Nat := [1, 1, 3, 2, 2, 1, 1, 6, 1, 1, 4]
def baseStart_3929175 : Nat := 118140960795 + 3929175 * 2 ^ 59
def prefixEnd_3929175 : Nat := 4983230072969 + 3 ^ 40 * 3929175 * 2
def baseEnd_3929175 : Nat := 2017555350629769818442559

theorem tailTrace_3929175 : CollatzResearch.WordTrace tailWord_3929175 prefixEnd_3929175 2017555350629769818442559 := by
  unfold tailWord_3929175
  simp only [CollatzResearch.WordTrace]
  refine ⟨143308785540277499510116979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95539190360184999673411319 143308785540277499510116979)
  ·
    refine ⟨214963178310416249265175469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143308785540277499510116979 214963178310416249265175469)
    ·
      refine ⟨80611191866406093474440801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214963178310416249265175469 80611191866406093474440801)
      ·
        refine ⟨60458393899804570105830601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80611191866406093474440801 60458393899804570105830601)
        ·
          refine ⟨45343795424853427579372951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60458393899804570105830601 45343795424853427579372951)
          ·
            refine ⟨68015693137280141369059427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45343795424853427579372951 68015693137280141369059427)
            ·
              refine ⟨102023539705920212053589141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68015693137280141369059427 102023539705920212053589141)
              ·
                refine ⟨4782353423715009940011991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102023539705920212053589141 4782353423715009940011991)
                ·
                  refine ⟨7173530135572514910017987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4782353423715009940011991 7173530135572514910017987)
                  ·
                    refine ⟨10760295203358772365026981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7173530135572514910017987 10760295203358772365026981)
                    ·
                      refine ⟨2017555350629769818442559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10760295203358772365026981 2017555350629769818442559)
                      ·
                        rfl

theorem cell23_3929175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_3929175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929175 prefixEnd_3929175 := by exact prefixLift 3929175
  have htrace : WordTrace (prefixWord ++ tailWord_3929175) baseStart_3929175 baseEnd_3929175 := by
    simpa [prefixWord, tailWord_3929175, baseEnd_3929175] using wordTrace_append hprefix tailTrace_3929175
  have hstable : (prefixWord ++ tailWord_3929175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929175).length < 2 ^ (prefixWord ++ tailWord_3929175).sum := by decide
  have hdescent : baseEnd_3929175 < baseStart_3929175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929178 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5]
def baseStart_3929178 : Nat := 118140960795 + 3929178 * 2 ^ 59
def prefixEnd_3929178 : Nat := 4983230072969 + 3 ^ 40 * 3929178 * 2
def baseEnd_3929178 : Nat := 2017556891071733306705045

theorem tailTrace_3929178 : CollatzResearch.WordTrace tailWord_3929178 prefixEnd_3929178 2017556891071733306705045 := by
  unfold tailWord_3929178
  simp only [CollatzResearch.WordTrace]
  refine ⟨35827223739816657755619047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95539263306177754014984125 35827223739816657755619047)
  ·
    refine ⟨53740835609724986633428571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35827223739816657755619047 53740835609724986633428571)
    ·
      refine ⟨80611253414587479950142857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53740835609724986633428571 80611253414587479950142857)
      ·
        refine ⟨60458440060940609962607143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80611253414587479950142857 60458440060940609962607143)
        ·
          refine ⟨90687660091410914943910715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60458440060940609962607143 90687660091410914943910715)
          ·
            refine ⟨136031490137116372415866073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90687660091410914943910715 136031490137116372415866073)
            ·
              refine ⟨102023617602837279311899555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136031490137116372415866073 102023617602837279311899555)
              ·
                refine ⟨153035426404255918967849333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102023617602837279311899555 153035426404255918967849333)
                ·
                  refine ⟨14347071225398992403235875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153035426404255918967849333 14347071225398992403235875)
                  ·
                    refine ⟨21520606838098488604853813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14347071225398992403235875 21520606838098488604853813)
                    ·
                      refine ⟨2017556891071733306705045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21520606838098488604853813 2017556891071733306705045)
                      ·
                        rfl

theorem cell23_3929178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_3929178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929178 prefixEnd_3929178 := by exact prefixLift 3929178
  have htrace : WordTrace (prefixWord ++ tailWord_3929178) baseStart_3929178 baseEnd_3929178 := by
    simpa [prefixWord, tailWord_3929178, baseEnd_3929178] using wordTrace_append hprefix tailTrace_3929178
  have hstable : (prefixWord ++ tailWord_3929178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929178).length < 2 ^ (prefixWord ++ tailWord_3929178).sum := by decide
  have hdescent : baseEnd_3929178 < baseStart_3929178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929186 : List Nat := [3, 3, 2, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_3929186 : Nat := 118140960795 + 3929186 * 2 ^ 59
def prefixEnd_3929186 : Nat := 4983230072969 + 3 ^ 40 * 3929186 * 2
def baseEnd_3929186 : Nat := 2017560998916969275405009

theorem tailTrace_3929186 : CollatzResearch.WordTrace tailWord_3929186 prefixEnd_3929186 2017560998916969275405009 := by
  unfold tailWord_3929186
  simp only [CollatzResearch.WordTrace]
  refine ⟨35827296685809412097191853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95539457828825098925844941 35827296685809412097191853)
  ·
    refine ⟨13435236257178529536446945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35827296685809412097191853 13435236257178529536446945)
    ·
      refine ⟨10076427192883897152335209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13435236257178529536446945 10076427192883897152335209)
      ·
        refine ⟨7557320394662922864251407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10076427192883897152335209 7557320394662922864251407)
        ·
          refine ⟨11335980591994384296377111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7557320394662922864251407 11335980591994384296377111)
          ·
            refine ⟨17003970887991576444565667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11335980591994384296377111 17003970887991576444565667)
            ·
              refine ⟨25505956331987364666848501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17003970887991576444565667 25505956331987364666848501)
              ·
                refine ⟨2391183406123815437517047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25505956331987364666848501 2391183406123815437517047)
                ·
                  refine ⟨3586775109185723156275571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2391183406123815437517047 3586775109185723156275571)
                  ·
                    refine ⟨5380162663778584734413357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3586775109185723156275571 5380162663778584734413357)
                    ·
                      refine ⟨2017560998916969275405009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5380162663778584734413357 2017560998916969275405009)
                      ·
                        rfl

theorem cell23_3929186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_3929186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929186 prefixEnd_3929186 := by exact prefixLift 3929186
  have htrace : WordTrace (prefixWord ++ tailWord_3929186) baseStart_3929186 baseEnd_3929186 := by
    simpa [prefixWord, tailWord_3929186, baseEnd_3929186] using wordTrace_append hprefix tailTrace_3929186
  have hstable : (prefixWord ++ tailWord_3929186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929186).length < 2 ^ (prefixWord ++ tailWord_3929186).sum := by decide
  have hdescent : baseEnd_3929186 < baseStart_3929186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929188 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_3929188 : Nat := 118140960795 + 3929188 * 2 ^ 59
def prefixEnd_3929188 : Nat := 4983230072969 + 3 ^ 40 * 3929188 * 2
def baseEnd_3929188 : Nat := 2017562025878278267579999

theorem tailTrace_3929188 : CollatzResearch.WordTrace tailWord_3929188 prefixEnd_3929188 2017562025878278267579999 := by
  unfold tailWord_3929188
  simp only [CollatzResearch.WordTrace]
  refine ⟨71654629844615201365170109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95539506459486935153560145 71654629844615201365170109)
  ·
    refine ⟨26870486191730700511938791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71654629844615201365170109 26870486191730700511938791)
    ·
      refine ⟨40305729287596050767908187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26870486191730700511938791 40305729287596050767908187)
      ·
        refine ⟨60458593931394076151862281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40305729287596050767908187 60458593931394076151862281)
        ·
          refine ⟨45343945448545557113896711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60458593931394076151862281 45343945448545557113896711)
          ·
            refine ⟨68015918172818335670845067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45343945448545557113896711 68015918172818335670845067)
            ·
              refine ⟨102023877259227503506267601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68015918172818335670845067 102023877259227503506267601)
              ·
                refine ⟨76517907944420627629700701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102023877259227503506267601 76517907944420627629700701)
                ·
                  refine ⟨28694215479157735361137763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76517907944420627629700701 28694215479157735361137763)
                  ·
                    refine ⟨43041323218736603041706645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28694215479157735361137763 43041323218736603041706645)
                    ·
                      refine ⟨2017562025878278267579999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43041323218736603041706645 2017562025878278267579999)
                      ·
                        rfl

theorem cell23_3929188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_3929188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929188 prefixEnd_3929188 := by exact prefixLift 3929188
  have htrace : WordTrace (prefixWord ++ tailWord_3929188) baseStart_3929188 baseEnd_3929188 := by
    simpa [prefixWord, tailWord_3929188, baseEnd_3929188] using wordTrace_append hprefix tailTrace_3929188
  have hstable : (prefixWord ++ tailWord_3929188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929188).length < 2 ^ (prefixWord ++ tailWord_3929188).sum := by decide
  have hdescent : baseEnd_3929188 < baseStart_3929188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929228 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 2, 7]
def baseStart_3929228 : Nat := 118140960795 + 3929228 * 2 ^ 59
def prefixEnd_3929228 : Nat := 4983230072969 + 3 ^ 40 * 3929228 * 2
def baseEnd_3929228 : Nat := 672527521701486037026605

theorem tailTrace_3929228 : CollatzResearch.WordTrace tailWord_3929228 prefixEnd_3929228 672527521701486037026605 := by
  unfold tailWord_3929228
  simp only [CollatzResearch.WordTrace]
  refine ⟨71655359304542744780898169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95540479072723659707864225 71655359304542744780898169)
  ·
    refine ⟨53741519478407058585673627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71655359304542744780898169 53741519478407058585673627)
    ·
      refine ⟨80612279217610587878510441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53741519478407058585673627 80612279217610587878510441)
      ·
        refine ⟨60459209413207940908882831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80612279217610587878510441 60459209413207940908882831)
        ·
          refine ⟨90688814119811911363324247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60459209413207940908882831 90688814119811911363324247)
          ·
            refine ⟨136033221179717867044986371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90688814119811911363324247 136033221179717867044986371)
            ·
              refine ⟨204049831769576800567479557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136033221179717867044986371 204049831769576800567479557)
              ·
                refine ⟨38259343456795650106402417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204049831769576800567479557 38259343456795650106402417)
                ·
                  refine ⟨28694507592596737579801813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38259343456795650106402417 28694507592596737579801813)
                  ·
                    refine ⟨672527521701486037026605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28694507592596737579801813 672527521701486037026605)
                    ·
                      rfl

theorem cell23_3929228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_3929228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929228 prefixEnd_3929228 := by exact prefixLift 3929228
  have htrace : WordTrace (prefixWord ++ tailWord_3929228) baseStart_3929228 baseEnd_3929228 := by
    simpa [prefixWord, tailWord_3929228, baseEnd_3929228] using wordTrace_append hprefix tailTrace_3929228
  have hstable : (prefixWord ++ tailWord_3929228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929228).length < 2 ^ (prefixWord ++ tailWord_3929228).sum := by decide
  have hdescent : baseEnd_3929228 < baseStart_3929228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929270 : List Nat := [5, 1, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_3929270 : Nat := 118140960795 + 3929270 * 2 ^ 59
def prefixEnd_3929270 : Nat := 4983230072969 + 3 ^ 40 * 3929270 * 2
def baseEnd_3929270 : Nat := 672534710430648982251541

theorem tailTrace_3929270 : CollatzResearch.WordTrace tailWord_3929270 prefixEnd_3929270 672534710430648982251541 := by
  unfold tailWord_3929270
  simp only [CollatzResearch.WordTrace]
  refine ⟨8957015654683333170926579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95541500316622220489883509 8957015654683333170926579)
  ·
    refine ⟨13435523482024999756389869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8957015654683333170926579 13435523482024999756389869)
    ·
      refine ⟨5038321305759374908646201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13435523482024999756389869 5038321305759374908646201)
      ·
        refine ⟨3778740979319531181484651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5038321305759374908646201 3778740979319531181484651)
        ·
          refine ⟨5668111468979296772226977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3778740979319531181484651 5668111468979296772226977)
          ·
            refine ⟨4251083601734472579170233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5668111468979296772226977 4251083601734472579170233)
            ·
              refine ⟨3188312701300854434377675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4251083601734472579170233 3188312701300854434377675)
              ·
                refine ⟨4782469051951281651566513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3188312701300854434377675 4782469051951281651566513)
                ·
                  refine ⟨3586851788963461238674885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4782469051951281651566513 3586851788963461238674885)
                  ·
                    refine ⟨672534710430648982251541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3586851788963461238674885 672534710430648982251541)
                    ·
                      rfl

theorem cell23_3929270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_3929270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929270 prefixEnd_3929270 := by exact prefixLift 3929270
  have htrace : WordTrace (prefixWord ++ tailWord_3929270) baseStart_3929270 baseEnd_3929270 := by
    simpa [prefixWord, tailWord_3929270, baseEnd_3929270] using wordTrace_append hprefix tailTrace_3929270
  have hstable : (prefixWord ++ tailWord_3929270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929270).length < 2 ^ (prefixWord ++ tailWord_3929270).sum := by decide
  have hdescent : baseEnd_3929270 < baseStart_3929270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929276 : List Nat := [2, 2, 2, 3, 2, 1, 4, 1, 2, 1, 3]
def baseStart_3929276 : Nat := 118140960795 + 3929276 * 2 ^ 59
def prefixEnd_3929276 : Nat := 4983230072969 + 3 ^ 40 * 3929276 * 2
def baseEnd_3929276 : Nat := 2017607212175873923279595

theorem tailTrace_3929276 : CollatzResearch.WordTrace tailWord_3929276 prefixEnd_3929276 2017607212175873923279595 := by
  unfold tailWord_3929276
  simp only [CollatzResearch.WordTrace]
  refine ⟨71656234656455796879771841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95541646208607729173029121 71656234656455796879771841)
  ·
    refine ⟨53742175992341847659828881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71656234656455796879771841 53742175992341847659828881)
    ·
      refine ⟨40306631994256385744871661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53742175992341847659828881 40306631994256385744871661)
      ·
        refine ⟨15114986997846144654326873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40306631994256385744871661 15114986997846144654326873)
        ·
          refine ⟨11336240248384608490745155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15114986997846144654326873 11336240248384608490745155)
          ·
            refine ⟨17004360372576912736117733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11336240248384608490745155 17004360372576912736117733)
            ·
              refine ⟨3188317569858171138022075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17004360372576912736117733 3188317569858171138022075)
              ·
                refine ⟨4782476354787256707033113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3188317569858171138022075 4782476354787256707033113)
                ·
                  refine ⟨3586857266090442530274835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4782476354787256707033113 3586857266090442530274835)
                  ·
                    refine ⟨5380285899135663795412253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3586857266090442530274835 5380285899135663795412253)
                    ·
                      refine ⟨2017607212175873923279595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5380285899135663795412253 2017607212175873923279595)
                      ·
                        rfl

theorem cell23_3929276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_3929276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929276 prefixEnd_3929276 := by exact prefixLift 3929276
  have htrace : WordTrace (prefixWord ++ tailWord_3929276) baseStart_3929276 baseEnd_3929276 := by
    simpa [prefixWord, tailWord_3929276, baseEnd_3929276] using wordTrace_append hprefix tailTrace_3929276
  have hstable : (prefixWord ++ tailWord_3929276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929276).length < 2 ^ (prefixWord ++ tailWord_3929276).sum := by decide
  have hdescent : baseEnd_3929276 < baseStart_3929276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929352 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 1, 7]
def baseStart_3929352 : Nat := 118140960795 + 3929352 * 2 ^ 59
def prefixEnd_3929352 : Nat := 4983230072969 + 3 ^ 40 * 3929352 * 2
def baseEnd_3929352 : Nat := 672548745568538541976415

theorem tailTrace_3929352 : CollatzResearch.WordTrace tailWord_3929352 prefixEnd_3929352 672548745568538541976415 := by
  unfold tailWord_3929352
  simp only [CollatzResearch.WordTrace]
  refine ⟨71657620630318129369655155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95543494173757505826206873 71657620630318129369655155)
  ·
    refine ⟨107486430945477194054482733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71657620630318129369655155 107486430945477194054482733)
    ·
      refine ⟨40307411604553947770431025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107486430945477194054482733 40307411604553947770431025)
      ·
        refine ⟨30230558703415460827823269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40307411604553947770431025 30230558703415460827823269)
        ·
          refine ⟨5668229756890398905216863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30230558703415460827823269 5668229756890398905216863)
          ·
            refine ⟨8502344635335598357825295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5668229756890398905216863 8502344635335598357825295)
            ·
              refine ⟨12753516953003397536737943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8502344635335598357825295 12753516953003397536737943)
              ·
                refine ⟨19130275429505096305106915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12753516953003397536737943 19130275429505096305106915)
                ·
                  refine ⟨28695413144257644457660373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19130275429505096305106915 28695413144257644457660373)
                  ·
                    refine ⟨672548745568538541976415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28695413144257644457660373 672548745568538541976415)
                    ·
                      rfl

theorem cell23_3929352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_3929352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929352 prefixEnd_3929352 := by exact prefixLift 3929352
  have htrace : WordTrace (prefixWord ++ tailWord_3929352) baseStart_3929352 baseEnd_3929352 := by
    simpa [prefixWord, tailWord_3929352, baseEnd_3929352] using wordTrace_append hprefix tailTrace_3929352
  have hstable : (prefixWord ++ tailWord_3929352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929352).length < 2 ^ (prefixWord ++ tailWord_3929352).sum := by decide
  have hdescent : baseEnd_3929352 < baseStart_3929352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929372 : List Nat := [2, 2, 3, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_3929372 : Nat := 118140960795 + 3929372 * 2 ^ 59
def prefixEnd_3929372 : Nat := 4983230072969 + 3 ^ 40 * 3929372 * 2
def baseEnd_3929372 : Nat := 2017656506318705547679153

theorem tailTrace_3929372 : CollatzResearch.WordTrace tailWord_3929372 prefixEnd_3929372 2017656506318705547679153 := by
  unfold tailWord_3929372
  simp only [CollatzResearch.WordTrace]
  refine ⟨71657985360281901077519185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95543980480375868103358913 71657985360281901077519185)
  ·
    refine ⟨53743489020211425808139389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71657985360281901077519185 53743489020211425808139389)
    ·
      refine ⟨20153808382579284678052271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53743489020211425808139389 20153808382579284678052271)
      ·
        refine ⟨30230712573868927017078407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20153808382579284678052271 30230712573868927017078407)
        ·
          refine ⟨45346068860803390525617611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30230712573868927017078407 45346068860803390525617611)
          ·
            refine ⟨68019103291205085788426417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45346068860803390525617611 68019103291205085788426417)
            ·
              refine ⟨51014327468403814341319813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68019103291205085788426417 51014327468403814341319813)
              ·
                refine ⟨9565186400325715188997465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51014327468403814341319813 9565186400325715188997465)
                ·
                  refine ⟨7173889800244286391748099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9565186400325715188997465 7173889800244286391748099)
                  ·
                    refine ⟨10760834700366429587622149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7173889800244286391748099 10760834700366429587622149)
                    ·
                      refine ⟨2017656506318705547679153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10760834700366429587622149 2017656506318705547679153)
                      ·
                        rfl

theorem cell23_3929372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_3929372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929372 prefixEnd_3929372 := by exact prefixLift 3929372
  have htrace : WordTrace (prefixWord ++ tailWord_3929372) baseStart_3929372 baseEnd_3929372 := by
    simpa [prefixWord, tailWord_3929372, baseEnd_3929372] using wordTrace_append hprefix tailTrace_3929372
  have hstable : (prefixWord ++ tailWord_3929372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929372).length < 2 ^ (prefixWord ++ tailWord_3929372).sum := by decide
  have hdescent : baseEnd_3929372 < baseStart_3929372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929389 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_3929389 : Nat := 118140960795 + 3929389 * 2 ^ 59
def prefixEnd_3929389 : Nat := 4983230072969 + 3 ^ 40 * 3929389 * 2
def baseEnd_3929389 : Nat := 2017665235489831981166575

theorem tailTrace_3929389 : CollatzResearch.WordTrace tailWord_3929389 prefixEnd_3929389 2017665235489831981166575 := by
  unfold tailWord_3929389
  simp only [CollatzResearch.WordTrace]
  refine ⟨143316590761502214058407221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95544393841001476038938147 143316590761502214058407221)
  ·
    refine ⟨13435930383890832567975677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143316590761502214058407221 13435930383890832567975677)
    ·
      refine ⟨5038473893959062212990879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13435930383890832567975677 5038473893959062212990879)
      ·
        refine ⟨7557710840938593319486319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5038473893959062212990879 7557710840938593319486319)
        ·
          refine ⟨11336566261407889979229479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7557710840938593319486319 11336566261407889979229479)
          ·
            refine ⟨17004849392111834968844219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11336566261407889979229479 17004849392111834968844219)
            ·
              refine ⟨25507274088167752453266329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17004849392111834968844219 25507274088167752453266329)
              ·
                refine ⟨19130455566125814339949747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25507274088167752453266329 19130455566125814339949747)
                ·
                  refine ⟨28695683349188721509924621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19130455566125814339949747 28695683349188721509924621)
                  ·
                    refine ⟨10760881255945770566221733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28695683349188721509924621 10760881255945770566221733)
                    ·
                      refine ⟨2017665235489831981166575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10760881255945770566221733 2017665235489831981166575)
                      ·
                        rfl

theorem cell23_3929389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_3929389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929389 prefixEnd_3929389 := by exact prefixLift 3929389
  have htrace : WordTrace (prefixWord ++ tailWord_3929389) baseStart_3929389 baseEnd_3929389 := by
    simpa [prefixWord, tailWord_3929389, baseEnd_3929389] using wordTrace_append hprefix tailTrace_3929389
  have hstable : (prefixWord ++ tailWord_3929389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929389).length < 2 ^ (prefixWord ++ tailWord_3929389).sum := by decide
  have hdescent : baseEnd_3929389 < baseStart_3929389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929409 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_3929409 : Nat := 118140960795 + 3929409 * 2 ^ 59
def prefixEnd_3929409 : Nat := 4983230072969 + 3 ^ 40 * 3929409 * 2
def baseEnd_3929409 : Nat := 2017675505102921902916483

theorem tailTrace_3929409 : CollatzResearch.WordTrace tailWord_3929409 prefixEnd_3929409 2017675505102921902916483 := by
  unfold tailWord_3929409
  simp only [CollatzResearch.WordTrace]
  refine ⟨143317320221429757474135281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95544880147619838316090187 143317320221429757474135281)
  ·
    refine ⟨107487990166072318105601461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143317320221429757474135281 107487990166072318105601461)
    ·
      refine ⟨10076999078069279822400137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107487990166072318105601461 10076999078069279822400137)
      ·
        refine ⟨7557749308551959866800103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10076999078069279822400137 7557749308551959866800103)
        ·
          refine ⟨11336623962827939800200155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7557749308551959866800103 11336623962827939800200155)
          ·
            refine ⟨17004935944241909700300233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11336623962827939800200155 17004935944241909700300233)
            ·
              refine ⟨12753701958181432275225175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17004935944241909700300233 12753701958181432275225175)
              ·
                refine ⟨19130552937272148412837763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12753701958181432275225175 19130552937272148412837763)
                ·
                  refine ⟨28695829405908222619256645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19130552937272148412837763 28695829405908222619256645)
                  ·
                    refine ⟨5380468013607791741110621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28695829405908222619256645 5380468013607791741110621)
                    ·
                      refine ⟨2017675505102921902916483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5380468013607791741110621 2017675505102921902916483)
                      ·
                        rfl

theorem cell23_3929409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_3929409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929409 prefixEnd_3929409 := by exact prefixLift 3929409
  have htrace : WordTrace (prefixWord ++ tailWord_3929409) baseStart_3929409 baseEnd_3929409 := by
    simpa [prefixWord, tailWord_3929409, baseEnd_3929409] using wordTrace_append hprefix tailTrace_3929409
  have hstable : (prefixWord ++ tailWord_3929409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929409).length < 2 ^ (prefixWord ++ tailWord_3929409).sum := by decide
  have hdescent : baseEnd_3929409 < baseStart_3929409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929472 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 6, 4]
def baseStart_3929472 : Nat := 118140960795 + 3929472 * 2 ^ 59
def prefixEnd_3929472 : Nat := 4983230072969 + 3 ^ 40 * 3929472 * 2
def baseEnd_3929472 : Nat := 672569284794718385476231

theorem tailTrace_3929472 : CollatzResearch.WordTrace tailWord_3929472 prefixEnd_3929472 672569284794718385476231 := by
  unfold tailWord_3929472
  simp only [CollatzResearch.WordTrace]
  refine ⟨71659809010100759616839335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95546412013467679489119113 71659809010100759616839335)
  ·
    refine ⟨107489713515151139425259003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71659809010100759616839335 107489713515151139425259003)
    ·
      refine ⟨161234570272726709137888505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107489713515151139425259003 161234570272726709137888505)
      ·
        refine ⟨120925927704545031853416379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161234570272726709137888505 120925927704545031853416379)
        ·
          refine ⟨181388891556817547780124569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120925927704545031853416379 181388891556817547780124569)
          ·
            refine ⟨136041668667613160835093427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181388891556817547780124569 136041668667613160835093427)
            ·
              refine ⟨204062503001419741252640141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136041668667613160835093427 204062503001419741252640141)
              ·
                refine ⟨76523438625532402969740053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 204062503001419741252640141 76523438625532402969740053)
                ·
                  refine ⟨3587036185571831389206565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76523438625532402969740053 3587036185571831389206565)
                  ·
                    refine ⟨672569284794718385476231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3587036185571831389206565 672569284794718385476231)
                    ·
                      rfl

theorem cell23_3929472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 6, 4].length) (baseStart_3929472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929472 prefixEnd_3929472 := by exact prefixLift 3929472
  have htrace : WordTrace (prefixWord ++ tailWord_3929472) baseStart_3929472 baseEnd_3929472 := by
    simpa [prefixWord, tailWord_3929472, baseEnd_3929472] using wordTrace_append hprefix tailTrace_3929472
  have hstable : (prefixWord ++ tailWord_3929472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929472).length < 2 ^ (prefixWord ++ tailWord_3929472).sum := by decide
  have hdescent : baseEnd_3929472 < baseStart_3929472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929476 : List Nat := [2, 3, 2, 1, 1, 4, 3, 1, 1, 5]
def baseStart_3929476 : Nat := 118140960795 + 3929476 * 2 ^ 59
def prefixEnd_3929476 : Nat := 4983230072969 + 3 ^ 40 * 3929476 * 2
def baseEnd_3929476 : Nat := 672569969435591046926225

theorem tailTrace_3929476 : CollatzResearch.WordTrace tailWord_3929476 prefixEnd_3929476 672569969435591046926225 := by
  unfold tailWord_3929476
  simp only [CollatzResearch.WordTrace]
  refine ⟨71659881956093513958412141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95546509274791351944549521 71659881956093513958412141)
  ·
    refine ⟨26872455733535067734404553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71659881956093513958412141 26872455733535067734404553)
    ·
      refine ⟨20154341800151300800803415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26872455733535067734404553 20154341800151300800803415)
      ·
        refine ⟨30231512700226951201205123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20154341800151300800803415 30231512700226951201205123)
        ·
          refine ⟨45347269050340426801807685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30231512700226951201205123 45347269050340426801807685)
          ·
            refine ⟨8502612946938830025338941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45347269050340426801807685 8502612946938830025338941)
            ·
              refine ⟨3188479855102061259502103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8502612946938830025338941 3188479855102061259502103)
              ·
                refine ⟨4782719782653091889253155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3188479855102061259502103 4782719782653091889253155)
                ·
                  refine ⟨7174079673979637833879733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4782719782653091889253155 7174079673979637833879733)
                  ·
                    refine ⟨672569969435591046926225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7174079673979637833879733 672569969435591046926225)
                    ·
                      rfl

theorem cell23_3929476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_3929476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929476 prefixEnd_3929476 := by exact prefixLift 3929476
  have htrace : WordTrace (prefixWord ++ tailWord_3929476) baseStart_3929476 baseEnd_3929476 := by
    simpa [prefixWord, tailWord_3929476, baseEnd_3929476] using wordTrace_append hprefix tailTrace_3929476
  have hstable : (prefixWord ++ tailWord_3929476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929476).length < 2 ^ (prefixWord ++ tailWord_3929476).sum := by decide
  have hdescent : baseEnd_3929476 < baseStart_3929476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929506 : List Nat := [3, 3, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_3929506 : Nat := 118140960795 + 3929506 * 2 ^ 59
def prefixEnd_3929506 : Nat := 4983230072969 + 3 ^ 40 * 3929506 * 2
def baseEnd_3929506 : Nat := 672575104242136007801179

theorem tailTrace_3929506 : CollatzResearch.WordTrace tailWord_3929506 prefixEnd_3929506 672575104242136007801179 := by
  unfold tailWord_3929506
  simp only [CollatzResearch.WordTrace]
  refine ⟨35830214525519585760104093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95547238734718895360277581 35830214525519585760104093)
  ·
    refine ⟨13436330447069844660039035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35830214525519585760104093 13436330447069844660039035)
    ·
      refine ⟨20154495670604766990058553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13436330447069844660039035 20154495670604766990058553)
      ·
        refine ⟨15115871752953575242543915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20154495670604766990058553 15115871752953575242543915)
        ·
          refine ⟨22673807629430362863815873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15115871752953575242543915 22673807629430362863815873)
          ·
            refine ⟨17005355722072772147861905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22673807629430362863815873 17005355722072772147861905)
            ·
              refine ⟨12754016791554579110896429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17005355722072772147861905 12754016791554579110896429)
              ·
                refine ⟨4782756296832967166586161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12754016791554579110896429 4782756296832967166586161)
                ·
                  refine ⟨3587067222624725374939621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4782756296832967166586161 3587067222624725374939621)
                  ·
                    refine ⟨672575104242136007801179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3587067222624725374939621 672575104242136007801179)
                    ·
                      rfl

theorem cell23_3929506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_3929506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929506 prefixEnd_3929506 := by exact prefixLift 3929506
  have htrace : WordTrace (prefixWord ++ tailWord_3929506) baseStart_3929506 baseEnd_3929506 := by
    simpa [prefixWord, tailWord_3929506, baseEnd_3929506] using wordTrace_append hprefix tailTrace_3929506
  have hstable : (prefixWord ++ tailWord_3929506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929506).length < 2 ^ (prefixWord ++ tailWord_3929506).sum := by decide
  have hdescent : baseEnd_3929506 < baseStart_3929506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929546 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 4, 1, 3]
def baseStart_3929546 : Nat := 118140960795 + 3929546 * 2 ^ 59
def prefixEnd_3929546 : Nat := 4983230072969 + 3 ^ 40 * 3929546 * 2
def baseEnd_3929546 : Nat := 2017745851952587866903353

theorem tailTrace_3929546 : CollatzResearch.WordTrace tailWord_3929546 prefixEnd_3929546 2017745851952587866903353 := by
  unfold tailWord_3929546
  simp only [CollatzResearch.WordTrace]
  refine ⟨35830579255483357467968123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95548211347955619914581661 35830579255483357467968123)
  ·
    refine ⟨53745868883225036201952185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35830579255483357467968123 53745868883225036201952185)
    ·
      refine ⟨40309401662418777151464139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53745868883225036201952185 40309401662418777151464139)
      ·
        refine ⟨60464102493628165727196209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40309401662418777151464139 60464102493628165727196209)
        ·
          refine ⟨45348076870221124295397157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60464102493628165727196209 45348076870221124295397157)
          ·
            refine ⟨8502764413166460805386967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45348076870221124295397157 8502764413166460805386967)
            ·
              refine ⟨12754146619749691208080451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8502764413166460805386967 12754146619749691208080451)
              ·
                refine ⟨19131219929624536812120677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12754146619749691208080451 19131219929624536812120677)
                ·
                  refine ⟨3587103736804600652272627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19131219929624536812120677 3587103736804600652272627)
                  ·
                    refine ⟨5380655605206900978408941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3587103736804600652272627 5380655605206900978408941)
                    ·
                      refine ⟨2017745851952587866903353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5380655605206900978408941 2017745851952587866903353)
                      ·
                        rfl

theorem cell23_3929546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_3929546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929546 prefixEnd_3929546 := by exact prefixLift 3929546
  have htrace : WordTrace (prefixWord ++ tailWord_3929546) baseStart_3929546 baseEnd_3929546 := by
    simpa [prefixWord, tailWord_3929546, baseEnd_3929546] using wordTrace_append hprefix tailTrace_3929546
  have hstable : (prefixWord ++ tailWord_3929546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929546).length < 2 ^ (prefixWord ++ tailWord_3929546).sum := by decide
  have hdescent : baseEnd_3929546 < baseStart_3929546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929572 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_3929572 : Nat := 118140960795 + 3929572 * 2 ^ 59
def prefixEnd_3929572 : Nat := 4983230072969 + 3 ^ 40 * 3929572 * 2
def baseEnd_3929572 : Nat := 2017759202449604765178233

theorem tailTrace_3929572 : CollatzResearch.WordTrace tailWord_3929572 prefixEnd_3929572 2017759202449604765178233 := by
  unfold tailWord_3929572
  simp only [CollatzResearch.WordTrace]
  refine ⟨71661632659919618156159485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95548843546559490874879313 71661632659919618156159485)
  ·
    refine ⟨26873112247469856808559807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71661632659919618156159485 26873112247469856808559807)
    ·
      refine ⟨40309668371204785212839711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26873112247469856808559807 40309668371204785212839711)
      ·
        refine ⟨60464502556807177819259567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40309668371204785212839711 60464502556807177819259567)
        ·
          refine ⟨90696753835210766728889351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60464502556807177819259567 90696753835210766728889351)
          ·
            refine ⟨136045130752816150093334027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90696753835210766728889351 136045130752816150093334027)
            ·
              refine ⟨204067696129224225140001041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136045130752816150093334027 204067696129224225140001041)
              ·
                refine ⟨153050772096918168855000781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204067696129224225140001041 153050772096918168855000781)
                ·
                  refine ⟨57394039536344313320625293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153050772096918168855000781 57394039536344313320625293)
                  ·
                    refine ⟨21522764826129117495234485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57394039536344313320625293 21522764826129117495234485)
                    ·
                      refine ⟨2017759202449604765178233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21522764826129117495234485 2017759202449604765178233)
                      ·
                        rfl

theorem cell23_3929572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_3929572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929572 prefixEnd_3929572 := by exact prefixLift 3929572
  have htrace : WordTrace (prefixWord ++ tailWord_3929572) baseStart_3929572 baseEnd_3929572 := by
    simpa [prefixWord, tailWord_3929572, baseEnd_3929572] using wordTrace_append hprefix tailTrace_3929572
  have hstable : (prefixWord ++ tailWord_3929572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929572).length < 2 ^ (prefixWord ++ tailWord_3929572).sum := by decide
  have hdescent : baseEnd_3929572 < baseStart_3929572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929573 : List Nat := [1, 3, 1, 5, 1, 1, 1, 4, 1, 3, 2]
def baseStart_3929573 : Nat := 118140960795 + 3929573 * 2 ^ 59
def prefixEnd_3929573 : Nat := 4983230072969 + 3 ^ 40 * 3929573 * 2
def baseEnd_3929573 : Nat := 2017759715930259261265729

theorem tailTrace_3929573 : CollatzResearch.WordTrace tailWord_3929573 prefixEnd_3929573 2017759715930259261265729 := by
  unfold tailWord_3929573
  simp only [CollatzResearch.WordTrace]
  refine ⟨143323301792835613483105373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95548867861890408988736915 143323301792835613483105373)
  ·
    refine ⟨53746238172313355056164515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143323301792835613483105373 53746238172313355056164515)
    ·
      refine ⟨80619357258470032584246773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53746238172313355056164515 80619357258470032584246773)
      ·
        refine ⟨7558064742981565554773135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80619357258470032584246773 7558064742981565554773135)
        ·
          refine ⟨11337097114472348332159703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7558064742981565554773135 11337097114472348332159703)
          ·
            refine ⟨17005645671708522498239555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11337097114472348332159703 17005645671708522498239555)
            ·
              refine ⟨25508468507562783747359333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17005645671708522498239555 25508468507562783747359333)
              ·
                refine ⟨4782837845168021952629875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25508468507562783747359333 4782837845168021952629875)
                ·
                  refine ⟨7174256767752032928944813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4782837845168021952629875 7174256767752032928944813)
                  ·
                    refine ⟨2690346287907012348354305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7174256767752032928944813 2690346287907012348354305)
                    ·
                      refine ⟨2017759715930259261265729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2690346287907012348354305 2017759715930259261265729)
                      ·
                        rfl

theorem cell23_3929573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_3929573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929573 prefixEnd_3929573 := by exact prefixLift 3929573
  have htrace : WordTrace (prefixWord ++ tailWord_3929573) baseStart_3929573 baseEnd_3929573 := by
    simpa [prefixWord, tailWord_3929573, baseEnd_3929573] using wordTrace_append hprefix tailTrace_3929573
  have hstable : (prefixWord ++ tailWord_3929573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929573).length < 2 ^ (prefixWord ++ tailWord_3929573).sum := by decide
  have hdescent : baseEnd_3929573 < baseStart_3929573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929660 : List Nat := [2, 2, 2, 2, 4, 2, 2, 2, 5]
def baseStart_3929660 : Nat := 118140960795 + 3929660 * 2 ^ 59
def prefixEnd_3929660 : Nat := 4983230072969 + 3 ^ 40 * 3929660 * 2
def baseEnd_3929660 : Nat := 224200487638577824541981

theorem tailTrace_3929660 : CollatzResearch.WordTrace tailWord_3929660 prefixEnd_3929660 224200487638577824541981 := by
  unfold tailWord_3929660
  simp only [CollatzResearch.WordTrace]
  refine ⟨71663237471760213670761217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95550983295680284894348289 71663237471760213670761217)
  ·
    refine ⟨53747428103820160253070913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71663237471760213670761217 53747428103820160253070913)
    ·
      refine ⟨40310571077865120189803185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53747428103820160253070913 40310571077865120189803185)
      ·
        refine ⟨30232928308398840142352389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40310571077865120189803185 30232928308398840142352389)
        ·
          refine ⟨5668674057824782526691073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30232928308398840142352389 5668674057824782526691073)
          ·
            refine ⟨4251505543368586895018305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5668674057824782526691073 4251505543368586895018305)
            ·
              refine ⟨3188629157526440171263729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4251505543368586895018305 3188629157526440171263729)
              ·
                refine ⟨2391471868144830128447797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3188629157526440171263729 2391471868144830128447797)
                ·
                  refine ⟨224200487638577824541981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2391471868144830128447797 224200487638577824541981)
                  ·
                    rfl

theorem cell23_3929660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 5].length) (baseStart_3929660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929660 prefixEnd_3929660 := by exact prefixLift 3929660
  have htrace : WordTrace (prefixWord ++ tailWord_3929660) baseStart_3929660 baseEnd_3929660 := by
    simpa [prefixWord, tailWord_3929660, baseEnd_3929660] using wordTrace_append hprefix tailTrace_3929660
  have hstable : (prefixWord ++ tailWord_3929660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929660).length < 2 ^ (prefixWord ++ tailWord_3929660).sum := by decide
  have hdescent : baseEnd_3929660 < baseStart_3929660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929670 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_3929670 : Nat := 118140960795 + 3929670 * 2 ^ 59
def prefixEnd_3929670 : Nat := 4983230072969 + 3 ^ 40 * 3929670 * 2
def baseEnd_3929670 : Nat := 2017809523553745381752783

theorem tailTrace_3929670 : CollatzResearch.WordTrace tailWord_3929670 prefixEnd_3929670 2017809523553745381752783 := by
  unfold tailWord_3929670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4478963739796381220293327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95551226448989466032924309 4478963739796381220293327)
  ·
    refine ⟨6718445609694571830439991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4478963739796381220293327 6718445609694571830439991)
    ·
      refine ⟨10077668414541857745659987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6718445609694571830439991 10077668414541857745659987)
      ·
        refine ⟨15116502621812786618489981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10077668414541857745659987 15116502621812786618489981)
        ·
          refine ⟨5668688483179794981933743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15116502621812786618489981 5668688483179794981933743)
          ·
            refine ⟨8503032724769692472900615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5668688483179794981933743 8503032724769692472900615)
            ·
              refine ⟨12754549087154538709350923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8503032724769692472900615 12754549087154538709350923)
              ·
                refine ⟨19131823630731808064026385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12754549087154538709350923 19131823630731808064026385)
                ·
                  refine ⟨14348867723048856048019789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19131823630731808064026385 14348867723048856048019789)
                  ·
                    refine ⟨5380825396143321018007421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14348867723048856048019789 5380825396143321018007421)
                    ·
                      refine ⟨2017809523553745381752783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5380825396143321018007421 2017809523553745381752783)
                      ·
                        rfl

theorem cell23_3929670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_3929670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929670 prefixEnd_3929670 := by exact prefixLift 3929670
  have htrace : WordTrace (prefixWord ++ tailWord_3929670) baseStart_3929670 baseEnd_3929670 := by
    simpa [prefixWord, tailWord_3929670, baseEnd_3929670] using wordTrace_append hprefix tailTrace_3929670
  have hstable : (prefixWord ++ tailWord_3929670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929670).length < 2 ^ (prefixWord ++ tailWord_3929670).sum := by decide
  have hdescent : baseEnd_3929670 < baseStart_3929670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929676 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 1, 6, 2]
def baseStart_3929676 : Nat := 118140960795 + 3929676 * 2 ^ 59
def prefixEnd_3929676 : Nat := 4983230072969 + 3 ^ 40 * 3929676 * 2
def baseEnd_3929676 : Nat := 2017812604437672358277755

theorem tailTrace_3929676 : CollatzResearch.WordTrace tailWord_3929676 prefixEnd_3929676 2017812604437672358277755 := by
  unfold tailWord_3929676
  simp only [CollatzResearch.WordTrace]
  refine ⟨71663529255731231037052441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95551372340974974716069921 71663529255731231037052441)
  ·
    refine ⟨53747646941798423277789331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71663529255731231037052441 53747646941798423277789331)
    ·
      refine ⟨80621470412697634916683997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53747646941798423277789331 80621470412697634916683997)
      ·
        refine ⟨30233051404761613093756499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80621470412697634916683997 30233051404761613093756499)
        ·
          refine ⟨45349577107142419640634749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30233051404761613093756499 45349577107142419640634749)
          ·
            refine ⟨17006091415178407365238031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45349577107142419640634749 17006091415178407365238031)
            ·
              refine ⟨25509137122767611047857047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17006091415178407365238031 25509137122767611047857047)
              ·
                refine ⟨38263705684151416571785571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25509137122767611047857047 38263705684151416571785571)
                ·
                  refine ⟨57395558526227124857678357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38263705684151416571785571 57395558526227124857678357)
                  ·
                    refine ⟨2690416805916896477703673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57395558526227124857678357 2690416805916896477703673)
                    ·
                      refine ⟨2017812604437672358277755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2690416805916896477703673 2017812604437672358277755)
                      ·
                        rfl

theorem cell23_3929676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_3929676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929676 prefixEnd_3929676 := by exact prefixLift 3929676
  have htrace : WordTrace (prefixWord ++ tailWord_3929676) baseStart_3929676 baseEnd_3929676 := by
    simpa [prefixWord, tailWord_3929676, baseEnd_3929676] using wordTrace_append hprefix tailTrace_3929676
  have hstable : (prefixWord ++ tailWord_3929676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929676).length < 2 ^ (prefixWord ++ tailWord_3929676).sum := by decide
  have hdescent : baseEnd_3929676 < baseStart_3929676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929679 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 3]
def baseStart_3929679 : Nat := 118140960795 + 3929679 * 2 ^ 59
def prefixEnd_3929679 : Nat := 4983230072969 + 3 ^ 40 * 3929679 * 2
def baseEnd_3929679 : Nat := 2017814144879635846540241

theorem tailTrace_3929679 : CollatzResearch.WordTrace tailWord_3929679 prefixEnd_3929679 2017814144879635846540241 := by
  unfold tailWord_3929679
  simp only [CollatzResearch.WordTrace]
  refine ⟨143327167930451593586464091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95551445286967729057642727 143327167930451593586464091)
  ·
    refine ⟨214990751895677390379696137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143327167930451593586464091 214990751895677390379696137)
    ·
      refine ⟨161243063921758042784772103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214990751895677390379696137 161243063921758042784772103)
      ·
        refine ⟨241864595882637064177158155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161243063921758042784772103 241864595882637064177158155)
        ·
          refine ⟨362796893823955596265737233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241864595882637064177158155 362796893823955596265737233)
          ·
            refine ⟨272097670367966697199302925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362796893823955596265737233 272097670367966697199302925)
            ·
              refine ⟨102036626387987511449738597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272097670367966697199302925 102036626387987511449738597)
              ·
                refine ⟨19131867447747658396825987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102036626387987511449738597 19131867447747658396825987)
                ·
                  refine ⟨28697801171621487595238981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19131867447747658396825987 28697801171621487595238981)
                  ·
                    refine ⟨5380837719679028924107309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28697801171621487595238981 5380837719679028924107309)
                    ·
                      refine ⟨2017814144879635846540241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5380837719679028924107309 2017814144879635846540241)
                      ·
                        rfl

theorem cell23_3929679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 3].length) (baseStart_3929679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929679 prefixEnd_3929679 := by exact prefixLift 3929679
  have htrace : WordTrace (prefixWord ++ tailWord_3929679) baseStart_3929679 baseEnd_3929679 := by
    simpa [prefixWord, tailWord_3929679, baseEnd_3929679] using wordTrace_append hprefix tailTrace_3929679
  have hstable : (prefixWord ++ tailWord_3929679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929679).length < 2 ^ (prefixWord ++ tailWord_3929679).sum := by decide
  have hdescent : baseEnd_3929679 < baseStart_3929679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929703 : List Nat := [1, 1, 5, 1, 1, 1, 3, 5, 1, 4]
def baseStart_3929703 : Nat := 118140960795 + 3929703 * 2 ^ 59
def prefixEnd_3929703 : Nat := 4983230072969 + 3 ^ 40 * 3929703 * 2
def baseEnd_3929703 : Nat := 672608822805114584213377

theorem tailTrace_3929703 : CollatzResearch.WordTrace tailWord_3929703 prefixEnd_3929703 672608822805114584213377 := by
  unfold tailWord_3929703
  simp only [CollatzResearch.WordTrace]
  refine ⟨143328043282364645685337763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95552028854909763790225175 143328043282364645685337763)
  ·
    refine ⟨214992064923546968528006645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143328043282364645685337763 214992064923546968528006645)
    ·
      refine ⟨20155506086582528299500623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214992064923546968528006645 20155506086582528299500623)
      ·
        refine ⟨30233259129873792449250935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20155506086582528299500623 30233259129873792449250935)
        ·
          refine ⟨45349888694810688673876403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30233259129873792449250935 45349888694810688673876403)
          ·
            refine ⟨68024833042216033010814605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45349888694810688673876403 68024833042216033010814605)
            ·
              refine ⟨25509312390831012379055477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68024833042216033010814605 25509312390831012379055477)
              ·
                refine ⟨2391498036640407410536451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25509312390831012379055477 2391498036640407410536451)
                ·
                  refine ⟨3587247054960611115804677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2391498036640407410536451 3587247054960611115804677)
                  ·
                    refine ⟨672608822805114584213377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3587247054960611115804677 672608822805114584213377)
                    ·
                      rfl

theorem cell23_3929703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_3929703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929703 prefixEnd_3929703 := by exact prefixLift 3929703
  have htrace : WordTrace (prefixWord ++ tailWord_3929703) baseStart_3929703 baseEnd_3929703 := by
    simpa [prefixWord, tailWord_3929703, baseEnd_3929703] using wordTrace_append hprefix tailTrace_3929703
  have hstable : (prefixWord ++ tailWord_3929703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929703).length < 2 ^ (prefixWord ++ tailWord_3929703).sum := by decide
  have hdescent : baseEnd_3929703 < baseStart_3929703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929749 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_3929749 : Nat := 118140960795 + 3929749 * 2 ^ 59
def prefixEnd_3929749 : Nat := 4983230072969 + 3 ^ 40 * 3929749 * 2
def baseEnd_3929749 : Nat := 2017850088525450572664919

theorem tailTrace_3929749 : CollatzResearch.WordTrace tailWord_3929749 prefixEnd_3929749 2017850088525450572664919 := by
  unfold tailWord_3929749
  simp only [CollatzResearch.WordTrace]
  refine ⟨143329721040197995541512301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95553147360131997027674867 143329721040197995541512301)
  ·
    refine ⟨53748645390074248328067113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143329721040197995541512301 53748645390074248328067113)
    ·
      refine ⟨40311484042555686246050335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53748645390074248328067113 40311484042555686246050335)
      ·
        refine ⟨60467226063833529369075503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40311484042555686246050335 60467226063833529369075503)
        ·
          refine ⟨90700839095750294053613255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60467226063833529369075503 90700839095750294053613255)
          ·
            refine ⟨136051258643625441080419883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90700839095750294053613255 136051258643625441080419883)
            ·
              refine ⟨204076887965438161620629825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136051258643625441080419883 204076887965438161620629825)
              ·
                refine ⟨153057665974078621215472369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204076887965438161620629825 153057665974078621215472369)
                ·
                  refine ⟨114793249480558965911604277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153057665974078621215472369 114793249480558965911604277)
                  ·
                    refine ⟨10761867138802403054212901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114793249480558965911604277 10761867138802403054212901)
                    ·
                      refine ⟨2017850088525450572664919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10761867138802403054212901 2017850088525450572664919)
                      ·
                        rfl

theorem cell23_3929749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_3929749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929749 prefixEnd_3929749 := by exact prefixLift 3929749
  have htrace : WordTrace (prefixWord ++ tailWord_3929749) baseStart_3929749 baseEnd_3929749 := by
    simpa [prefixWord, tailWord_3929749, baseEnd_3929749] using wordTrace_append hprefix tailTrace_3929749
  have hstable : (prefixWord ++ tailWord_3929749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929749).length < 2 ^ (prefixWord ++ tailWord_3929749).sum := by decide
  have hdescent : baseEnd_3929749 < baseStart_3929749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929776 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 4, 4]
def baseStart_3929776 : Nat := 118140960795 + 3929776 * 2 ^ 59
def prefixEnd_3929776 : Nat := 4983230072969 + 3 ^ 40 * 3929776 * 2
def baseEnd_3929776 : Nat := 672621317501040655675765

theorem tailTrace_3929776 : CollatzResearch.WordTrace tailWord_3929776 prefixEnd_3929776 672621317501040655675765 := by
  unfold tailWord_3929776
  simp only [CollatzResearch.WordTrace]
  refine ⟨71665352905550089576372591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95553803874066786101830121 71665352905550089576372591)
  ·
    refine ⟨107498029358325134364558887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71665352905550089576372591 107498029358325134364558887)
    ·
      refine ⟨161247044037487701546838331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107498029358325134364558887 161247044037487701546838331)
      ·
        refine ⟨241870566056231552320257497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161247044037487701546838331 241870566056231552320257497)
        ·
          refine ⟨181402924542173664240193123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241870566056231552320257497 181402924542173664240193123)
          ·
            refine ⟨272104386813260496360289685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181402924542173664240193123 272104386813260496360289685)
            ·
              refine ⟨12754893131871585766888579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 272104386813260496360289685 12754893131871585766888579)
              ·
                refine ⟨19132339697807378650332869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12754893131871585766888579 19132339697807378650332869)
                ·
                  refine ⟨3587313693338883496937413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19132339697807378650332869 3587313693338883496937413)
                  ·
                    refine ⟨672621317501040655675765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3587313693338883496937413 672621317501040655675765)
                    ·
                      rfl

theorem cell23_3929776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 4, 4].length) (baseStart_3929776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929776 prefixEnd_3929776 := by exact prefixLift 3929776
  have htrace : WordTrace (prefixWord ++ tailWord_3929776) baseStart_3929776 baseEnd_3929776 := by
    simpa [prefixWord, tailWord_3929776, baseEnd_3929776] using wordTrace_append hprefix tailTrace_3929776
  have hstable : (prefixWord ++ tailWord_3929776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929776).length < 2 ^ (prefixWord ++ tailWord_3929776).sum := by decide
  have hdescent : baseEnd_3929776 < baseStart_3929776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929779 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 6]
def baseStart_3929779 : Nat := 118140960795 + 3929779 * 2 ^ 59
def prefixEnd_3929779 : Nat := 4983230072969 + 3 ^ 40 * 3929779 * 2
def baseEnd_3929779 : Nat := 2017865492945085455289781

theorem tailTrace_3929779 : CollatzResearch.WordTrace tailWord_3929779 prefixEnd_3929779 2017865492945085455289781 := by
  unfold tailWord_3929779
  simp only [CollatzResearch.WordTrace]
  refine ⟨143330815230089310665104391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95553876820059540443402927 143330815230089310665104391)
  ·
    refine ⟨214996222845133965997656587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143330815230089310665104391 214996222845133965997656587)
    ·
      refine ⟨322494334267700948996484881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214996222845133965997656587 322494334267700948996484881)
      ·
        refine ⟨241870750700775711747363661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322494334267700948996484881 241870750700775711747363661)
        ·
          refine ⟨90701531512790891905261373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241870750700775711747363661 90701531512790891905261373)
          ·
            refine ⟨34013074317296584464473015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90701531512790891905261373 34013074317296584464473015)
            ·
              refine ⟨51019611475944876696709523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34013074317296584464473015 51019611475944876696709523)
              ·
                refine ⟨76529417213917315045064285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51019611475944876696709523 76529417213917315045064285)
                ·
                  refine ⟨28698531455218993141899107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76529417213917315045064285 28698531455218993141899107)
                  ·
                    refine ⟨43047797182828489712848661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28698531455218993141899107 43047797182828489712848661)
                    ·
                      refine ⟨2017865492945085455289781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43047797182828489712848661 2017865492945085455289781)
                      ·
                        rfl

theorem cell23_3929779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_3929779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929779 prefixEnd_3929779 := by exact prefixLift 3929779
  have htrace : WordTrace (prefixWord ++ tailWord_3929779) baseStart_3929779 baseEnd_3929779 := by
    simpa [prefixWord, tailWord_3929779, baseEnd_3929779] using wordTrace_append hprefix tailTrace_3929779
  have hstable : (prefixWord ++ tailWord_3929779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929779).length < 2 ^ (prefixWord ++ tailWord_3929779).sum := by decide
  have hdescent : baseEnd_3929779 < baseStart_3929779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929786 : List Nat := [3, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5]
def baseStart_3929786 : Nat := 118140960795 + 3929786 * 2 ^ 59
def prefixEnd_3929786 : Nat := 4983230072969 + 3 ^ 40 * 3929786 * 2
def baseEnd_3929786 : Nat := 2017869087309666927902249

theorem tailTrace_3929786 : CollatzResearch.WordTrace tailWord_3929786 prefixEnd_3929786 2017869087309666927902249 := by
  unfold tailWord_3929786
  simp only [CollatzResearch.WordTrace]
  refine ⟨35832767635265987715152303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95554047027375967240406141 35832767635265987715152303)
  ·
    refine ⟨53749151452898981572728455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35832767635265987715152303 53749151452898981572728455)
    ·
      refine ⟨80623727179348472359092683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53749151452898981572728455 80623727179348472359092683)
      ·
        refine ⟨120935590769022708538639025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80623727179348472359092683 120935590769022708538639025)
        ·
          refine ⟨90701693076767031403979269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120935590769022708538639025 90701693076767031403979269)
          ·
            refine ⟨17006567451893818388246113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90701693076767031403979269 17006567451893818388246113)
            ·
              refine ⟨12754925588920363791184585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17006567451893818388246113 12754925588920363791184585)
              ·
                refine ⟨9566194191690272843388439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12754925588920363791184585 9566194191690272843388439)
                ·
                  refine ⟨14349291287535409265082659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9566194191690272843388439 14349291287535409265082659)
                  ·
                    refine ⟨21523936931303113897623989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14349291287535409265082659 21523936931303113897623989)
                    ·
                      refine ⟨2017869087309666927902249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21523936931303113897623989 2017869087309666927902249)
                      ·
                        rfl

theorem cell23_3929786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_3929786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929786 prefixEnd_3929786 := by exact prefixLift 3929786
  have htrace : WordTrace (prefixWord ++ tailWord_3929786) baseStart_3929786 baseEnd_3929786 := by
    simpa [prefixWord, tailWord_3929786, baseEnd_3929786] using wordTrace_append hprefix tailTrace_3929786
  have hstable : (prefixWord ++ tailWord_3929786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929786).length < 2 ^ (prefixWord ++ tailWord_3929786).sum := by decide
  have hdescent : baseEnd_3929786 < baseStart_3929786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929796 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_3929796 : Nat := 118140960795 + 3929796 * 2 ^ 59
def prefixEnd_3929796 : Nat := 4983230072969 + 3 ^ 40 * 3929796 * 2
def baseEnd_3929796 : Nat := 2017874222116211888777203

theorem tailTrace_3929796 : CollatzResearch.WordTrace tailWord_3929796 prefixEnd_3929796 2017874222116211888777203 := by
  unfold tailWord_3929796
  simp only [CollatzResearch.WordTrace]
  refine ⟨71665717635513861284236621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95554290180685148378982161 71665717635513861284236621)
  ·
    refine ⟨26874644113317697981588733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71665717635513861284236621 26874644113317697981588733)
    ·
      refine ⟨10077991542494136743095775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26874644113317697981588733 10077991542494136743095775)
      ·
        refine ⟨15116987313741205114643663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10077991542494136743095775 15116987313741205114643663)
        ·
          refine ⟨22675480970611807671965495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15116987313741205114643663 22675480970611807671965495)
          ·
            refine ⟨34013221455917711507948243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22675480970611807671965495 34013221455917711507948243)
            ·
              refine ⟨51019832183876567261922365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34013221455917711507948243 51019832183876567261922365)
              ·
                refine ⟨19132437068953712723220887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51019832183876567261922365 19132437068953712723220887)
                ·
                  refine ⟨28698655603430569084831331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19132437068953712723220887 28698655603430569084831331)
                  ·
                    refine ⟨43047983405145853627246997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28698655603430569084831331 43047983405145853627246997)
                    ·
                      refine ⟨2017874222116211888777203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 43047983405145853627246997 2017874222116211888777203)
                      ·
                        rfl

theorem cell23_3929796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_3929796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929796 prefixEnd_3929796 := by exact prefixLift 3929796
  have htrace : WordTrace (prefixWord ++ tailWord_3929796) baseStart_3929796 baseEnd_3929796 := by
    simpa [prefixWord, tailWord_3929796, baseEnd_3929796] using wordTrace_append hprefix tailTrace_3929796
  have hstable : (prefixWord ++ tailWord_3929796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929796).length < 2 ^ (prefixWord ++ tailWord_3929796).sum := by decide
  have hdescent : baseEnd_3929796 < baseStart_3929796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929814 : List Nat := [5, 2, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_3929814 : Nat := 118140960795 + 3929814 * 2 ^ 59
def prefixEnd_3929814 : Nat := 4983230072969 + 3 ^ 40 * 3929814 * 2
def baseEnd_3929814 : Nat := 672627821589330939450707

theorem tailTrace_3929814 : CollatzResearch.WordTrace tailWord_3929814 prefixEnd_3929814 672627821589330939450707 := by
  unfold tailWord_3929814
  simp only [CollatzResearch.WordTrace]
  refine ⟨8958255736560156977664281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95554727856641674428418997 8958255736560156977664281)
  ·
    refine ⟨6718691802420117733248211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8958255736560156977664281 6718691802420117733248211)
    ·
      refine ⟨10078037703630176599872317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6718691802420117733248211 10078037703630176599872317)
      ·
        refine ⟨3779264138861316224952119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10078037703630176599872317 3779264138861316224952119)
        ·
          refine ⟨5668896208291974337428179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3779264138861316224952119 5668896208291974337428179)
          ·
            refine ⟨8503344312437961506142269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5668896208291974337428179 8503344312437961506142269)
            ·
              refine ⟨3188754117164235564803351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8503344312437961506142269 3188754117164235564803351)
              ·
                refine ⟨4783131175746353347205027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3188754117164235564803351 4783131175746353347205027)
                ·
                  refine ⟨7174696763619530020807541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4783131175746353347205027 7174696763619530020807541)
                  ·
                    refine ⟨672627821589330939450707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7174696763619530020807541 672627821589330939450707)
                    ·
                      rfl

theorem cell23_3929814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_3929814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929814 prefixEnd_3929814 := by exact prefixLift 3929814
  have htrace : WordTrace (prefixWord ++ tailWord_3929814) baseStart_3929814 baseEnd_3929814 := by
    simpa [prefixWord, tailWord_3929814, baseEnd_3929814] using wordTrace_append hprefix tailTrace_3929814
  have hstable : (prefixWord ++ tailWord_3929814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929814).length < 2 ^ (prefixWord ++ tailWord_3929814).sum := by decide
  have hdescent : baseEnd_3929814 < baseStart_3929814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929834 : List Nat := [3, 1, 3, 1, 1, 1, 6, 2, 1, 2, 2]
def baseStart_3929834 : Nat := 118140960795 + 3929834 * 2 ^ 59
def prefixEnd_3929834 : Nat := 4983230072969 + 3 ^ 40 * 3929834 * 2
def baseEnd_3929834 : Nat := 2017893734381082740102029

theorem tailTrace_3929834 : CollatzResearch.WordTrace tailWord_3929834 prefixEnd_3929834 2017893734381082740102029 := by
  unfold tailWord_3929834
  simp only [CollatzResearch.WordTrace]
  refine ⟨35833205311222513764589139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95555214163260036705571037 35833205311222513764589139)
  ·
    refine ⟨53749807966833770646883709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35833205311222513764589139 53749807966833770646883709)
    ·
      refine ⟨20156177987562663992581391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53749807966833770646883709 20156177987562663992581391)
      ·
        refine ⟨30234266981343995988872087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20156177987562663992581391 30234266981343995988872087)
        ·
          refine ⟨45351400472015993983308131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30234266981343995988872087 45351400472015993983308131)
          ·
            refine ⟨68027100708023990974962197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45351400472015993983308131 68027100708023990974962197)
            ·
              refine ⟨3188770345688624576951353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68027100708023990974962197 3188770345688624576951353)
              ·
                refine ⟨2391577759266468432713515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3188770345688624576951353 2391577759266468432713515)
                ·
                  refine ⟨3587366638899702649070273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2391577759266468432713515 3587366638899702649070273)
                  ·
                    refine ⟨2690524979174776986802705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3587366638899702649070273 2690524979174776986802705)
                    ·
                      refine ⟨2017893734381082740102029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2690524979174776986802705 2017893734381082740102029)
                      ·
                        rfl

theorem cell23_3929834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_3929834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929834 prefixEnd_3929834 := by exact prefixLift 3929834
  have htrace : WordTrace (prefixWord ++ tailWord_3929834) baseStart_3929834 baseEnd_3929834 := by
    simpa [prefixWord, tailWord_3929834, baseEnd_3929834] using wordTrace_append hprefix tailTrace_3929834
  have hstable : (prefixWord ++ tailWord_3929834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929834).length < 2 ^ (prefixWord ++ tailWord_3929834).sum := by decide
  have hdescent : baseEnd_3929834 < baseStart_3929834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929843 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 3, 3, 2]
def baseStart_3929843 : Nat := 118140960795 + 3929843 * 2 ^ 59
def prefixEnd_3929843 : Nat := 4983230072969 + 3 ^ 40 * 3929843 * 2
def baseEnd_3929843 : Nat := 2017898355706973204889487

theorem tailTrace_3929843 : CollatzResearch.WordTrace tailWord_3929843 prefixEnd_3929843 2017898355706973204889487 := by
  unfold tailWord_3929843
  simp only [CollatzResearch.WordTrace]
  refine ⟨143333149501857449595434183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95555433001238299730289455 143333149501857449595434183)
  ·
    refine ⟨214999724252786174393151275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143333149501857449595434183 214999724252786174393151275)
    ·
      refine ⟨322499586379179261589726913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214999724252786174393151275 322499586379179261589726913)
      ·
        refine ⟨241874689784384446192295185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322499586379179261589726913 241874689784384446192295185)
        ·
          refine ⟨181406017338288334644221389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241874689784384446192295185 181406017338288334644221389)
          ·
            refine ⟨68027256501858125491583021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181406017338288334644221389 68027256501858125491583021)
            ·
              refine ⟨25510221188196797059343633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68027256501858125491583021 25510221188196797059343633)
              ·
                refine ⟨19132665891147597794507725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25510221188196797059343633 19132665891147597794507725)
                ·
                  refine ⟨7174749709180349172940397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19132665891147597794507725 7174749709180349172940397)
                  ·
                    refine ⟨2690531140942630939852649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7174749709180349172940397 2690531140942630939852649)
                    ·
                      refine ⟨2017898355706973204889487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2690531140942630939852649 2017898355706973204889487)
                      ·
                        rfl

theorem cell23_3929843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 3, 2].length) (baseStart_3929843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929843 prefixEnd_3929843 := by exact prefixLift 3929843
  have htrace : WordTrace (prefixWord ++ tailWord_3929843) baseStart_3929843 baseEnd_3929843 := by
    simpa [prefixWord, tailWord_3929843, baseEnd_3929843] using wordTrace_append hprefix tailTrace_3929843
  have hstable : (prefixWord ++ tailWord_3929843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929843).length < 2 ^ (prefixWord ++ tailWord_3929843).sum := by decide
  have hdescent : baseEnd_3929843 < baseStart_3929843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929860 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 3, 3, 2]
def baseStart_3929860 : Nat := 118140960795 + 3929860 * 2 ^ 59
def prefixEnd_3929860 : Nat := 4983230072969 + 3 ^ 40 * 3929860 * 2
def baseEnd_3929860 : Nat := 2017907084878099638376909

theorem tailTrace_3929860 : CollatzResearch.WordTrace tailWord_3929860 prefixEnd_3929860 2017907084878099638376909 := by
  unfold tailWord_3929860
  simp only [CollatzResearch.WordTrace]
  refine ⟨71666884771397930749401517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95555846361863907665868689 71666884771397930749401517)
  ·
    refine ⟨26875081789274224031025569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71666884771397930749401517 26875081789274224031025569)
    ·
      refine ⟨20156311341955668023269177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26875081789274224031025569 20156311341955668023269177)
      ·
        refine ⟨15117233506466751017451883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20156311341955668023269177 15117233506466751017451883)
        ·
          refine ⟨22675850259700126526177825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15117233506466751017451883 22675850259700126526177825)
          ·
            refine ⟨17006887694775094894633369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22675850259700126526177825 17006887694775094894633369)
            ·
              refine ⟨12755165771081321170975027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17006887694775094894633369 12755165771081321170975027)
              ·
                refine ⟨19132748656621981756462541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12755165771081321170975027 19132748656621981756462541)
                ·
                  refine ⟨7174780746233243158673453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19132748656621981756462541 7174780746233243158673453)
                  ·
                    refine ⟨2690542779837466184502545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7174780746233243158673453 2690542779837466184502545)
                    ·
                      refine ⟨2017907084878099638376909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2690542779837466184502545 2017907084878099638376909)
                      ·
                        rfl

theorem cell23_3929860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_3929860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929860 prefixEnd_3929860 := by exact prefixLift 3929860
  have htrace : WordTrace (prefixWord ++ tailWord_3929860) baseStart_3929860 baseEnd_3929860 := by
    simpa [prefixWord, tailWord_3929860, baseEnd_3929860] using wordTrace_append hprefix tailTrace_3929860
  have hstable : (prefixWord ++ tailWord_3929860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929860).length < 2 ^ (prefixWord ++ tailWord_3929860).sum := by decide
  have hdescent : baseEnd_3929860 < baseStart_3929860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929877 : List Nat := [1, 3, 2, 1, 2, 3, 4, 1, 1, 3, 2]
def baseStart_3929877 : Nat := 118140960795 + 3929877 * 2 ^ 59
def prefixEnd_3929877 : Nat := 4983230072969 + 3 ^ 40 * 3929877 * 2
def baseEnd_3929877 : Nat := 2017915814049226071864331

theorem tailTrace_3929877 : CollatzResearch.WordTrace tailWord_3929877 prefixEnd_3929877 2017915814049226071864331 := by
  unfold tailWord_3929877
  simp only [CollatzResearch.WordTrace]
  refine ⟨143334389583734273402171885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95556259722489515601447923 143334389583734273402171885)
  ·
    refine ⟨53750396093900352525814457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143334389583734273402171885 53750396093900352525814457)
    ·
      refine ⟨40312797070425264394360843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53750396093900352525814457 40312797070425264394360843)
      ·
        refine ⟨60469195605637896591541265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40312797070425264394360843 60469195605637896591541265)
        ·
          refine ⟨45351896704228422443655949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60469195605637896591541265 45351896704228422443655949)
          ·
            refine ⟨17006961264085658416370981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45351896704228422443655949 17006961264085658416370981)
            ·
              refine ⟨3188805237016060953069559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17006961264085658416370981 3188805237016060953069559)
              ·
                refine ⟨4783207855524091429604339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3188805237016060953069559 4783207855524091429604339)
                ·
                  refine ⟨7174811783286137144406509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4783207855524091429604339 7174811783286137144406509)
                  ·
                    refine ⟨2690554418732301429152441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7174811783286137144406509 2690554418732301429152441)
                    ·
                      refine ⟨2017915814049226071864331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2690554418732301429152441 2017915814049226071864331)
                      ·
                        rfl

theorem cell23_3929877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_3929877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929877 prefixEnd_3929877 := by exact prefixLift 3929877
  have htrace : WordTrace (prefixWord ++ tailWord_3929877) baseStart_3929877 baseEnd_3929877 := by
    simpa [prefixWord, tailWord_3929877, baseEnd_3929877] using wordTrace_append hprefix tailTrace_3929877
  have hstable : (prefixWord ++ tailWord_3929877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929877).length < 2 ^ (prefixWord ++ tailWord_3929877).sum := by decide
  have hdescent : baseEnd_3929877 < baseStart_3929877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929907 : List Nat := [1, 1, 1, 2, 7, 2, 1, 1, 1, 4, 2]
def baseStart_3929907 : Nat := 118140960795 + 3929907 * 2 ^ 59
def prefixEnd_3929907 : Nat := 4983230072969 + 3 ^ 40 * 3929907 * 2
def baseEnd_3929907 : Nat := 2017931218468860954489193

theorem tailTrace_3929907 : CollatzResearch.WordTrace tailWord_3929907 prefixEnd_3929907 2017931218468860954489193 := by
  unfold tailWord_3929907
  simp only [CollatzResearch.WordTrace]
  refine ⟨143335483773625588525763975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95556989182417059017175983 143335483773625588525763975)
  ·
    refine ⟨215003225660438382788645963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143335483773625588525763975 215003225660438382788645963)
    ·
      refine ⟨322504838490657574182968945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215003225660438382788645963 322504838490657574182968945)
      ·
        refine ⟨241878628867993180637226709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322504838490657574182968945 241878628867993180637226709)
        ·
          refine ⟨5669030364093590171185001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 241878628867993180637226709 5669030364093590171185001)
          ·
            refine ⟨4251772773070192628388751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5669030364093590171185001 4251772773070192628388751)
            ·
              refine ⟨6377659159605288942583127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4251772773070192628388751 6377659159605288942583127)
              ·
                refine ⟨9566488739407933413874691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6377659159605288942583127 9566488739407933413874691)
                ·
                  refine ⟨14349733109111900120812037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9566488739407933413874691 14349733109111900120812037)
                  ·
                    refine ⟨2690574957958481272652257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14349733109111900120812037 2690574957958481272652257)
                    ·
                      refine ⟨2017931218468860954489193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2690574957958481272652257 2017931218468860954489193)
                      ·
                        rfl

theorem cell23_3929907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 4, 2].length) (baseStart_3929907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929907 prefixEnd_3929907 := by exact prefixLift 3929907
  have htrace : WordTrace (prefixWord ++ tailWord_3929907) baseStart_3929907 baseEnd_3929907 := by
    simpa [prefixWord, tailWord_3929907, baseEnd_3929907] using wordTrace_append hprefix tailTrace_3929907
  have hstable : (prefixWord ++ tailWord_3929907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929907).length < 2 ^ (prefixWord ++ tailWord_3929907).sum := by decide
  have hdescent : baseEnd_3929907 < baseStart_3929907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929936 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 5]
def baseStart_3929936 : Nat := 118140960795 + 3929936 * 2 ^ 59
def prefixEnd_3929936 : Nat := 4983230072969 + 3 ^ 40 * 3929936 * 2
def baseEnd_3929936 : Nat := 2017946109407841341026559

theorem tailTrace_3929936 : CollatzResearch.WordTrace tailWord_3929936 prefixEnd_3929936 2017946109407841341026559 := by
  unfold tailWord_3929936
  simp only [CollatzResearch.WordTrace]
  refine ⟨71668270745260263239284831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95557694327013684319046441 71668270745260263239284831)
  ·
    refine ⟨107502406117890394858927247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71668270745260263239284831 107502406117890394858927247)
    ·
      refine ⟨161253609176835592288390871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107502406117890394858927247 161253609176835592288390871)
      ·
        refine ⟨241880413765253388432586307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161253609176835592288390871 241880413765253388432586307)
        ·
          refine ⟨362820620647880082648879461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241880413765253388432586307 362820620647880082648879461)
          ·
            refine ⟨68028866371477515496664899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 362820620647880082648879461 68028866371477515496664899)
            ·
              refine ⟨102043299557216273244997349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68028866371477515496664899 102043299557216273244997349)
              ·
                refine ⟨19133118666978051233437003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102043299557216273244997349 19133118666978051233437003)
                ·
                  refine ⟨28699678000467076850155505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19133118666978051233437003 28699678000467076850155505)
                  ·
                    refine ⟨21524758500350307637616629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28699678000467076850155505 21524758500350307637616629)
                    ·
                      refine ⟨2017946109407841341026559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21524758500350307637616629 2017946109407841341026559)
                      ·
                        rfl

theorem cell23_3929936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_3929936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929936 prefixEnd_3929936 := by exact prefixLift 3929936
  have htrace : WordTrace (prefixWord ++ tailWord_3929936) baseStart_3929936 baseEnd_3929936 := by
    simpa [prefixWord, tailWord_3929936, baseEnd_3929936] using wordTrace_append hprefix tailTrace_3929936
  have hstable : (prefixWord ++ tailWord_3929936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929936).length < 2 ^ (prefixWord ++ tailWord_3929936).sum := by decide
  have hdescent : baseEnd_3929936 < baseStart_3929936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3929963 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 1, 6, 2]
def baseStart_3929963 : Nat := 118140960795 + 3929963 * 2 ^ 59
def prefixEnd_3929963 : Nat := 4983230072969 + 3 ^ 40 * 3929963 * 2
def baseEnd_3929963 : Nat := 2017959973385512735388935

theorem tailTrace_3929963 : CollatzResearch.WordTrace tailWord_3929963 prefixEnd_3929963 2017959973385512735388935 := by
  unfold tailWord_3929963
  simp only [CollatzResearch.WordTrace]
  refine ⟨143337526261422710089802543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95558350840948473393201695 143337526261422710089802543)
  ·
    refine ⟨215006289392134065134703815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143337526261422710089802543 215006289392134065134703815)
    ·
      refine ⟨322509434088201097702055723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215006289392134065134703815 322509434088201097702055723)
      ·
        refine ⟨483764151132301646553083585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322509434088201097702055723 483764151132301646553083585)
        ·
          refine ⟨362823113349226234914812689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483764151132301646553083585 362823113349226234914812689)
          ·
            refine ⟨272117335011919676186109517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362823113349226234914812689 272117335011919676186109517)
            ·
              refine ⟨102044000629469878569791069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272117335011919676186109517 102044000629469878569791069)
              ·
                refine ⟨38266500236051204463671651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102044000629469878569791069 38266500236051204463671651)
                ·
                  refine ⟨57399750354076806695507477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38266500236051204463671651 57399750354076806695507477)
                  ·
                    refine ⟨2690613297847350313851913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57399750354076806695507477 2690613297847350313851913)
                    ·
                      refine ⟨2017959973385512735388935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2690613297847350313851913 2017959973385512735388935)
                      ·
                        rfl

theorem cell23_3929963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 6, 2].length) (baseStart_3929963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3929963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3929963 prefixEnd_3929963 := by exact prefixLift 3929963
  have htrace : WordTrace (prefixWord ++ tailWord_3929963) baseStart_3929963 baseEnd_3929963 := by
    simpa [prefixWord, tailWord_3929963, baseEnd_3929963] using wordTrace_append hprefix tailTrace_3929963
  have hstable : (prefixWord ++ tailWord_3929963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3929963).length < 2 ^ (prefixWord ++ tailWord_3929963).sum := by decide
  have hdescent : baseEnd_3929963 < baseStart_3929963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3929963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930007 : List Nat := [1, 1, 3, 3, 1, 4, 1, 4, 1, 4]
def baseStart_3930007 : Nat := 118140960795 + 3930007 * 2 ^ 59
def prefixEnd_3930007 : Nat := 4983230072969 + 3 ^ 40 * 3930007 * 2
def baseEnd_3930007 : Nat := 672660855511436854412911

theorem tailTrace_3930007 : CollatzResearch.WordTrace tailWord_3930007 prefixEnd_3930007 672660855511436854412911 := by
  unfold tailWord_3930007
  simp only [CollatzResearch.WordTrace]
  refine ⟨143339131073263305604404275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95559420715508870402936183 143339131073263305604404275)
  ·
    refine ⟨215008696609894958406606413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143339131073263305604404275 215008696609894958406606413)
    ·
      refine ⟨80628261228710609402477405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215008696609894958406606413 80628261228710609402477405)
      ·
        refine ⟨30235597960766478525929027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80628261228710609402477405 30235597960766478525929027)
        ·
          refine ⟨45353396941149717788893541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30235597960766478525929027 45353396941149717788893541)
          ·
            refine ⟨8503761926465572085417539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45353396941149717788893541 8503761926465572085417539)
            ·
              refine ⟨12755642889698358128126309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8503761926465572085417539 12755642889698358128126309)
              ·
                refine ⟨2391683041818442149023683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12755642889698358128126309 2391683041818442149023683)
                ·
                  refine ⟨3587524562727663223535525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2391683041818442149023683 3587524562727663223535525)
                  ·
                    refine ⟨672660855511436854412911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3587524562727663223535525 672660855511436854412911)
                    ·
                      rfl

theorem cell23_3930007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 1, 4].length) (baseStart_3930007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930007 prefixEnd_3930007 := by exact prefixLift 3930007
  have htrace : WordTrace (prefixWord ++ tailWord_3930007) baseStart_3930007 baseEnd_3930007 := by
    simpa [prefixWord, tailWord_3930007, baseEnd_3930007] using wordTrace_append hprefix tailTrace_3930007
  have hstable : (prefixWord ++ tailWord_3930007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930007).length < 2 ^ (prefixWord ++ tailWord_3930007).sum := by decide
  have hdescent : baseEnd_3930007 < baseStart_3930007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930024 : List Nat := [2, 1, 6, 2, 1, 1, 1, 2, 3, 4]
def baseStart_3930024 : Nat := 118140960795 + 3930024 * 2 ^ 59
def prefixEnd_3930024 : Nat := 4983230072969 + 3 ^ 40 * 3930024 * 2
def baseEnd_3930024 : Nat := 672663765235145665575385

theorem tailTrace_3930024 : CollatzResearch.WordTrace tailWord_3930024 prefixEnd_3930024 672663765235145665575385 := by
  unfold tailWord_3930024
  simp only [CollatzResearch.WordTrace]
  refine ⟨71669875557100858753886563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95559834076134478338515417 71669875557100858753886563)
  ·
    refine ⟨107504813335651288130829845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71669875557100858753886563 107504813335651288130829845)
    ·
      refine ⟨5039288125108654131132649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107504813335651288130829845 5039288125108654131132649)
      ·
        refine ⟨3779466093831490598349487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5039288125108654131132649 3779466093831490598349487)
        ·
          refine ⟨5669199140747235897524231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3779466093831490598349487 5669199140747235897524231)
          ·
            refine ⟨8503798711120853846286347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5669199140747235897524231 8503798711120853846286347)
            ·
              refine ⟨12755698066681280769429521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8503798711120853846286347 12755698066681280769429521)
              ·
                refine ⟨9566773550010960577072141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12755698066681280769429521 9566773550010960577072141)
                ·
                  refine ⟨3587540081254110216402053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9566773550010960577072141 3587540081254110216402053)
                  ·
                    refine ⟨672663765235145665575385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3587540081254110216402053 672663765235145665575385)
                    ·
                      rfl

theorem cell23_3930024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_3930024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930024 prefixEnd_3930024 := by exact prefixLift 3930024
  have htrace : WordTrace (prefixWord ++ tailWord_3930024) baseStart_3930024 baseEnd_3930024 := by
    simpa [prefixWord, tailWord_3930024, baseEnd_3930024] using wordTrace_append hprefix tailTrace_3930024
  have hstable : (prefixWord ++ tailWord_3930024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930024).length < 2 ^ (prefixWord ++ tailWord_3930024).sum := by decide
  have hdescent : baseEnd_3930024 < baseStart_3930024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930040 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 1, 5, 2]
def baseStart_3930040 : Nat := 118140960795 + 3930040 * 2 ^ 59
def prefixEnd_3930040 : Nat := 4983230072969 + 3 ^ 40 * 3930040 * 2
def baseEnd_3930040 : Nat := 2017999511395908934126081

theorem tailTrace_3930040 : CollatzResearch.WordTrace tailWord_3930040 prefixEnd_3930040 2017999511395908934126081 := by
  unfold tailWord_3930040
  simp only [CollatzResearch.WordTrace]
  refine ⟨71670167341071876120177787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95560223121429168160237049 71670167341071876120177787)
  ·
    refine ⟨107505251011607814180266681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71670167341071876120177787 107505251011607814180266681)
    ·
      refine ⟨80628938258705860635200011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107505251011607814180266681 80628938258705860635200011)
      ·
        refine ⟨120943407388058790952800017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80628938258705860635200011 120943407388058790952800017)
        ·
          refine ⟨90707555541044093214600013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120943407388058790952800017 90707555541044093214600013)
          ·
            refine ⟨34015333327891534955475005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90707555541044093214600013 34015333327891534955475005)
            ·
              refine ⟨12755749997959325608303127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34015333327891534955475005 12755749997959325608303127)
              ·
                refine ⟨19133624996938988412454691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12755749997959325608303127 19133624996938988412454691)
                ·
                  refine ⟨28700437495408482618682037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19133624996938988412454691 28700437495408482618682037)
                  ·
                    refine ⟨2690666015194545245501441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28700437495408482618682037 2690666015194545245501441)
                    ·
                      refine ⟨2017999511395908934126081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2690666015194545245501441 2017999511395908934126081)
                      ·
                        rfl

theorem cell23_3930040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 1, 5, 2].length) (baseStart_3930040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930040 prefixEnd_3930040 := by exact prefixLift 3930040
  have htrace : WordTrace (prefixWord ++ tailWord_3930040) baseStart_3930040 baseEnd_3930040 := by
    simpa [prefixWord, tailWord_3930040, baseEnd_3930040] using wordTrace_append hprefix tailTrace_3930040
  have hstable : (prefixWord ++ tailWord_3930040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930040).length < 2 ^ (prefixWord ++ tailWord_3930040).sum := by decide
  have hdescent : baseEnd_3930040 < baseStart_3930040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930053 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 5, 1, 4]
def baseStart_3930053 : Nat := 118140960795 + 3930053 * 2 ^ 59
def prefixEnd_3930053 : Nat := 4983230072969 + 3 ^ 40 * 3930053 * 2
def baseEnd_3930053 : Nat := 2018006186644417383263521

theorem tailTrace_3930053 : CollatzResearch.WordTrace tailWord_3930053 prefixEnd_3930053 2018006186644417383263521 := by
  unfold tailWord_3930053
  simp only [CollatzResearch.WordTrace]
  refine ⟨143340808831096655460578813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95560539220731103640385875 143340808831096655460578813)
  ·
    refine ⟨53752803311661245797717055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143340808831096655460578813 53752803311661245797717055)
    ·
      refine ⟨80629204967491868696575583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53752803311661245797717055 80629204967491868696575583)
      ·
        refine ⟨120943807451237803044863375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80629204967491868696575583 120943807451237803044863375)
        ·
          refine ⟨181415711176856704567295063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120943807451237803044863375 181415711176856704567295063)
          ·
            refine ⟨272123566765285056850942595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181415711176856704567295063 272123566765285056850942595)
            ·
              refine ⟨408185350147927585276413893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272123566765285056850942595 408185350147927585276413893)
              ·
                refine ⟨76534753152736422239327605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 408185350147927585276413893 76534753152736422239327605)
                ·
                  refine ⟨7175133108069039584936963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76534753152736422239327605 7175133108069039584936963)
                  ·
                    refine ⟨10762699662103559377405445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7175133108069039584936963 10762699662103559377405445)
                    ·
                      refine ⟨2018006186644417383263521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10762699662103559377405445 2018006186644417383263521)
                      ·
                        rfl

theorem cell23_3930053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_3930053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930053 prefixEnd_3930053 := by exact prefixLift 3930053
  have htrace : WordTrace (prefixWord ++ tailWord_3930053) baseStart_3930053 baseEnd_3930053 := by
    simpa [prefixWord, tailWord_3930053, baseEnd_3930053] using wordTrace_append hprefix tailTrace_3930053
  have hstable : (prefixWord ++ tailWord_3930053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930053).length < 2 ^ (prefixWord ++ tailWord_3930053).sum := by decide
  have hdescent : baseEnd_3930053 < baseStart_3930053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930080 : List Nat := [2, 1, 1, 3, 1, 1, 1, 7, 2, 4]
def baseStart_3930080 : Nat := 118140960795 + 3930080 * 2 ^ 59
def prefixEnd_3930080 : Nat := 4983230072969 + 3 ^ 40 * 3930080 * 2
def baseEnd_3930080 : Nat := 672673350207362925875299

theorem tailTrace_3930080 : CollatzResearch.WordTrace tailWord_3930080 prefixEnd_3930080 672673350207362925875299 := by
  unfold tailWord_3930080
  simp only [CollatzResearch.WordTrace]
  refine ⟨71670896800999419535905847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95561195734665892714541129 71670896800999419535905847)
  ·
    refine ⟨107506345201499129303858771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71670896800999419535905847 107506345201499129303858771)
    ·
      refine ⟨161259517802248693955788157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107506345201499129303858771 161259517802248693955788157)
      ·
        refine ⟨60472319175843260233420559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161259517802248693955788157 60472319175843260233420559)
        ·
          refine ⟨90708478763764890350130839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60472319175843260233420559 90708478763764890350130839)
          ·
            refine ⟨136062718145647335525196259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90708478763764890350130839 136062718145647335525196259)
            ·
              refine ⟨204094077218471003287794389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136062718145647335525196259 204094077218471003287794389)
              ·
                refine ⟨4783454934807914139557681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 204094077218471003287794389 4783454934807914139557681)
                ·
                  refine ⟨3587591201105935604668261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4783454934807914139557681 3587591201105935604668261)
                  ·
                    refine ⟨672673350207362925875299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3587591201105935604668261 672673350207362925875299)
                    ·
                      rfl

theorem cell23_3930080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 2, 4].length) (baseStart_3930080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930080 prefixEnd_3930080 := by exact prefixLift 3930080
  have htrace : WordTrace (prefixWord ++ tailWord_3930080) baseStart_3930080 baseEnd_3930080 := by
    simpa [prefixWord, tailWord_3930080, baseEnd_3930080] using wordTrace_append hprefix tailTrace_3930080
  have hstable : (prefixWord ++ tailWord_3930080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930080).length < 2 ^ (prefixWord ++ tailWord_3930080).sum := by decide
  have hdescent : baseEnd_3930080 < baseStart_3930080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930110 : List Nat := [4, 2, 2, 2, 1, 1, 11]
def baseStart_3930110 : Nat := 118140960795 + 3930110 * 2 ^ 59
def prefixEnd_3930110 : Nat := 4983230072969 + 3 ^ 40 * 3930110 * 2
def baseEnd_3930110 : Nat := 24914017963478069879639

theorem tailTrace_3930110 : CollatzResearch.WordTrace tailWord_3930110 prefixEnd_3930110 24914017963478069879639 := by
  unfold tailWord_3930110
  simp only [CollatzResearch.WordTrace]
  refine ⟨17917860973986269274425473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95561925194593436130269189 17917860973986269274425473)
  ·
    refine ⟨13438395730489701955819105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17917860973986269274425473 13438395730489701955819105)
    ·
      refine ⟨10078796797867276466864329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13438395730489701955819105 10078796797867276466864329)
      ·
        refine ⟨7559097598400457350148247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10078796797867276466864329 7559097598400457350148247)
        ·
          refine ⟨11338646397600686025222371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7559097598400457350148247 11338646397600686025222371)
          ·
            refine ⟨17007969596401029037833557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11338646397600686025222371 17007969596401029037833557)
            ·
              refine ⟨24914017963478069879639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17007969596401029037833557 24914017963478069879639)
              ·
                rfl

theorem cell23_3930110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 11].length) (baseStart_3930110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930110 prefixEnd_3930110 := by exact prefixLift 3930110
  have htrace : WordTrace (prefixWord ++ tailWord_3930110) baseStart_3930110 baseEnd_3930110 := by
    simpa [prefixWord, tailWord_3930110, baseEnd_3930110] using wordTrace_append hprefix tailTrace_3930110
  have hstable : (prefixWord ++ tailWord_3930110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930110).length < 2 ^ (prefixWord ++ tailWord_3930110).sum := by decide
  have hdescent : baseEnd_3930110 < baseStart_3930110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930123 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 2, 7]
def baseStart_3930123 : Nat := 118140960795 + 3930123 * 2 ^ 59
def prefixEnd_3930123 : Nat := 4983230072969 + 3 ^ 40 * 3930123 * 2
def baseEnd_3930123 : Nat := 672680710096744036462733

theorem tailTrace_3930123 : CollatzResearch.WordTrace tailWord_3930123 prefixEnd_3930123 672680710096744036462733 := by
  unfold tailWord_3930123
  simp only [CollatzResearch.WordTrace]
  refine ⟨143343361940843057415627023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95562241293895371610418015 143343361940843057415627023)
  ·
    refine ⟨215015042911264586123440535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143343361940843057415627023 215015042911264586123440535)
    ·
      refine ⟨322522564366896879185160803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215015042911264586123440535 322522564366896879185160803)
      ·
        refine ⟨483783846550345318777741205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322522564366896879185160803 483783846550345318777741205)
        ·
          refine ⟨22677367807047436817706619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 483783846550345318777741205 22677367807047436817706619)
          ·
            refine ⟨34016051710571155226559929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22677367807047436817706619 34016051710571155226559929)
            ·
              refine ⟨25512038782928366419919947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34016051710571155226559929 25512038782928366419919947)
              ·
                refine ⟨38268058174392549629879921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25512038782928366419919947 38268058174392549629879921)
                ·
                  refine ⟨28701043630794412222409941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38268058174392549629879921 28701043630794412222409941)
                  ·
                    refine ⟨672680710096744036462733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28701043630794412222409941 672680710096744036462733)
                    ·
                      rfl

theorem cell23_3930123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 7].length) (baseStart_3930123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930123 prefixEnd_3930123 := by exact prefixLift 3930123
  have htrace : WordTrace (prefixWord ++ tailWord_3930123) baseStart_3930123 baseEnd_3930123 := by
    simpa [prefixWord, tailWord_3930123, baseEnd_3930123] using wordTrace_append hprefix tailTrace_3930123
  have hstable : (prefixWord ++ tailWord_3930123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930123).length < 2 ^ (prefixWord ++ tailWord_3930123).sum := by decide
  have hdescent : baseEnd_3930123 < baseStart_3930123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930147 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 3, 3, 2]
def baseStart_3930147 : Nat := 118140960795 + 3930147 * 2 ^ 59
def prefixEnd_3930147 : Nat := 4983230072969 + 3 ^ 40 * 3930147 * 2
def baseEnd_3930147 : Nat := 2018054453825940015488089

theorem tailTrace_3930147 : CollatzResearch.WordTrace tailWord_3930147 prefixEnd_3930147 2018054453825940015488089 := by
  unfold tailWord_3930147
  simp only [CollatzResearch.WordTrace]
  refine ⟨143344237292756109514500695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95562824861837406343000463 143344237292756109514500695)
  ·
    refine ⟨215016355939134164271751043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143344237292756109514500695 215016355939134164271751043)
    ·
      refine ⟨322524533908701246407626565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215016355939134164271751043 322524533908701246407626565)
      ·
        refine ⟨60473350107881483701429981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322524533908701246407626565 60473350107881483701429981)
        ·
          refine ⟨22677506290455556388036243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60473350107881483701429981 22677506290455556388036243)
          ·
            refine ⟨34016259435683334582054365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22677506290455556388036243 34016259435683334582054365)
            ·
              refine ⟨12756097288381250468270387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34016259435683334582054365 12756097288381250468270387)
              ·
                refine ⟨19134145932571875702405581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12756097288381250468270387 19134145932571875702405581)
                ·
                  refine ⟨7175304724714453388402093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19134145932571875702405581 7175304724714453388402093)
                  ·
                    refine ⟨2690739271767920020650785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7175304724714453388402093 2690739271767920020650785)
                    ·
                      refine ⟨2018054453825940015488089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2690739271767920020650785 2018054453825940015488089)
                      ·
                        rfl

theorem cell23_3930147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_3930147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930147 prefixEnd_3930147 := by exact prefixLift 3930147
  have htrace : WordTrace (prefixWord ++ tailWord_3930147) baseStart_3930147 baseEnd_3930147 := by
    simpa [prefixWord, tailWord_3930147, baseEnd_3930147] using wordTrace_append hprefix tailTrace_3930147
  have hstable : (prefixWord ++ tailWord_3930147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930147).length < 2 ^ (prefixWord ++ tailWord_3930147).sum := by decide
  have hdescent : baseEnd_3930147 < baseStart_3930147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930190 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_3930190 : Nat := 118140960795 + 3930190 * 2 ^ 59
def prefixEnd_3930190 : Nat := 4983230072969 + 3 ^ 40 * 3930190 * 2
def baseEnd_3930190 : Nat := 2018076533494083347250391

theorem tailTrace_3930190 : CollatzResearch.WordTrace tailWord_3930190 prefixEnd_3930190 2018076533494083347250391 := by
  unfold tailWord_3930190
  simp only [CollatzResearch.WordTrace]
  refine ⟨17918225703950040982289503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95563870421066885238877349 17918225703950040982289503)
  ·
    refine ⟨26877338555925061473434255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17918225703950040982289503 26877338555925061473434255)
    ·
      refine ⟨40316007833887592210151383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26877338555925061473434255 40316007833887592210151383)
      ·
        refine ⟨60474011750831388315227075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40316007833887592210151383 60474011750831388315227075)
        ·
          refine ⟨90711017626247082472840613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60474011750831388315227075 90711017626247082472840613)
          ·
            refine ⟨17008315804921327963657615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90711017626247082472840613 17008315804921327963657615)
            ·
              refine ⟨25512473707381991945486423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17008315804921327963657615 25512473707381991945486423)
              ·
                refine ⟨38268710561072987918229635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25512473707381991945486423 38268710561072987918229635)
                ·
                  refine ⟨57403065841609481877344453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38268710561072987918229635 57403065841609481877344453)
                  ·
                    refine ⟨10763074845301777852002085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57403065841609481877344453 10763074845301777852002085)
                    ·
                      refine ⟨2018076533494083347250391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10763074845301777852002085 2018076533494083347250391)
                      ·
                        rfl

theorem cell23_3930190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_3930190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930190 prefixEnd_3930190 := by exact prefixLift 3930190
  have htrace : WordTrace (prefixWord ++ tailWord_3930190) baseStart_3930190 baseEnd_3930190 := by
    simpa [prefixWord, tailWord_3930190, baseEnd_3930190] using wordTrace_append hprefix tailTrace_3930190
  have hstable : (prefixWord ++ tailWord_3930190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930190).length < 2 ^ (prefixWord ++ tailWord_3930190).sum := by decide
  have hdescent : baseEnd_3930190 < baseStart_3930190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930200 : List Nat := [2, 1, 2, 2, 1, 5, 1, 2, 7]
def baseStart_3930200 : Nat := 118140960795 + 3930200 * 2 ^ 59
def prefixEnd_3930200 : Nat := 4983230072969 + 3 ^ 40 * 3930200 * 2
def baseEnd_3930200 : Nat := 224231296477847589791705

theorem tailTrace_3930200 : CollatzResearch.WordTrace tailWord_3930200 prefixEnd_3930200 224231296477847589791705 := by
  unfold tailWord_3930200
  simp only [CollatzResearch.WordTrace]
  refine ⟨71673085180782049783090027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95564113574376066377453369 71673085180782049783090027)
  ·
    refine ⟨107509627771173074674635041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71673085180782049783090027 107509627771173074674635041)
    ·
      refine ⟨80632220828379806005976281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107509627771173074674635041 80632220828379806005976281)
      ·
        refine ⟨60474165621284854504482211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80632220828379806005976281 60474165621284854504482211)
        ·
          refine ⟨90711248431927281756723317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60474165621284854504482211 90711248431927281756723317)
          ·
            refine ⟨8504179540493182664692811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90711248431927281756723317 8504179540493182664692811)
            ·
              refine ⟨12756269310739773997039217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8504179540493182664692811 12756269310739773997039217)
              ·
                refine ⟨9567201983054830497779413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12756269310739773997039217 9567201983054830497779413)
                ·
                  refine ⟨224231296477847589791705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9567201983054830497779413 224231296477847589791705)
                  ·
                    rfl

theorem cell23_3930200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 7].length) (baseStart_3930200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930200 prefixEnd_3930200 := by exact prefixLift 3930200
  have htrace : WordTrace (prefixWord ++ tailWord_3930200) baseStart_3930200 baseEnd_3930200 := by
    simpa [prefixWord, tailWord_3930200, baseEnd_3930200] using wordTrace_append hprefix tailTrace_3930200
  have hstable : (prefixWord ++ tailWord_3930200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930200).length < 2 ^ (prefixWord ++ tailWord_3930200).sum := by decide
  have hdescent : baseEnd_3930200 < baseStart_3930200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930217 : List Nat := [1, 2, 1, 1, 1, 5, 4, 3, 5]
def baseStart_3930217 : Nat := 118140960795 + 3930217 * 2 ^ 59
def prefixEnd_3930217 : Nat := 4983230072969 + 3 ^ 40 * 3930217 * 2
def baseEnd_3930217 : Nat := 224232266385750526845863

theorem tailTrace_3930217 : CollatzResearch.WordTrace tailWord_3930217 prefixEnd_3930217 224232266385750526845863 := by
  unfold tailWord_3930217
  simp only [CollatzResearch.WordTrace]
  refine ⟨143346790402502511469548905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95564526935001674313032603 143346790402502511469548905)
  ·
    refine ⟨107510092801876883602161679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143346790402502511469548905 107510092801876883602161679)
    ·
      refine ⟨161265139202815325403242519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107510092801876883602161679 161265139202815325403242519)
      ·
        refine ⟨241897708804222988104863779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161265139202815325403242519 241897708804222988104863779)
        ·
          refine ⟨362846563206334482157295669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241897708804222988104863779 362846563206334482157295669)
          ·
            refine ⟨34016865300593857702246469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 362846563206334482157295669 34016865300593857702246469)
            ·
              refine ⟨6378162243861348319171213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34016865300593857702246469 6378162243861348319171213)
              ·
                refine ⟨2391810841448005619689205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6378162243861348319171213 2391810841448005619689205)
                ·
                  refine ⟨224232266385750526845863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2391810841448005619689205 224232266385750526845863)
                  ·
                    rfl

theorem cell23_3930217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 5].length) (baseStart_3930217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930217 prefixEnd_3930217 := by exact prefixLift 3930217
  have htrace : WordTrace (prefixWord ++ tailWord_3930217) baseStart_3930217 baseEnd_3930217 := by
    simpa [prefixWord, tailWord_3930217, baseEnd_3930217] using wordTrace_append hprefix tailTrace_3930217
  have hstable : (prefixWord ++ tailWord_3930217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930217).length < 2 ^ (prefixWord ++ tailWord_3930217).sum := by decide
  have hdescent : baseEnd_3930217 < baseStart_3930217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930290 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 8]
def baseStart_3930290 : Nat := 118140960795 + 3930290 * 2 ^ 59
def prefixEnd_3930290 : Nat := 4983230072969 + 3 ^ 40 * 3930290 * 2
def baseEnd_3930290 : Nat := 224236431284392550666659

theorem tailTrace_3930290 : CollatzResearch.WordTrace tailWord_3930290 prefixEnd_3930290 224236431284392550666659 := by
  unfold tailWord_3930290
  simp only [CollatzResearch.WordTrace]
  refine ⟨35837363232809511234239081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95566301954158696624637549 35837363232809511234239081)
  ·
    refine ⟨26878022424607133425679311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35837363232809511234239081 26878022424607133425679311)
    ·
      refine ⟨40317033636910700138518967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26878022424607133425679311 40317033636910700138518967)
      ·
        refine ⟨60475550455366050207778451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40317033636910700138518967 60475550455366050207778451)
        ·
          refine ⟨90713325683049075311667677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60475550455366050207778451 90713325683049075311667677)
          ·
            refine ⟨34017497131143403241875379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90713325683049075311667677 34017497131143403241875379)
            ·
              refine ⟨51026245696715104862813069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34017497131143403241875379 51026245696715104862813069)
              ·
                refine ⟨19134842136268164323554901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51026245696715104862813069 19134842136268164323554901)
                ·
                  refine ⟨224236431284392550666659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19134842136268164323554901 224236431284392550666659)
                  ·
                    rfl

theorem cell23_3930290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_3930290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930290 prefixEnd_3930290 := by exact prefixLift 3930290
  have htrace : WordTrace (prefixWord ++ tailWord_3930290) baseStart_3930290 baseEnd_3930290 := by
    simpa [prefixWord, tailWord_3930290, baseEnd_3930290] using wordTrace_append hprefix tailTrace_3930290
  have hstable : (prefixWord ++ tailWord_3930290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930290).length < 2 ^ (prefixWord ++ tailWord_3930290).sum := by decide
  have hdescent : baseEnd_3930290 < baseStart_3930290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930367 : List Nat := [1, 1, 2, 2, 1, 4, 4, 1, 1, 6]
def baseStart_3930367 : Nat := 118140960795 + 3930367 * 2 ^ 59
def prefixEnd_3930367 : Nat := 4983230072969 + 3 ^ 40 * 3930367 * 2
def baseEnd_3930367 : Nat := 672722473189976384912359

theorem tailTrace_3930367 : CollatzResearch.WordTrace tailWord_3930367 prefixEnd_3930367 672722473189976384912359 := by
  unfold tailWord_3930367
  simp only [CollatzResearch.WordTrace]
  refine ⟨143352261351959087087509355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95568174234639391391672903 143352261351959087087509355)
  ·
    refine ⟨215028392027938630631264033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143352261351959087087509355 215028392027938630631264033)
    ·
      refine ⟨161271294020953972973448025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215028392027938630631264033 161271294020953972973448025)
      ·
        refine ⟨120953470515715479730086019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161271294020953972973448025 120953470515715479730086019)
        ·
          refine ⟨181430205773573219595129029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120953470515715479730086019 181430205773573219595129029)
          ·
            refine ⟨34018163582544978674086693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181430205773573219595129029 34018163582544978674086693)
            ·
              refine ⟨6378405671727183501391255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34018163582544978674086693 6378405671727183501391255)
              ·
                refine ⟨9567608507590775252086883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6378405671727183501391255 9567608507590775252086883)
                ·
                  refine ⟨14351412761386162878130325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9567608507590775252086883 14351412761386162878130325)
                  ·
                    refine ⟨672722473189976384912359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14351412761386162878130325 672722473189976384912359)
                    ·
                      rfl

theorem cell23_3930367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 6].length) (baseStart_3930367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930367 prefixEnd_3930367 := by exact prefixLift 3930367
  have htrace : WordTrace (prefixWord ++ tailWord_3930367) baseStart_3930367 baseEnd_3930367 := by
    simpa [prefixWord, tailWord_3930367, baseEnd_3930367] using wordTrace_append hprefix tailTrace_3930367
  have hstable : (prefixWord ++ tailWord_3930367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930367).length < 2 ^ (prefixWord ++ tailWord_3930367).sum := by decide
  have hdescent : baseEnd_3930367 < baseStart_3930367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930391 : List Nat := [1, 1, 3, 4, 1, 2, 4, 1, 1, 1, 4]
def baseStart_3930391 : Nat := 118140960795 + 3930391 * 2 ^ 59
def prefixEnd_3930391 : Nat := 4983230072969 + 3 ^ 40 * 3930391 * 2
def baseEnd_3930391 : Nat := 2018179743105637060836967

theorem tailTrace_3930391 : CollatzResearch.WordTrace tailWord_3930391 prefixEnd_3930391 2018179743105637060836967 := by
  unfold tailWord_3930391
  simp only [CollatzResearch.WordTrace]
  refine ⟨143353136703872139186383027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95568757802581426124255351 143353136703872139186383027)
  ·
    refine ⟨215029705055808208779574541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143353136703872139186383027 215029705055808208779574541)
    ·
      refine ⟨80636139395928078292340453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215029705055808208779574541 80636139395928078292340453)
      ·
        refine ⟨15119276136736514679813835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80636139395928078292340453 15119276136736514679813835)
        ·
          refine ⟨22678914205104772019720753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15119276136736514679813835 22678914205104772019720753)
          ·
            refine ⟨17009185653828579014790565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22678914205104772019720753 17009185653828579014790565)
            ·
              refine ⟨3189222310092858565273231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17009185653828579014790565 3189222310092858565273231)
              ·
                refine ⟨4783833465139287847909847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3189222310092858565273231 4783833465139287847909847)
                ·
                  refine ⟨7175750197708931771864771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4783833465139287847909847 7175750197708931771864771)
                  ·
                    refine ⟨10763625296563397657797157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7175750197708931771864771 10763625296563397657797157)
                    ·
                      refine ⟨2018179743105637060836967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10763625296563397657797157 2018179743105637060836967)
                      ·
                        rfl

theorem cell23_3930391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_3930391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930391 prefixEnd_3930391 := by exact prefixLift 3930391
  have htrace : WordTrace (prefixWord ++ tailWord_3930391) baseStart_3930391 baseEnd_3930391 := by
    simpa [prefixWord, tailWord_3930391, baseEnd_3930391] using wordTrace_append hprefix tailTrace_3930391
  have hstable : (prefixWord ++ tailWord_3930391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930391).length < 2 ^ (prefixWord ++ tailWord_3930391).sum := by decide
  have hdescent : baseEnd_3930391 < baseStart_3930391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930418 : List Nat := [3, 2, 1, 1, 5, 1, 3, 1, 2, 4]
def baseStart_3930418 : Nat := 118140960795 + 3930418 * 2 ^ 59
def prefixEnd_3930418 : Nat := 4983230072969 + 3 ^ 40 * 3930418 * 2
def baseEnd_3930418 : Nat := 672731202361102818399781

theorem tailTrace_3930418 : CollatzResearch.WordTrace tailWord_3930418 prefixEnd_3930418 672731202361102818399781 := by
  unfold tailWord_3930418
  simp only [CollatzResearch.WordTrace]
  refine ⟨35838530368693580699403977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95569414316516215198410605 35838530368693580699403977)
  ·
    refine ⟨26878897776520185524552983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35838530368693580699403977 26878897776520185524552983)
    ·
      refine ⟨40318346664780278286829475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26878897776520185524552983 40318346664780278286829475)
      ·
        refine ⟨60477519997170417430244213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40318346664780278286829475 60477519997170417430244213)
        ·
          refine ⟨5669767499734726634085395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60477519997170417430244213 5669767499734726634085395)
          ·
            refine ⟨8504651249602089951128093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5669767499734726634085395 8504651249602089951128093)
            ·
              refine ⟨3189244218600783731673035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8504651249602089951128093 3189244218600783731673035)
              ·
                refine ⟨4783866327901175597509553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3189244218600783731673035 4783866327901175597509553)
                ·
                  refine ⟨3587899745925881698132165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4783866327901175597509553 3587899745925881698132165)
                  ·
                    refine ⟨672731202361102818399781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3587899745925881698132165 672731202361102818399781)
                    ·
                      rfl

theorem cell23_3930418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_3930418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930418 prefixEnd_3930418 := by exact prefixLift 3930418
  have htrace : WordTrace (prefixWord ++ tailWord_3930418) baseStart_3930418 baseEnd_3930418 := by
    simpa [prefixWord, tailWord_3930418, baseEnd_3930418] using wordTrace_append hprefix tailTrace_3930418
  have hstable : (prefixWord ++ tailWord_3930418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930418).length < 2 ^ (prefixWord ++ tailWord_3930418).sum := by decide
  have hdescent : baseEnd_3930418 < baseStart_3930418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930424 : List Nat := [2, 1, 2, 1, 3, 1, 5, 1, 1, 3, 3]
def baseStart_3930424 : Nat := 118140960795 + 3930424 * 2 ^ 59
def prefixEnd_3930424 : Nat := 4983230072969 + 3 ^ 40 * 3930424 * 2
def baseEnd_3930424 : Nat := 2018196687967235431724315

theorem tailTrace_3930424 : CollatzResearch.WordTrace tailWord_3930424 prefixEnd_3930424 2018196687967235431724315 := by
  unfold tailWord_3930424
  simp only [CollatzResearch.WordTrace]
  refine ⟨71677170156376292911167163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95569560208501723881556217 71677170156376292911167163)
  ·
    refine ⟨107515755234564439366750745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71677170156376292911167163 107515755234564439366750745)
    ·
      refine ⟨80636816425923329525063059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107515755234564439366750745 80636816425923329525063059)
      ·
        refine ⟨120955224638884994287594589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80636816425923329525063059 120955224638884994287594589)
        ·
          refine ⟨45358209239581872857847971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120955224638884994287594589 45358209239581872857847971)
          ·
            refine ⟨68037313859372809286771957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45358209239581872857847971 68037313859372809286771957)
            ·
              refine ⟨6378498174316200870634871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68037313859372809286771957 6378498174316200870634871)
              ·
                refine ⟨9567747261474301305952307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6378498174316200870634871 9567747261474301305952307)
                ·
                  refine ⟨14351620892211451958928461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9567747261474301305952307 14351620892211451958928461)
                  ·
                    refine ⟨5381857834579294484598173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14351620892211451958928461 5381857834579294484598173)
                    ·
                      refine ⟨2018196687967235431724315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5381857834579294484598173 2018196687967235431724315)
                      ·
                        rfl

theorem cell23_3930424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_3930424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930424 prefixEnd_3930424 := by exact prefixLift 3930424
  have htrace : WordTrace (prefixWord ++ tailWord_3930424) baseStart_3930424 baseEnd_3930424 := by
    simpa [prefixWord, tailWord_3930424, baseEnd_3930424] using wordTrace_append hprefix tailTrace_3930424
  have hstable : (prefixWord ++ tailWord_3930424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930424).length < 2 ^ (prefixWord ++ tailWord_3930424).sum := by decide
  have hdescent : baseEnd_3930424 < baseStart_3930424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930467 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 5]
def baseStart_3930467 : Nat := 118140960795 + 3930467 * 2 ^ 59
def prefixEnd_3930467 : Nat := 4983230072969 + 3 ^ 40 * 3930467 * 2
def baseEnd_3930467 : Nat := 2018218767635378763486617

theorem tailTrace_3930467 : CollatzResearch.WordTrace tailWord_3930467 prefixEnd_3930467 2018218767635378763486617 := by
  unfold tailWord_3930467
  simp only [CollatzResearch.WordTrace]
  refine ⟨143355908651596804166149655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95570605767731202777433103 143355908651596804166149655)
  ·
    refine ⟨215033862977395206249224483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143355908651596804166149655 215033862977395206249224483)
    ·
      refine ⟨322550794466092809373836725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215033862977395206249224483 322550794466092809373836725)
      ·
        refine ⟨30239136981196200878797193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 322550794466092809373836725 30239136981196200878797193)
        ·
          refine ⟨22679352735897150659097895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30239136981196200878797193 22679352735897150659097895)
          ·
            refine ⟨34019029103845725988646843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22679352735897150659097895 34019029103845725988646843)
            ·
              refine ⟨51028543655768588982970265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34019029103845725988646843 51028543655768588982970265)
              ·
                refine ⟨38271407741826441737227699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51028543655768588982970265 38271407741826441737227699)
                ·
                  refine ⟨57407111612739662605841549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38271407741826441737227699 57407111612739662605841549)
                  ·
                    refine ⟨21527666854777373477190581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57407111612739662605841549 21527666854777373477190581)
                    ·
                      refine ⟨2018218767635378763486617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21527666854777373477190581 2018218767635378763486617)
                      ·
                        rfl

theorem cell23_3930467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_3930467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930467 prefixEnd_3930467 := by exact prefixLift 3930467
  have htrace : WordTrace (prefixWord ++ tailWord_3930467) baseStart_3930467 baseEnd_3930467 := by
    simpa [prefixWord, tailWord_3930467, baseEnd_3930467] using wordTrace_append hprefix tailTrace_3930467
  have hstable : (prefixWord ++ tailWord_3930467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930467).length < 2 ^ (prefixWord ++ tailWord_3930467).sum := by decide
  have hdescent : baseEnd_3930467 < baseStart_3930467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930485 : List Nat := [1, 3, 4, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_3930485 : Nat := 118140960795 + 3930485 * 2 ^ 59
def prefixEnd_3930485 : Nat := 4983230072969 + 3 ^ 40 * 3930485 * 2
def baseEnd_3930485 : Nat := 2018228010287159693061535

theorem tailTrace_3930485 : CollatzResearch.WordTrace tailWord_3930485 prefixEnd_3930485 2018228010287159693061535 := by
  unfold tailWord_3930485
  simp only [CollatzResearch.WordTrace]
  refine ⟨143356565165531593240304909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95571043443687728826869939 143356565165531593240304909)
  ·
    refine ⟨53758711937074347465114341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143356565165531593240304909 53758711937074347465114341)
    ·
      refine ⟨10079758488201440149708939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53758711937074347465114341 10079758488201440149708939)
      ·
        refine ⟨15119637732302160224563409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10079758488201440149708939 15119637732302160224563409)
        ·
          refine ⟨11339728299226620168422557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15119637732302160224563409 11339728299226620168422557)
          ·
            refine ⟨4252398112209982563158459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11339728299226620168422557 4252398112209982563158459)
            ·
              refine ⟨6378597168314973844737689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4252398112209982563158459 6378597168314973844737689)
              ·
                refine ⟨4783947876236230383553267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6378597168314973844737689 4783947876236230383553267)
                ·
                  refine ⟨7175921814354345575329901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4783947876236230383553267 7175921814354345575329901)
                  ·
                    refine ⟨2690970680382879590748713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7175921814354345575329901 2690970680382879590748713)
                    ·
                      refine ⟨2018228010287159693061535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2690970680382879590748713 2018228010287159693061535)
                      ·
                        rfl

theorem cell23_3930485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_3930485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930485 prefixEnd_3930485 := by exact prefixLift 3930485
  have htrace : WordTrace (prefixWord ++ tailWord_3930485) baseStart_3930485 baseEnd_3930485 := by
    simpa [prefixWord, tailWord_3930485, baseEnd_3930485] using wordTrace_append hprefix tailTrace_3930485
  have hstable : (prefixWord ++ tailWord_3930485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930485).length < 2 ^ (prefixWord ++ tailWord_3930485).sum := by decide
  have hdescent : baseEnd_3930485 < baseStart_3930485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930517 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 3, 7]
def baseStart_3930517 : Nat := 118140960795 + 3930517 * 2 ^ 59
def prefixEnd_3930517 : Nat := 4983230072969 + 3 ^ 40 * 3930517 * 2
def baseEnd_3930517 : Nat := 672748147222701189287129

theorem tailTrace_3930517 : CollatzResearch.WordTrace tailWord_3930517 prefixEnd_3930517 672748147222701189287129 := by
  unfold tailWord_3930517
  simp only [CollatzResearch.WordTrace]
  refine ⟨143357732301415662705469805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95571821534277108470313203 143357732301415662705469805)
  ·
    refine ⟨53759149613030873514551177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143357732301415662705469805 53759149613030873514551177)
    ·
      refine ⟨40319362209773155135913383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53759149613030873514551177 40319362209773155135913383)
      ·
        refine ⟨60479043314659732703870075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40319362209773155135913383 60479043314659732703870075)
        ·
          refine ⟨90718564971989599055805113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60479043314659732703870075 90718564971989599055805113)
          ·
            refine ⟨68038923728992199291853835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90718564971989599055805113 68038923728992199291853835)
            ·
              refine ⟨102058385593488298937780753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68038923728992199291853835 102058385593488298937780753)
              ·
                refine ⟨76543789195116224203335565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102058385593488298937780753 76543789195116224203335565)
                ·
                  refine ⟨28703920948168584076250837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76543789195116224203335565 28703920948168584076250837)
                  ·
                    refine ⟨672748147222701189287129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28703920948168584076250837 672748147222701189287129)
                    ·
                      rfl

theorem cell23_3930517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_3930517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930517 prefixEnd_3930517 := by exact prefixLift 3930517
  have htrace : WordTrace (prefixWord ++ tailWord_3930517) baseStart_3930517 baseEnd_3930517 := by
    simpa [prefixWord, tailWord_3930517, baseEnd_3930517] using wordTrace_append hprefix tailTrace_3930517
  have hstable : (prefixWord ++ tailWord_3930517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930517).length < 2 ^ (prefixWord ++ tailWord_3930517).sum := by decide
  have hdescent : baseEnd_3930517 < baseStart_3930517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930551 : List Nat := [1, 1, 3, 1, 3, 5, 1, 1, 2, 5]
def baseStart_3930551 : Nat := 118140960795 + 3930551 * 2 ^ 59
def prefixEnd_3930551 : Nat := 4983230072969 + 3 ^ 40 * 3930551 * 2
def baseEnd_3930551 : Nat := 672753966670118811612077

theorem tailTrace_3930551 : CollatzResearch.WordTrace tailWord_3930551 prefixEnd_3930551 672753966670118811612077 := by
  unfold tailWord_3930551
  simp only [CollatzResearch.WordTrace]
  refine ⟨143358972383292486512207507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95572648255528324341471671 143358972383292486512207507)
  ·
    refine ⟨215038458574938729768311261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143358972383292486512207507 215038458574938729768311261)
    ·
      refine ⟨80639421965602023663116723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215038458574938729768311261 80639421965602023663116723)
      ·
        refine ⟨120959132948403035494675085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80639421965602023663116723 120959132948403035494675085)
        ·
          refine ⟨45359674855651138310503157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120959132948403035494675085 45359674855651138310503157)
          ·
            refine ⟨4252469517717294216609671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45359674855651138310503157 4252469517717294216609671)
            ·
              refine ⟨6378704276575941324914507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4252469517717294216609671 6378704276575941324914507)
              ·
                refine ⟨9568056414863911987371761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6378704276575941324914507 9568056414863911987371761)
                ·
                  refine ⟨7176042311147933990528821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9568056414863911987371761 7176042311147933990528821)
                  ·
                    refine ⟨672753966670118811612077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7176042311147933990528821 672753966670118811612077)
                    ·
                      rfl

theorem cell23_3930551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_3930551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930551 prefixEnd_3930551 := by exact prefixLift 3930551
  have htrace : WordTrace (prefixWord ++ tailWord_3930551) baseStart_3930551 baseEnd_3930551 := by
    simpa [prefixWord, tailWord_3930551, baseEnd_3930551] using wordTrace_append hprefix tailTrace_3930551
  have hstable : (prefixWord ++ tailWord_3930551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930551).length < 2 ^ (prefixWord ++ tailWord_3930551).sum := by decide
  have hdescent : baseEnd_3930551 < baseStart_3930551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930581 : List Nat := [1, 3, 2, 3, 1, 2, 1, 3, 3, 4]
def baseStart_3930581 : Nat := 118140960795 + 3930581 * 2 ^ 59
def prefixEnd_3930581 : Nat := 4983230072969 + 3 ^ 40 * 3930581 * 2
def baseEnd_3930581 : Nat := 672759101476663772487031

theorem tailTrace_3930581 : CollatzResearch.WordTrace tailWord_3930581 prefixEnd_3930581 672759101476663772487031 := by
  unfold tailWord_3930581
  simp only [CollatzResearch.WordTrace]
  refine ⟨143360066573183801635799597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95573377715455867757199731 143360066573183801635799597)
  ·
    refine ⟨53760024964943925613424849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143360066573183801635799597 53760024964943925613424849)
    ·
      refine ⟨40320018723707944210068637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53760024964943925613424849 40320018723707944210068637)
      ·
        refine ⟨15120007021390479078775739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40320018723707944210068637 15120007021390479078775739)
        ·
          refine ⟨22680010532085718618163609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15120007021390479078775739 22680010532085718618163609)
          ·
            refine ⟨17010007899064288963622707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22680010532085718618163609 17010007899064288963622707)
            ·
              refine ⟨25515011848596433445434061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17010007899064288963622707 25515011848596433445434061)
              ·
                refine ⟨9568129443223662542037773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25515011848596433445434061 9568129443223662542037773)
                ·
                  refine ⟨3588048541208873453264165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9568129443223662542037773 3588048541208873453264165)
                  ·
                    refine ⟨672759101476663772487031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3588048541208873453264165 672759101476663772487031)
                    ·
                      rfl

theorem cell23_3930581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_3930581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930581 prefixEnd_3930581 := by exact prefixLift 3930581
  have htrace : WordTrace (prefixWord ++ tailWord_3930581) baseStart_3930581 baseEnd_3930581 := by
    simpa [prefixWord, tailWord_3930581, baseEnd_3930581] using wordTrace_append hprefix tailTrace_3930581
  have hstable : (prefixWord ++ tailWord_3930581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930581).length < 2 ^ (prefixWord ++ tailWord_3930581).sum := by decide
  have hdescent : baseEnd_3930581 < baseStart_3930581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930604 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 3]
def baseStart_3930604 : Nat := 118140960795 + 3930604 * 2 ^ 59
def prefixEnd_3930604 : Nat := 4983230072969 + 3 ^ 40 * 3930604 * 2
def baseEnd_3930604 : Nat := 2018289114485044727473487

theorem tailTrace_3930604 : CollatzResearch.WordTrace tailWord_3930604 prefixEnd_3930604 2018289114485044727473487 := by
  unfold tailWord_3930604
  simp only [CollatzResearch.WordTrace]
  refine ⟨71680452726050238281943433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95573936968066984375924577 71680452726050238281943433)
  ·
    refine ⟨53760339544537678711457575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71680452726050238281943433 53760339544537678711457575)
    ·
      refine ⟨80640509316806518067186363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53760339544537678711457575 80640509316806518067186363)
      ·
        refine ⟨120960763975209777100779545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80640509316806518067186363 120960763975209777100779545)
        ·
          refine ⟨90720572981407332825584659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120960763975209777100779545 90720572981407332825584659)
          ·
            refine ⟨136080859472110999238376989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90720572981407332825584659 136080859472110999238376989)
            ·
              refine ⟨51030322302041624714391371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136080859472110999238376989 51030322302041624714391371)
              ·
                refine ⟨76545483453062437071587057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51030322302041624714391371 76545483453062437071587057)
                ·
                  refine ⟨57409112589796827803690293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76545483453062437071587057 57409112589796827803690293)
                  ·
                    refine ⟨5382104305293452606595965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57409112589796827803690293 5382104305293452606595965)
                    ·
                      refine ⟨2018289114485044727473487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5382104305293452606595965 2018289114485044727473487)
                      ·
                        rfl

theorem cell23_3930604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_3930604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930604 prefixEnd_3930604 := by exact prefixLift 3930604
  have htrace : WordTrace (prefixWord ++ tailWord_3930604) baseStart_3930604 baseEnd_3930604 := by
    simpa [prefixWord, tailWord_3930604, baseEnd_3930604] using wordTrace_append hprefix tailTrace_3930604
  have hstable : (prefixWord ++ tailWord_3930604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930604).length < 2 ^ (prefixWord ++ tailWord_3930604).sum := by decide
  have hdescent : baseEnd_3930604 < baseStart_3930604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930661 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 2, 6, 2]
def baseStart_3930661 : Nat := 118140960795 + 3930661 * 2 ^ 59
def prefixEnd_3930661 : Nat := 4983230072969 + 3 ^ 40 * 3930661 * 2
def baseEnd_3930661 : Nat := 2018318382882351004460725

theorem tailTrace_3930661 : CollatzResearch.WordTrace tailWord_3930661 prefixEnd_3930661 2018318382882351004460725 := by
  unfold tailWord_3930661
  simp only [CollatzResearch.WordTrace]
  refine ⟨143362984412893975298711837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95575322941929316865807891 143362984412893975298711837)
  ·
    refine ⟨53761119154835240737016939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143362984412893975298711837 53761119154835240737016939)
    ·
      refine ⟨80641678732252861105525409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53761119154835240737016939 80641678732252861105525409)
      ·
        refine ⟨60481259049189645829144057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80641678732252861105525409 60481259049189645829144057)
        ·
          refine ⟨45360944286892234371858043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60481259049189645829144057 45360944286892234371858043)
          ·
            refine ⟨68041416430338351557787065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45360944286892234371858043 68041416430338351557787065)
            ·
              refine ⟨51031062322753763668340299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68041416430338351557787065 51031062322753763668340299)
              ·
                refine ⟨76546593484130645502510449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51031062322753763668340299 76546593484130645502510449)
                ·
                  refine ⟨57409945113097984126882837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76546593484130645502510449 57409945113097984126882837)
                  ·
                    refine ⟨2691091177176468005947633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57409945113097984126882837 2691091177176468005947633)
                    ·
                      refine ⟨2018318382882351004460725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2691091177176468005947633 2018318382882351004460725)
                      ·
                        rfl

theorem cell23_3930661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_3930661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930661 prefixEnd_3930661 := by exact prefixLift 3930661
  have htrace : WordTrace (prefixWord ++ tailWord_3930661) baseStart_3930661 baseEnd_3930661 := by
    simpa [prefixWord, tailWord_3930661, baseEnd_3930661] using wordTrace_append hprefix tailTrace_3930661
  have hstable : (prefixWord ++ tailWord_3930661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930661).length < 2 ^ (prefixWord ++ tailWord_3930661).sum := by decide
  have hdescent : baseEnd_3930661 < baseStart_3930661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930684 : List Nat := [2, 2, 2, 2, 3, 12]
def baseStart_3930684 : Nat := 118140960795 + 3930684 * 2 ^ 59
def prefixEnd_3930684 : Nat := 4983230072969 + 3 ^ 40 * 3930684 * 2
def baseEnd_3930684 : Nat := 8305885567643639565733

theorem tailTrace_3930684 : CollatzResearch.WordTrace tailWord_3930684 prefixEnd_3930684 8305885567643639565733 := by
  unfold tailWord_3930684
  simp only [CollatzResearch.WordTrace]
  refine ⟨71681911645905325113399553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95575882194540433484532737 71681911645905325113399553)
  ·
    refine ⟨53761433734428993835049665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71681911645905325113399553 53761433734428993835049665)
    ·
      refine ⟨40321075300821745376287249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53761433734428993835049665 40321075300821745376287249)
      ·
        refine ⟨30240806475616309032215437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40321075300821745376287249 30240806475616309032215437)
        ·
          refine ⟨11340302428356115887080789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30240806475616309032215437 11340302428356115887080789)
          ·
            refine ⟨8305885567643639565733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 11340302428356115887080789 8305885567643639565733)
            ·
              rfl

theorem cell23_3930684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 12].length) (baseStart_3930684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930684 prefixEnd_3930684 := by exact prefixLift 3930684
  have htrace : WordTrace (prefixWord ++ tailWord_3930684) baseStart_3930684 baseEnd_3930684 := by
    simpa [prefixWord, tailWord_3930684, baseEnd_3930684] using wordTrace_append hprefix tailTrace_3930684
  have hstable : (prefixWord ++ tailWord_3930684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930684).length < 2 ^ (prefixWord ++ tailWord_3930684).sum := by decide
  have hdescent : baseEnd_3930684 < baseStart_3930684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930689 : List Nat := [1, 2, 5, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_3930689 : Nat := 118140960795 + 3930689 * 2 ^ 59
def prefixEnd_3930689 : Nat := 4983230072969 + 3 ^ 40 * 3930689 * 2
def baseEnd_3930689 : Nat := 2018332760340676894910597

theorem tailTrace_3930689 : CollatzResearch.WordTrace tailWord_3930689 prefixEnd_3930689 2018332760340676894910597 := by
  unfold tailWord_3930689
  simp only [CollatzResearch.WordTrace]
  refine ⟨143364005656792536080731121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95576003771195024053820747 143364005656792536080731121)
  ·
    refine ⟨107523004242594402060548341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143364005656792536080731121 107523004242594402060548341)
    ·
      refine ⟨10080281647743225193176407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107523004242594402060548341 10080281647743225193176407)
      ·
        refine ⟨15120422471614837789764611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10080281647743225193176407 15120422471614837789764611)
        ·
          refine ⟨22680633707422256684646917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15120422471614837789764611 22680633707422256684646917)
          ·
            refine ⟨4252618820141673128371297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22680633707422256684646917 4252618820141673128371297)
            ·
              refine ⟨3189464115106254846278473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4252618820141673128371297 3189464115106254846278473)
              ·
                refine ⟨2392098086329691134708855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3189464115106254846278473 2392098086329691134708855)
                ·
                  refine ⟨3588147129494536702063283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2392098086329691134708855 3588147129494536702063283)
                  ·
                    refine ⟨5382220694241805053094925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3588147129494536702063283 5382220694241805053094925)
                    ·
                      refine ⟨2018332760340676894910597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5382220694241805053094925 2018332760340676894910597)
                      ·
                        rfl

theorem cell23_3930689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_3930689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930689 prefixEnd_3930689 := by exact prefixLift 3930689
  have htrace : WordTrace (prefixWord ++ tailWord_3930689) baseStart_3930689 baseEnd_3930689 := by
    simpa [prefixWord, tailWord_3930689, baseEnd_3930689] using wordTrace_append hprefix tailTrace_3930689
  have hstable : (prefixWord ++ tailWord_3930689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930689).length < 2 ^ (prefixWord ++ tailWord_3930689).sum := by decide
  have hdescent : baseEnd_3930689 < baseStart_3930689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930708 : List Nat := [2, 4, 1, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_3930708 : Nat := 118140960795 + 3930708 * 2 ^ 59
def prefixEnd_3930708 : Nat := 4983230072969 + 3 ^ 40 * 3930708 * 2
def baseEnd_3930708 : Nat := 2018342516473112320573009

theorem tailTrace_3930708 : CollatzResearch.WordTrace tailWord_3930708 prefixEnd_3930708 2018342516473112320573009 := by
  unfold tailWord_3930708
  simp only [CollatzResearch.WordTrace]
  refine ⟨71682349321861851162836389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95576465762482468217115185 71682349321861851162836389)
  ·
    refine ⟨13440440497849097093031823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71682349321861851162836389 13440440497849097093031823)
    ·
      refine ⟨20160660746773645639547735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13440440497849097093031823 20160660746773645639547735)
      ·
        refine ⟨30240991120160468459321603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20160660746773645639547735 30240991120160468459321603)
        ·
          refine ⟨45361486680240702688982405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30240991120160468459321603 45361486680240702688982405)
          ·
            refine ⟨8505278752545131754184201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45361486680240702688982405 8505278752545131754184201)
            ·
              refine ⟨6378959064408848815638151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8505278752545131754184201 6378959064408848815638151)
              ·
                refine ⟨9568438596613273223457227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6378959064408848815638151 9568438596613273223457227)
                ·
                  refine ⟨14352657894919909835185841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9568438596613273223457227 14352657894919909835185841)
                  ·
                    refine ⟨10764493421189932376389381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14352657894919909835185841 10764493421189932376389381)
                    ·
                      refine ⟨2018342516473112320573009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10764493421189932376389381 2018342516473112320573009)
                      ·
                        rfl

theorem cell23_3930708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_3930708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930708 prefixEnd_3930708 := by exact prefixLift 3930708
  have htrace : WordTrace (prefixWord ++ tailWord_3930708) baseStart_3930708 baseEnd_3930708 := by
    simpa [prefixWord, tailWord_3930708, baseEnd_3930708] using wordTrace_append hprefix tailTrace_3930708
  have hstable : (prefixWord ++ tailWord_3930708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930708).length < 2 ^ (prefixWord ++ tailWord_3930708).sum := by decide
  have hdescent : baseEnd_3930708 < baseStart_3930708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930744 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 3, 8]
def baseStart_3930744 : Nat := 118140960795 + 3930744 * 2 ^ 59
def prefixEnd_3930744 : Nat := 4983230072969 + 3 ^ 40 * 3930744 * 2
def baseEnd_3930744 : Nat := 672787000592224726574281

theorem tailTrace_3930744 : CollatzResearch.WordTrace tailWord_3930744 prefixEnd_3930744 672787000592224726574281 := by
  unfold tailWord_3930744
  simp only [CollatzResearch.WordTrace]
  refine ⟨71683005835796640236991643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95577341114395520315988857 71683005835796640236991643)
  ·
    refine ⟨107524508753694960355487465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71683005835796640236991643 107524508753694960355487465)
    ·
      refine ⟨80643381565271220266615599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107524508753694960355487465 80643381565271220266615599)
      ·
        refine ⟨120965072347906830399923399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80643381565271220266615599 120965072347906830399923399)
        ·
          refine ⟨181447608521860245599885099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120965072347906830399923399 181447608521860245599885099)
          ·
            refine ⟨272171412782790368399827649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181447608521860245599885099 272171412782790368399827649)
            ·
              refine ⟨204128559587092776299870737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272171412782790368399827649 204128559587092776299870737)
              ·
                refine ⟨153096419690319582224903053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204128559587092776299870737 153096419690319582224903053)
                ·
                  refine ⟨57411157383869843334338645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 153096419690319582224903053 57411157383869843334338645)
                  ·
                    refine ⟨672787000592224726574281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57411157383869843334338645 672787000592224726574281)
                    ·
                      rfl

theorem cell23_3930744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_3930744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930744 prefixEnd_3930744 := by exact prefixLift 3930744
  have htrace : WordTrace (prefixWord ++ tailWord_3930744) baseStart_3930744 baseEnd_3930744 := by
    simpa [prefixWord, tailWord_3930744, baseEnd_3930744] using wordTrace_append hprefix tailTrace_3930744
  have hstable : (prefixWord ++ tailWord_3930744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930744).length < 2 ^ (prefixWord ++ tailWord_3930744).sum := by decide
  have hdescent : baseEnd_3930744 < baseStart_3930744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930745 : List Nat := [1, 2, 1, 3, 3, 2, 3, 2, 2, 1, 3]
def baseStart_3930745 : Nat := 118140960795 + 3930745 * 2 ^ 59
def prefixEnd_3930745 : Nat := 4983230072969 + 3 ^ 40 * 3930745 * 2
def baseEnd_3930745 : Nat := 2018361515257328675810339

theorem tailTrace_3930745 : CollatzResearch.WordTrace tailWord_3930745 prefixEnd_3930745 2018361515257328675810339 := by
  unfold tailWord_3930745
  simp only [CollatzResearch.WordTrace]
  refine ⟨143366048144589657644769689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95577365429726438429846459 143366048144589657644769689)
  ·
    refine ⟨107524536108442243233577267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143366048144589657644769689 107524536108442243233577267)
    ·
      refine ⟨161286804162663364850365901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107524536108442243233577267 161286804162663364850365901)
      ·
        refine ⟨60482551560998761818887213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161286804162663364850365901 60482551560998761818887213)
        ·
          refine ⟨22680956835374535682082705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60482551560998761818887213 22680956835374535682082705)
          ·
            refine ⟨17010717626530901761562029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22680956835374535682082705 17010717626530901761562029)
            ·
              refine ⟨6379019109949088160585761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17010717626530901761562029 6379019109949088160585761)
              ·
                refine ⟨4784264332461816120439321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6379019109949088160585761 4784264332461816120439321)
                ·
                  refine ⟨3588198249346362090329491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4784264332461816120439321 3588198249346362090329491)
                  ·
                    refine ⟨5382297374019543135494237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3588198249346362090329491 5382297374019543135494237)
                    ·
                      refine ⟨2018361515257328675810339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5382297374019543135494237 2018361515257328675810339)
                      ·
                        rfl

theorem cell23_3930745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_3930745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930745 prefixEnd_3930745 := by exact prefixLift 3930745
  have htrace : WordTrace (prefixWord ++ tailWord_3930745) baseStart_3930745 baseEnd_3930745 := by
    simpa [prefixWord, tailWord_3930745, baseEnd_3930745] using wordTrace_append hprefix tailTrace_3930745
  have hstable : (prefixWord ++ tailWord_3930745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930745).length < 2 ^ (prefixWord ++ tailWord_3930745).sum := by decide
  have hdescent : baseEnd_3930745 < baseStart_3930745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930762 : List Nat := [3, 1, 2, 3, 4, 1, 1, 1, 1, 3, 3]
def baseStart_3930762 : Nat := 118140960795 + 3930762 * 2 ^ 59
def prefixEnd_3930762 : Nat := 4983230072969 + 3 ^ 40 * 3930762 * 2
def baseEnd_3930762 : Nat := 2018370244428455109297761

theorem tailTrace_3930762 : CollatzResearch.WordTrace tailWord_3930762 prefixEnd_3930762 2018370244428455109297761 := by
  unfold tailWord_3930762
  simp only [CollatzResearch.WordTrace]
  refine ⟨35841667046382017387034635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95577778790352046365425693 35841667046382017387034635)
  ·
    refine ⟨53762500569573026080551953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35841667046382017387034635 53762500569573026080551953)
    ·
      refine ⟨40321875427179769560413965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53762500569573026080551953 40321875427179769560413965)
      ·
        refine ⟨15120703285192413585155237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40321875427179769560413965 15120703285192413585155237)
        ·
          refine ⟨2835131865973577547216607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15120703285192413585155237 2835131865973577547216607)
          ·
            refine ⟨4252697798960366320824911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2835131865973577547216607 4252697798960366320824911)
            ·
              refine ⟨6379046698440549481237367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4252697798960366320824911 6379046698440549481237367)
              ·
                refine ⟨9568570047660824221856051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6379046698440549481237367 9568570047660824221856051)
                ·
                  refine ⟨14352855071491236332784077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9568570047660824221856051 14352855071491236332784077)
                  ·
                    refine ⟨5382320651809213624794029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14352855071491236332784077 5382320651809213624794029)
                    ·
                      refine ⟨2018370244428455109297761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5382320651809213624794029 2018370244428455109297761)
                      ·
                        rfl

theorem cell23_3930762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_3930762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930762 prefixEnd_3930762 := by exact prefixLift 3930762
  have htrace : WordTrace (prefixWord ++ tailWord_3930762) baseStart_3930762 baseEnd_3930762 := by
    simpa [prefixWord, tailWord_3930762, baseEnd_3930762] using wordTrace_append hprefix tailTrace_3930762
  have hstable : (prefixWord ++ tailWord_3930762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930762).length < 2 ^ (prefixWord ++ tailWord_3930762).sum := by decide
  have hdescent : baseEnd_3930762 < baseStart_3930762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930772 : List Nat := [2, 4, 2, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_3930772 : Nat := 118140960795 + 3930772 * 2 ^ 59
def prefixEnd_3930772 : Nat := 4983230072969 + 3 ^ 40 * 3930772 * 2
def baseEnd_3930772 : Nat := 2018375379235000070172715

theorem tailTrace_3930772 : CollatzResearch.WordTrace tailWord_3930772 prefixEnd_3930772 2018375379235000070172715 := by
  unfold tailWord_3930772
  simp only [CollatzResearch.WordTrace]
  refine ⟨71683516457745920628001285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95578021943661227504001713 71683516457745920628001285)
  ·
    refine ⟨13440659335827360117750241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71683516457745920628001285 13440659335827360117750241)
    ·
      refine ⟨10080494501870520088312681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13440659335827360117750241 10080494501870520088312681)
      ·
        refine ⟨7560370876402890066234511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10080494501870520088312681 7560370876402890066234511)
        ·
          refine ⟨11340556314604335099351767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7560370876402890066234511 11340556314604335099351767)
          ·
            refine ⟨17010834471906502649027651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11340556314604335099351767 17010834471906502649027651)
            ·
              refine ⟨25516251707859753973541477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17010834471906502649027651 25516251707859753973541477)
              ·
                refine ⟨4784297195223703870039027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25516251707859753973541477 4784297195223703870039027)
                ·
                  refine ⟨7176445792835555805058541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4784297195223703870039027 7176445792835555805058541)
                  ·
                    refine ⟨2691167172313333426896953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7176445792835555805058541 2691167172313333426896953)
                    ·
                      refine ⟨2018375379235000070172715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2691167172313333426896953 2018375379235000070172715)
                      ·
                        rfl

theorem cell23_3930772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_3930772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930772 prefixEnd_3930772 := by exact prefixLift 3930772
  have htrace : WordTrace (prefixWord ++ tailWord_3930772) baseStart_3930772 baseEnd_3930772 := by
    simpa [prefixWord, tailWord_3930772, baseEnd_3930772] using wordTrace_append hprefix tailTrace_3930772
  have hstable : (prefixWord ++ tailWord_3930772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930772).length < 2 ^ (prefixWord ++ tailWord_3930772).sum := by decide
  have hdescent : baseEnd_3930772 < baseStart_3930772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930781 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_3930781 : Nat := 118140960795 + 3930781 * 2 ^ 59
def prefixEnd_3930781 : Nat := 4983230072969 + 3 ^ 40 * 3930781 * 2
def baseEnd_3930781 : Nat := 2018380000560890534960173

theorem tailTrace_3930781 : CollatzResearch.WordTrace tailWord_3930781 prefixEnd_3930781 2018380000560890534960173 := by
  unfold tailWord_3930781
  simp only [CollatzResearch.WordTrace]
  refine ⟨143367361172459235793080197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95578240781639490528720131 143367361172459235793080197)
  ·
    refine ⟨26881380219836106711202537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143367361172459235793080197 26881380219836106711202537)
    ·
      refine ⟨20161035164877080033401903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26881380219836106711202537 20161035164877080033401903)
      ·
        refine ⟨30241552747315620050102855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20161035164877080033401903 30241552747315620050102855)
        ·
          refine ⟨45362329120973430075154283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30241552747315620050102855 45362329120973430075154283)
          ·
            refine ⟨68043493681460145112731425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45362329120973430075154283 68043493681460145112731425)
            ·
              refine ⟨51032620261095108834548569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68043493681460145112731425 51032620261095108834548569)
              ·
                refine ⟨38274465195821331625911427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51032620261095108834548569 38274465195821331625911427)
                ·
                  refine ⟨57411697793731997438867141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38274465195821331625911427 57411697793731997438867141)
                  ·
                    refine ⟨10764693336324749519787589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57411697793731997438867141 10764693336324749519787589)
                    ·
                      refine ⟨2018380000560890534960173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10764693336324749519787589 2018380000560890534960173)
                      ·
                        rfl

theorem cell23_3930781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_3930781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930781 prefixEnd_3930781 := by exact prefixLift 3930781
  have htrace : WordTrace (prefixWord ++ tailWord_3930781) baseStart_3930781 baseEnd_3930781 := by
    simpa [prefixWord, tailWord_3930781, baseEnd_3930781] using wordTrace_append hprefix tailTrace_3930781
  have hstable : (prefixWord ++ tailWord_3930781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930781).length < 2 ^ (prefixWord ++ tailWord_3930781).sum := by decide
  have hdescent : baseEnd_3930781 < baseStart_3930781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930869 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_3930869 : Nat := 118140960795 + 3930869 * 2 ^ 59
def prefixEnd_3930869 : Nat := 4983230072969 + 3 ^ 40 * 3930869 * 2
def baseEnd_3930869 : Nat := 2018425186858486190659769

theorem tailTrace_3930869 : CollatzResearch.WordTrace tailWord_3930869 prefixEnd_3930869 2018425186858486190659769 := by
  unfold tailWord_3930869
  simp only [CollatzResearch.WordTrace]
  refine ⟨143370570796140426822283661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95580380530760284548189107 143370570796140426822283661)
  ·
    refine ⟨53763964048552660058356373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143370570796140426822283661 53763964048552660058356373)
    ·
      refine ⟨2520185814775905940235455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53763964048552660058356373 2520185814775905940235455)
      ·
        refine ⟨3780278722163858910353183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2520185814775905940235455 3780278722163858910353183)
        ·
          refine ⟨5670418083245788365529775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3780278722163858910353183 5670418083245788365529775)
          ·
            refine ⟨8505627124868682548294663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5670418083245788365529775 8505627124868682548294663)
            ·
              refine ⟨12758440687303023822441995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8505627124868682548294663 12758440687303023822441995)
              ·
                refine ⟨19137661030954535733662993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12758440687303023822441995 19137661030954535733662993)
                ·
                  refine ⟨14353245773215901800247245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19137661030954535733662993 14353245773215901800247245)
                  ·
                    refine ⟨5382467164955963175092717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14353245773215901800247245 5382467164955963175092717)
                    ·
                      refine ⟨2018425186858486190659769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5382467164955963175092717 2018425186858486190659769)
                      ·
                        rfl

theorem cell23_3930869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_3930869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930869 prefixEnd_3930869 := by exact prefixLift 3930869
  have htrace : WordTrace (prefixWord ++ tailWord_3930869) baseStart_3930869 baseEnd_3930869 := by
    simpa [prefixWord, tailWord_3930869, baseEnd_3930869] using wordTrace_append hprefix tailTrace_3930869
  have hstable : (prefixWord ++ tailWord_3930869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930869).length < 2 ^ (prefixWord ++ tailWord_3930869).sum := by decide
  have hdescent : baseEnd_3930869 < baseStart_3930869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930871 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 4]
def baseStart_3930871 : Nat := 118140960795 + 3930871 * 2 ^ 59
def prefixEnd_3930871 : Nat := 4983230072969 + 3 ^ 40 * 3930871 * 2
def baseEnd_3930871 : Nat := 2018426213819795182834759

theorem tailTrace_3930871 : CollatzResearch.WordTrace tailWord_3930871 prefixEnd_3930871 2018426213819795182834759 := by
  unfold tailWord_3930871
  simp only [CollatzResearch.WordTrace]
  refine ⟨143370643742133181163856467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95580429161422120775904311 143370643742133181163856467)
  ·
    refine ⟨215055965613199771745784701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143370643742133181163856467 215055965613199771745784701)
    ·
      refine ⟨80645987104949914404669263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215055965613199771745784701 80645987104949914404669263)
      ·
        refine ⟨120968980657424871607003895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80645987104949914404669263 120968980657424871607003895)
        ·
          refine ⟨181453470986137307410505843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120968980657424871607003895 181453470986137307410505843)
          ·
            refine ⟨272180206479205961115758765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181453470986137307410505843 272180206479205961115758765)
            ·
              refine ⟨102067577429702235418409537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 272180206479205961115758765 102067577429702235418409537)
              ·
                refine ⟨76550683072276676563807153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102067577429702235418409537 76550683072276676563807153)
                ·
                  refine ⟨57413012304207507422855365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76550683072276676563807153 57413012304207507422855365)
                  ·
                    refine ⟨10764939807038907641785381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57413012304207507422855365 10764939807038907641785381)
                    ·
                      refine ⟨2018426213819795182834759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10764939807038907641785381 2018426213819795182834759)
                      ·
                        rfl

theorem cell23_3930871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_3930871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930871 prefixEnd_3930871 := by exact prefixLift 3930871
  have htrace : WordTrace (prefixWord ++ tailWord_3930871) baseStart_3930871 baseEnd_3930871 := by
    simpa [prefixWord, tailWord_3930871, baseEnd_3930871] using wordTrace_append hprefix tailTrace_3930871
  have hstable : (prefixWord ++ tailWord_3930871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930871).length < 2 ^ (prefixWord ++ tailWord_3930871).sum := by decide
  have hdescent : baseEnd_3930871 < baseStart_3930871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930881 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 10]
def baseStart_3930881 : Nat := 118140960795 + 3930881 * 2 ^ 59
def prefixEnd_3930881 : Nat := 4983230072969 + 3 ^ 40 * 3930881 * 2
def baseEnd_3930881 : Nat := 224270149847371127078857

theorem tailTrace_3930881 : CollatzResearch.WordTrace tailWord_3930881 prefixEnd_3930881 224270149847371127078857 := by
  unfold tailWord_3930881
  simp only [CollatzResearch.WordTrace]
  refine ⟨143371008472096952871720497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95580672314731301914480331 143371008472096952871720497)
  ·
    refine ⟨107528256354072714653790373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143371008472096952871720497 107528256354072714653790373)
    ·
      refine ⟨20161548066388633997585695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107528256354072714653790373 20161548066388633997585695)
      ·
        refine ⟨30242322099582950996378543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20161548066388633997585695 30242322099582950996378543)
        ·
          refine ⟨45363483149374426494567815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30242322099582950996378543 45363483149374426494567815)
          ·
            refine ⟨68045224724061639741851723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45363483149374426494567815 68045224724061639741851723)
            ·
              refine ⟨102067837086092459612777585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68045224724061639741851723 102067837086092459612777585)
              ·
                refine ⟨76550877814569344709583189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102067837086092459612777585 76550877814569344709583189)
                ·
                  refine ⟨224270149847371127078857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 76550877814569344709583189 224270149847371127078857)
                  ·
                    rfl

theorem cell23_3930881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 10].length) (baseStart_3930881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930881 prefixEnd_3930881 := by exact prefixLift 3930881
  have htrace : WordTrace (prefixWord ++ tailWord_3930881) baseStart_3930881 baseEnd_3930881 := by
    simpa [prefixWord, tailWord_3930881, baseEnd_3930881] using wordTrace_append hprefix tailTrace_3930881
  have hstable : (prefixWord ++ tailWord_3930881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930881).length < 2 ^ (prefixWord ++ tailWord_3930881).sum := by decide
  have hdescent : baseEnd_3930881 < baseStart_3930881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930921 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 2, 4, 5]
def baseStart_3930921 : Nat := 118140960795 + 3930921 * 2 ^ 59
def prefixEnd_3930921 : Nat := 4983230072969 + 3 ^ 40 * 3930921 * 2
def baseEnd_3930921 : Nat := 2018451887852519987209529

theorem tailTrace_3930921 : CollatzResearch.WordTrace tailWord_3930921 prefixEnd_3930921 2018451887852519987209529 := by
  unfold tailWord_3930921
  simp only [CollatzResearch.WordTrace]
  refine ⟨143372467391952039703176617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95581644927968026468784411 143372467391952039703176617)
  ·
    refine ⟨107529350543964029777382463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143372467391952039703176617 107529350543964029777382463)
    ·
      refine ⟨161294025815946044666073695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107529350543964029777382463 161294025815946044666073695)
      ·
        refine ⟨241941038723919066999110543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161294025815946044666073695 241941038723919066999110543)
        ·
          refine ⟨362911558085878600498665815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241941038723919066999110543 362911558085878600498665815)
          ·
            refine ⟨544367337128817900747998723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362911558085878600498665815 544367337128817900747998723)
            ·
              refine ⟨816551005693226851121998085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544367337128817900747998723 816551005693226851121998085)
              ·
                refine ⟨153103313567480034585374641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 816551005693226851121998085 153103313567480034585374641)
                ·
                  refine ⟨114827485175610025939030981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153103313567480034585374641 114827485175610025939030981)
                  ·
                    refine ⟨21530153470426879863568309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114827485175610025939030981 21530153470426879863568309)
                    ·
                      refine ⟨2018451887852519987209529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21530153470426879863568309 2018451887852519987209529)
                      ·
                        rfl

theorem cell23_3930921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_3930921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930921 prefixEnd_3930921 := by exact prefixLift 3930921
  have htrace : WordTrace (prefixWord ++ tailWord_3930921) baseStart_3930921 baseEnd_3930921 := by
    simpa [prefixWord, tailWord_3930921, baseEnd_3930921] using wordTrace_append hprefix tailTrace_3930921
  have hstable : (prefixWord ++ tailWord_3930921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930921).length < 2 ^ (prefixWord ++ tailWord_3930921).sum := by decide
  have hdescent : baseEnd_3930921 < baseStart_3930921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930958 : List Nat := [4, 1, 1, 1, 1, 1, 1, 6, 1, 6]
def baseStart_3930958 : Nat := 118140960795 + 3930958 * 2 ^ 59
def prefixEnd_3930958 : Nat := 4983230072969 + 3 ^ 40 * 3930958 * 2
def baseEnd_3930958 : Nat := 672823628878912114148953

theorem tailTrace_3930958 : CollatzResearch.WordTrace tailWord_3930958 prefixEnd_3930958 672823628878912114148953 := by
  unfold tailWord_3930958
  simp only [CollatzResearch.WordTrace]
  refine ⟨17921727111602249377784191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95582544595211996681515685 17921727111602249377784191)
  ·
    refine ⟨26882590667403374066676287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17921727111602249377784191 26882590667403374066676287)
    ·
      refine ⟨40323886001105061100014431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26882590667403374066676287 40323886001105061100014431)
      ·
        refine ⟨60485829001657591650021647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40323886001105061100014431 60485829001657591650021647)
        ·
          refine ⟨90728743502486387475032471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60485829001657591650021647 90728743502486387475032471)
          ·
            refine ⟨136093115253729581212548707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90728743502486387475032471 136093115253729581212548707)
            ·
              refine ⟨204139672880594371818823061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136093115253729581212548707 204139672880594371818823061)
              ·
                refine ⟨9569047166277861179007331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 204139672880594371818823061 9569047166277861179007331)
                ·
                  refine ⟨14353570749416791768510997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9569047166277861179007331 14353570749416791768510997)
                  ·
                    refine ⟨672823628878912114148953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14353570749416791768510997 672823628878912114148953)
                    ·
                      rfl

theorem cell23_3930958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_3930958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930958 prefixEnd_3930958 := by exact prefixLift 3930958
  have htrace : WordTrace (prefixWord ++ tailWord_3930958) baseStart_3930958 baseEnd_3930958 := by
    simpa [prefixWord, tailWord_3930958, baseEnd_3930958] using wordTrace_append hprefix tailTrace_3930958
  have hstable : (prefixWord ++ tailWord_3930958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930958).length < 2 ^ (prefixWord ++ tailWord_3930958).sum := by decide
  have hdescent : baseEnd_3930958 < baseStart_3930958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930965 : List Nat := [1, 3, 2, 2, 2, 1, 1, 5, 1, 1, 4]
def baseStart_3930965 : Nat := 118140960795 + 3930965 * 2 ^ 59
def prefixEnd_3930965 : Nat := 4983230072969 + 3 ^ 40 * 3930965 * 2
def baseEnd_3930965 : Nat := 2018474481001317815059327

theorem tailTrace_3930965 : CollatzResearch.WordTrace tailWord_3930965 prefixEnd_3930965 2018474481001317815059327 := by
  unfold tailWord_3930965
  simp only [CollatzResearch.WordTrace]
  refine ⟨143374072203792635217778349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95582714802528423478518899 143374072203792635217778349)
  ·
    refine ⟨53765277076422238206666881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143374072203792635217778349 53765277076422238206666881)
    ·
      refine ⟨40323957807316678655000161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53765277076422238206666881 40323957807316678655000161)
      ·
        refine ⟨30242968355487508991250121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40323957807316678655000161 30242968355487508991250121)
        ·
          refine ⟨22682226266615631743437591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30242968355487508991250121 22682226266615631743437591)
          ·
            refine ⟨34023339399923447615156387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22682226266615631743437591 34023339399923447615156387)
            ·
              refine ⟨51035009099885171422734581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34023339399923447615156387 51035009099885171422734581)
              ·
                refine ⟨4784532103114234820881367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51035009099885171422734581 4784532103114234820881367)
                ·
                  refine ⟨7176798154671352231322051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4784532103114234820881367 7176798154671352231322051)
                  ·
                    refine ⟨10765197232007028346983077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7176798154671352231322051 10765197232007028346983077)
                    ·
                      refine ⟨2018474481001317815059327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10765197232007028346983077 2018474481001317815059327)
                      ·
                        rfl

theorem cell23_3930965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_3930965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930965 prefixEnd_3930965 := by exact prefixLift 3930965
  have htrace : WordTrace (prefixWord ++ tailWord_3930965) baseStart_3930965 baseEnd_3930965 := by
    simpa [prefixWord, tailWord_3930965, baseEnd_3930965] using wordTrace_append hprefix tailTrace_3930965
  have hstable : (prefixWord ++ tailWord_3930965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930965).length < 2 ^ (prefixWord ++ tailWord_3930965).sum := by decide
  have hdescent : baseEnd_3930965 < baseStart_3930965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930975 : List Nat := [1, 1, 2, 3, 1, 3, 2, 4, 2, 4]
def baseStart_3930975 : Nat := 118140960795 + 3930975 * 2 ^ 59
def prefixEnd_3930975 : Nat := 4983230072969 + 3 ^ 40 * 3930975 * 2
def baseEnd_3930975 : Nat := 672826538602620925311427

theorem tailTrace_3930975 : CollatzResearch.WordTrace tailWord_3930975 prefixEnd_3930975 672826538602620925311427 := by
  unfold tailWord_3930975
  simp only [CollatzResearch.WordTrace]
  refine ⟨143374436933756406925642379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95582957955837604617094919 143374436933756406925642379)
  ·
    refine ⟨215061655400634610388463569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143374436933756406925642379 215061655400634610388463569)
    ·
      refine ⟨161296241550475957791347677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215061655400634610388463569 161296241550475957791347677)
      ·
        refine ⟨60486090581428484171755379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161296241550475957791347677 60486090581428484171755379)
        ·
          refine ⟨90729135872142726257633069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60486090581428484171755379 90729135872142726257633069)
          ·
            refine ⟨34023425952053522346612401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90729135872142726257633069 34023425952053522346612401)
            ·
              refine ⟨25517569464040141759959301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34023425952053522346612401 25517569464040141759959301)
              ·
                refine ⟨4784544274507526579992369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25517569464040141759959301 4784544274507526579992369)
                ·
                  refine ⟨3588408205880644934994277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4784544274507526579992369 3588408205880644934994277)
                  ·
                    refine ⟨672826538602620925311427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3588408205880644934994277 672826538602620925311427)
                    ·
                      rfl

theorem cell23_3930975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 4].length) (baseStart_3930975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930975 prefixEnd_3930975 := by exact prefixLift 3930975
  have htrace : WordTrace (prefixWord ++ tailWord_3930975) baseStart_3930975 baseEnd_3930975 := by
    simpa [prefixWord, tailWord_3930975, baseEnd_3930975] using wordTrace_append hprefix tailTrace_3930975
  have hstable : (prefixWord ++ tailWord_3930975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930975).length < 2 ^ (prefixWord ++ tailWord_3930975).sum := by decide
  have hdescent : baseEnd_3930975 < baseStart_3930975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930988 : List Nat := [2, 2, 1, 1, 4, 1, 4, 8]
def baseStart_3930988 : Nat := 118140960795 + 3930988 * 2 ^ 59
def prefixEnd_3930988 : Nat := 4983230072969 + 3 ^ 40 * 3930988 * 2
def baseEnd_3930988 : Nat := 74758751520606341669323

theorem tailTrace_3930988 : CollatzResearch.WordTrace tailWord_3930988 prefixEnd_3930988 74758751520606341669323 := by
  unfold tailWord_3930988
  simp only [CollatzResearch.WordTrace]
  refine ⟨71687455541354655072932809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95583274055139540097243745 71687455541354655072932809)
  ·
    refine ⟨53765591656015991304699607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71687455541354655072932809 53765591656015991304699607)
    ·
      refine ⟨80648387484023986957049411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53765591656015991304699607 80648387484023986957049411)
      ·
        refine ⟨120972581226035980435574117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80648387484023986957049411 120972581226035980435574117)
        ·
          refine ⟨22682358979881746331670147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120972581226035980435574117 22682358979881746331670147)
          ·
            refine ⟨34023538469822619497505221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22682358979881746331670147 34023538469822619497505221)
            ·
              refine ⟨6379413463091741155782229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34023538469822619497505221 6379413463091741155782229)
              ·
                refine ⟨74758751520606341669323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6379413463091741155782229 74758751520606341669323)
                ·
                  rfl

theorem cell23_3930988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 8].length) (baseStart_3930988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930988 prefixEnd_3930988 := by exact prefixLift 3930988
  have htrace : WordTrace (prefixWord ++ tailWord_3930988) baseStart_3930988 baseEnd_3930988 := by
    simpa [prefixWord, tailWord_3930988, baseEnd_3930988] using wordTrace_append hprefix tailTrace_3930988
  have hstable : (prefixWord ++ tailWord_3930988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930988).length < 2 ^ (prefixWord ++ tailWord_3930988).sum := by decide
  have hdescent : baseEnd_3930988 < baseStart_3930988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3930992 : List Nat := [2, 1, 1, 1, 4, 1, 6, 1, 2, 4]
def baseStart_3930992 : Nat := 118140960795 + 3930992 * 2 ^ 59
def prefixEnd_3930992 : Nat := 4983230072969 + 3 ^ 40 * 3930992 * 2
def baseEnd_3930992 : Nat := 672829448326329736473901

theorem tailTrace_3930992 : CollatzResearch.WordTrace tailWord_3930992 prefixEnd_3930992 672829448326329736473901 := by
  unfold tailWord_3930992
  simp only [CollatzResearch.WordTrace]
  refine ⟨71687528487347409414505615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95583371316463212552674153 71687528487347409414505615)
  ·
    refine ⟨107531292731021114121758423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71687528487347409414505615 107531292731021114121758423)
    ·
      refine ⟨161296939096531671182637635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107531292731021114121758423 161296939096531671182637635)
      ·
        refine ⟨241945408644797506773956453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161296939096531671182637635 241945408644797506773956453)
        ·
          refine ⟨45364764120899532520116835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241945408644797506773956453 45364764120899532520116835)
          ·
            refine ⟨68047146181349298780175253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45364764120899532520116835 68047146181349298780175253)
            ·
              refine ⟨3189709977250748380320715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68047146181349298780175253 3189709977250748380320715)
              ·
                refine ⟨4784564965876122570481073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3189709977250748380320715 4784564965876122570481073)
                ·
                  refine ⟨3588423724407091927860805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4784564965876122570481073 3588423724407091927860805)
                  ·
                    refine ⟨672829448326329736473901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3588423724407091927860805 672829448326329736473901)
                    ·
                      rfl

theorem cell23_3930992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 2, 4].length) (baseStart_3930992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3930992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3930992 prefixEnd_3930992 := by exact prefixLift 3930992
  have htrace : WordTrace (prefixWord ++ tailWord_3930992) baseStart_3930992 baseEnd_3930992 := by
    simpa [prefixWord, tailWord_3930992, baseEnd_3930992] using wordTrace_append hprefix tailTrace_3930992
  have hstable : (prefixWord ++ tailWord_3930992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3930992).length < 2 ^ (prefixWord ++ tailWord_3930992).sum := by decide
  have hdescent : baseEnd_3930992 < baseStart_3930992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3930992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931015 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 3]
def baseStart_3931015 : Nat := 118140960795 + 3931015 * 2 ^ 59
def prefixEnd_3931015 : Nat := 4983230072969 + 3 ^ 40 * 3931015 * 2
def baseEnd_3931015 : Nat := 2018500155034042619434097

theorem tailTrace_3931015 : CollatzResearch.WordTrace tailWord_3931015 prefixEnd_3931015 2018500155034042619434097 := by
  unfold tailWord_3931015
  simp only [CollatzResearch.WordTrace]
  refine ⟨143375895853611493757098499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95583930569074329171398999 143375895853611493757098499)
  ·
    refine ⟨215063843780417240635647749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143375895853611493757098499 215063843780417240635647749)
    ·
      refine ⟨40324470708828232619183953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215063843780417240635647749 40324470708828232619183953)
      ·
        refine ⟨30243353031621174464387965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40324470708828232619183953 30243353031621174464387965)
        ·
          refine ⟨11341257386857940424145487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30243353031621174464387965 11341257386857940424145487)
          ·
            refine ⟨17011886080286910636218231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11341257386857940424145487 17011886080286910636218231)
            ·
              refine ⟨25517829120430365954327347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17011886080286910636218231 25517829120430365954327347)
              ·
                refine ⟨38276743680645548931491021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25517829120430365954327347 38276743680645548931491021)
                ·
                  refine ⟨14353778880242080849309133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38276743680645548931491021 14353778880242080849309133)
                  ·
                    refine ⟨5382667080090780318490925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14353778880242080849309133 5382667080090780318490925)
                    ·
                      refine ⟨2018500155034042619434097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5382667080090780318490925 2018500155034042619434097)
                      ·
                        rfl

theorem cell23_3931015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_3931015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931015 prefixEnd_3931015 := by exact prefixLift 3931015
  have htrace : WordTrace (prefixWord ++ tailWord_3931015) baseStart_3931015 baseEnd_3931015 := by
    simpa [prefixWord, tailWord_3931015, baseEnd_3931015] using wordTrace_append hprefix tailTrace_3931015
  have hstable : (prefixWord ++ tailWord_3931015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931015).length < 2 ^ (prefixWord ++ tailWord_3931015).sum := by decide
  have hdescent : baseEnd_3931015 < baseStart_3931015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931072 : List Nat := [2, 1, 1, 2, 3, 3, 2, 2, 1, 4, 2]
def baseStart_3931072 : Nat := 118140960795 + 3931072 * 2 ^ 59
def prefixEnd_3931072 : Nat := 4983230072969 + 3 ^ 40 * 3931072 * 2
def baseEnd_3931072 : Nat := 2018529423431348896421335

theorem tailTrace_3931072 : CollatzResearch.WordTrace tailWord_3931072 prefixEnd_3931072 2018529423431348896421335 := by
  unfold tailWord_3931072
  simp only [CollatzResearch.WordTrace]
  refine ⟨71688987407202496245961735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95585316542936661661282313 71688987407202496245961735)
  ·
    refine ⟨107533481110803744368942603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71688987407202496245961735 107533481110803744368942603)
    ·
      refine ⟨161300221666205616553413905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107533481110803744368942603 161300221666205616553413905)
      ·
        refine ⟨120975166249654212415060429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161300221666205616553413905 120975166249654212415060429)
        ·
          refine ⟨45365687343620329655647661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120975166249654212415060429 45365687343620329655647661)
          ·
            refine ⟨17012132753857623620867873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45365687343620329655647661 17012132753857623620867873)
            ·
              refine ⟨12759099565393217715650905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17012132753857623620867873 12759099565393217715650905)
              ·
                refine ⟨9569324674044913286738179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12759099565393217715650905 9569324674044913286738179)
                ·
                  refine ⟨14353987011067369930107269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9569324674044913286738179 14353987011067369930107269)
                  ·
                    refine ⟨2691372564575131861895113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14353987011067369930107269 2691372564575131861895113)
                    ·
                      refine ⟨2018529423431348896421335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2691372564575131861895113 2018529423431348896421335)
                      ·
                        rfl

theorem cell23_3931072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 1, 4, 2].length) (baseStart_3931072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931072 prefixEnd_3931072 := by exact prefixLift 3931072
  have htrace : WordTrace (prefixWord ++ tailWord_3931072) baseStart_3931072 baseEnd_3931072 := by
    simpa [prefixWord, tailWord_3931072, baseEnd_3931072] using wordTrace_append hprefix tailTrace_3931072
  have hstable : (prefixWord ++ tailWord_3931072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931072).length < 2 ^ (prefixWord ++ tailWord_3931072).sum := by decide
  have hdescent : baseEnd_3931072 < baseStart_3931072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931106 : List Nat := [3, 3, 3, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_3931106 : Nat := 118140960795 + 3931106 * 2 ^ 59
def prefixEnd_3931106 : Nat := 4983230072969 + 3 ^ 40 * 3931106 * 2
def baseEnd_3931106 : Nat := 2018546881773601763396179

theorem tailTrace_3931106 : CollatzResearch.WordTrace tailWord_3931106 prefixEnd_3931106 2018546881773601763396179 := by
  unfold tailWord_3931106
  simp only [CollatzResearch.WordTrace]
  refine ⟨35844803724070454074665293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95586143264187877532440781 35844803724070454074665293)
  ·
    refine ⟨13441801396526420277999485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35844803724070454074665293 13441801396526420277999485)
    ·
      refine ⟨5040675523697407604249807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13441801396526420277999485 5040675523697407604249807)
      ·
        refine ⟨7561013285546111406374711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5040675523697407604249807 7561013285546111406374711)
        ·
          refine ⟨11341519928319167109562067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7561013285546111406374711 11341519928319167109562067)
          ·
            refine ⟨17012279892478750664343101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11341519928319167109562067 17012279892478750664343101)
            ·
              refine ⟨6379604959679531499128663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17012279892478750664343101 6379604959679531499128663)
              ·
                refine ⟨9569407439519297248692995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6379604959679531499128663 9569407439519297248692995)
                ·
                  refine ⟨14354111159278945873039493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9569407439519297248692995 14354111159278945873039493)
                  ·
                    refine ⟨2691395842364802351194905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14354111159278945873039493 2691395842364802351194905)
                    ·
                      refine ⟨2018546881773601763396179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2691395842364802351194905 2018546881773601763396179)
                      ·
                        rfl

theorem cell23_3931106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_3931106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931106 prefixEnd_3931106 := by exact prefixLift 3931106
  have htrace : WordTrace (prefixWord ++ tailWord_3931106) baseStart_3931106 baseEnd_3931106 := by
    simpa [prefixWord, tailWord_3931106, baseEnd_3931106] using wordTrace_append hprefix tailTrace_3931106
  have hstable : (prefixWord ++ tailWord_3931106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931106).length < 2 ^ (prefixWord ++ tailWord_3931106).sum := by decide
  have hdescent : baseEnd_3931106 < baseStart_3931106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931162 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2]
def baseStart_3931162 : Nat := 118140960795 + 3931162 * 2 ^ 59
def prefixEnd_3931162 : Nat := 4983230072969 + 3 ^ 40 * 3931162 * 2
def baseEnd_3931162 : Nat := 2018575636690253544295921

theorem tailTrace_3931162 : CollatzResearch.WordTrace tailWord_3931162 prefixEnd_3931162 2018575636690253544295921 := by
  unfold tailWord_3931162
  simp only [CollatzResearch.WordTrace]
  refine ⟨35845314346019734465674935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95587504922719291908466493 35845314346019734465674935)
  ·
    refine ⟨53767971519029601698512403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35845314346019734465674935 53767971519029601698512403)
    ·
      refine ⟨80651957278544402547768605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53767971519029601698512403 80651957278544402547768605)
      ·
        refine ⟨30244483979454150955413227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80651957278544402547768605 30244483979454150955413227)
        ·
          refine ⟨45366725969181226433119841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30244483979454150955413227 45366725969181226433119841)
          ·
            refine ⟨34025044476885919824839881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45366725969181226433119841 34025044476885919824839881)
            ·
              refine ⟨25518783357664439868629911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34025044476885919824839881 25518783357664439868629911)
              ·
                refine ⟨38278175036496659802944867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25518783357664439868629911 38278175036496659802944867)
                ·
                  refine ⟨57417262554744989704417301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38278175036496659802944867 57417262554744989704417301)
                  ·
                    refine ⟨2691434182253671392394561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57417262554744989704417301 2691434182253671392394561)
                    ·
                      refine ⟨2018575636690253544295921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2691434182253671392394561 2018575636690253544295921)
                      ·
                        rfl

theorem cell23_3931162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_3931162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931162 prefixEnd_3931162 := by exact prefixLift 3931162
  have htrace : WordTrace (prefixWord ++ tailWord_3931162) baseStart_3931162 baseEnd_3931162 := by
    simpa [prefixWord, tailWord_3931162, baseEnd_3931162] using wordTrace_append hprefix tailTrace_3931162
  have hstable : (prefixWord ++ tailWord_3931162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931162).length < 2 ^ (prefixWord ++ tailWord_3931162).sum := by decide
  have hdescent : baseEnd_3931162 < baseStart_3931162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931189 : List Nat := [1, 3, 3, 1, 1, 1, 1, 7, 1, 4]
def baseStart_3931189 : Nat := 118140960795 + 3931189 * 2 ^ 59
def prefixEnd_3931189 : Nat := 4983230072969 + 3 ^ 40 * 3931189 * 2
def baseEnd_3931189 : Nat := 672863166889308312886099

theorem tailTrace_3931189 : CollatzResearch.WordTrace tailWord_3931189 prefixEnd_3931189 672863166889308312886099 := by
  unfold tailWord_3931189
  simp only [CollatzResearch.WordTrace]
  refine ⟨143382242154981121473932621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95588161436654080982621747 143382242154981121473932621)
  ·
    refine ⟨53768340808117920552724733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143382242154981121473932621 53768340808117920552724733)
    ·
      refine ⟨20163127803044220207271775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53768340808117920552724733 20163127803044220207271775)
      ·
        refine ⟨30244691704566330310907663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20163127803044220207271775 30244691704566330310907663)
        ·
          refine ⟨45367037556849495466361495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30244691704566330310907663 45367037556849495466361495)
          ·
            refine ⟨68050556335274243199542243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45367037556849495466361495 68050556335274243199542243)
            ·
              refine ⟨102075834502911364799313365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68050556335274243199542243 102075834502911364799313365)
              ·
                refine ⟨2392402371161985112483907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 102075834502911364799313365 2392402371161985112483907)
                ·
                  refine ⟨3588603556742977668725861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2392402371161985112483907 3588603556742977668725861)
                  ·
                    refine ⟨672863166889308312886099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3588603556742977668725861 672863166889308312886099)
                    ·
                      rfl

theorem cell23_3931189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_3931189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931189 prefixEnd_3931189 := by exact prefixLift 3931189
  have htrace : WordTrace (prefixWord ++ tailWord_3931189) baseStart_3931189 baseEnd_3931189 := by
    simpa [prefixWord, tailWord_3931189, baseEnd_3931189] using wordTrace_append hprefix tailTrace_3931189
  have hstable : (prefixWord ++ tailWord_3931189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931189).length < 2 ^ (prefixWord ++ tailWord_3931189).sum := by decide
  have hdescent : baseEnd_3931189 < baseStart_3931189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931232 : List Nat := [2, 1, 1, 3, 2, 2, 2, 4, 1, 5]
def baseStart_3931232 : Nat := 118140960795 + 3931232 * 2 ^ 59
def prefixEnd_3931232 : Nat := 4983230072969 + 3 ^ 40 * 3931232 * 2
def baseEnd_3931232 : Nat := 672870526778689423473533

theorem tailTrace_3931232 : CollatzResearch.WordTrace tailWord_3931232 prefixEnd_3931232 672870526778689423473533 := by
  unfold tailWord_3931232
  simp only [CollatzResearch.WordTrace]
  refine ⟨71691905246912669908873975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95589206995883559878498633 71691905246912669908873975)
  ·
    refine ⟨107537857870369004863310963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71691905246912669908873975 107537857870369004863310963)
    ·
      refine ⟨161306786805553507294966445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107537857870369004863310963 161306786805553507294966445)
      ·
        refine ⟨60490045052082565235612417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161306786805553507294966445 60490045052082565235612417)
        ·
          refine ⟨45367533789061923926709313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60490045052082565235612417 45367533789061923926709313)
          ·
            refine ⟨34025650341796442945031985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45367533789061923926709313 34025650341796442945031985)
            ·
              refine ⟨25519237756347332208773989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34025650341796442945031985 25519237756347332208773989)
              ·
                refine ⟨4784857079315124789145123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25519237756347332208773989 4784857079315124789145123)
                ·
                  refine ⟨7177285618972687183717685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4784857079315124789145123 7177285618972687183717685)
                  ·
                    refine ⟨672870526778689423473533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7177285618972687183717685 672870526778689423473533)
                    ·
                      rfl

theorem cell23_3931232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 1, 5].length) (baseStart_3931232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931232 prefixEnd_3931232 := by exact prefixLift 3931232
  have htrace : WordTrace (prefixWord ++ tailWord_3931232) baseStart_3931232 baseEnd_3931232 := by
    simpa [prefixWord, tailWord_3931232, baseEnd_3931232] using wordTrace_append hprefix tailTrace_3931232
  have hstable : (prefixWord ++ tailWord_3931232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931232).length < 2 ^ (prefixWord ++ tailWord_3931232).sum := by decide
  have hdescent : baseEnd_3931232 < baseStart_3931232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931239 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 1, 5, 2]
def baseStart_3931239 : Nat := 118140960795 + 3931239 * 2 ^ 59
def prefixEnd_3931239 : Nat := 4983230072969 + 3 ^ 40 * 3931239 * 2
def baseEnd_3931239 : Nat := 2018615174700649743033067

theorem tailTrace_3931239 : CollatzResearch.WordTrace tailWord_3931239 prefixEnd_3931239 2018615174700649743033067 := by
  unfold tailWord_3931239
  simp only [CollatzResearch.WordTrace]
  refine ⟨143384065804799980013252771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95589377203199986675501847 143384065804799980013252771)
  ·
    refine ⟨215076098707199970019879157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143384065804799980013252771 215076098707199970019879157)
    ·
      refine ⟨20163384253799997189363671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215076098707199970019879157 20163384253799997189363671)
      ·
        refine ⟨30245076380699995784045507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20163384253799997189363671 30245076380699995784045507)
        ·
          refine ⟨45367614571049993676068261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30245076380699995784045507 45367614571049993676068261)
          ·
            refine ⟨8506427732071873814262799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45367614571049993676068261 8506427732071873814262799)
            ·
              refine ⟨12759641598107810721394199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8506427732071873814262799 12759641598107810721394199)
              ·
                refine ⟨19139462397161716082091299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12759641598107810721394199 19139462397161716082091299)
                ·
                  refine ⟨28709193595742574123136949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19139462397161716082091299 28709193595742574123136949)
                  ·
                    refine ⟨2691486899600866324044089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28709193595742574123136949 2691486899600866324044089)
                    ·
                      refine ⟨2018615174700649743033067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2691486899600866324044089 2018615174700649743033067)
                      ·
                        rfl

theorem cell23_3931239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_3931239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931239 prefixEnd_3931239 := by exact prefixLift 3931239
  have htrace : WordTrace (prefixWord ++ tailWord_3931239) baseStart_3931239 baseEnd_3931239 := by
    simpa [prefixWord, tailWord_3931239, baseEnd_3931239] using wordTrace_append hprefix tailTrace_3931239
  have hstable : (prefixWord ++ tailWord_3931239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931239).length < 2 ^ (prefixWord ++ tailWord_3931239).sum := by decide
  have hdescent : baseEnd_3931239 < baseStart_3931239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931253 : List Nat := [1, 3, 4, 3, 2, 1, 1, 2, 6]
def baseStart_3931253 : Nat := 118140960795 + 3931253 * 2 ^ 59
def prefixEnd_3931253 : Nat := 4983230072969 + 3 ^ 40 * 3931253 * 2
def baseEnd_3931253 : Nat := 224291373714423632028667

theorem tailTrace_3931253 : CollatzResearch.WordTrace tailWord_3931253 prefixEnd_3931253 224291373714423632028667 := by
  unfold tailWord_3931253
  simp only [CollatzResearch.WordTrace]
  refine ⟨143384576426749260404262413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95589717617832840269508275 143384576426749260404262413)
  ·
    refine ⟨53769216160030972651598405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143384576426749260404262413 53769216160030972651598405)
    ·
      refine ⟨10081728030005807372174701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53769216160030972651598405 10081728030005807372174701)
      ·
        refine ⟨3780648011252177764565513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10081728030005807372174701 3780648011252177764565513)
        ·
          refine ⟨2835486008439133323424135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3780648011252177764565513 2835486008439133323424135)
          ·
            refine ⟨4253229012658699985136203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2835486008439133323424135 4253229012658699985136203)
            ·
              refine ⟨6379843518988049977704305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4253229012658699985136203 6379843518988049977704305)
              ·
                refine ⟨4784882639241037483278229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6379843518988049977704305 4784882639241037483278229)
                ·
                  refine ⟨224291373714423632028667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4784882639241037483278229 224291373714423632028667)
                  ·
                    rfl

theorem cell23_3931253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 6].length) (baseStart_3931253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931253 prefixEnd_3931253 := by exact prefixLift 3931253
  have htrace : WordTrace (prefixWord ++ tailWord_3931253) baseStart_3931253 baseEnd_3931253 := by
    simpa [prefixWord, tailWord_3931253, baseEnd_3931253] using wordTrace_append hprefix tailTrace_3931253
  have hstable : (prefixWord ++ tailWord_3931253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931253).length < 2 ^ (prefixWord ++ tailWord_3931253).sum := by decide
  have hdescent : baseEnd_3931253 < baseStart_3931253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931292 : List Nat := [2, 2, 3, 2, 1, 3, 1, 9]
def baseStart_3931292 : Nat := 118140960795 + 3931292 * 2 ^ 59
def prefixEnd_3931292 : Nat := 4983230072969 + 3 ^ 40 * 3931292 * 2
def baseEnd_3931292 : Nat := 74764532932419927247049

theorem tailTrace_3931292 : CollatzResearch.WordTrace tailWord_3931292 prefixEnd_3931292 74764532932419927247049 := by
  unfold tailWord_3931292
  simp only [CollatzResearch.WordTrace]
  refine ⟨71692999436803985032466065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95590665915738646709954753 71692999436803985032466065)
  ·
    refine ⟨53769749577602988774349549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71692999436803985032466065 53769749577602988774349549)
    ·
      refine ⟨20163656091601120790381081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53769749577602988774349549 20163656091601120790381081)
      ·
        refine ⟨15122742068700840592785811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20163656091601120790381081 15122742068700840592785811)
        ·
          refine ⟨22684113103051260889178717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15122742068700840592785811 22684113103051260889178717)
          ·
            refine ⟨8506542413644222833442019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22684113103051260889178717 8506542413644222833442019)
            ·
              refine ⟨12759813620466334250163029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8506542413644222833442019 12759813620466334250163029)
              ·
                refine ⟨74764532932419927247049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12759813620466334250163029 74764532932419927247049)
                ·
                  rfl

theorem cell23_3931292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 9].length) (baseStart_3931292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931292 prefixEnd_3931292 := by exact prefixLift 3931292
  have htrace : WordTrace (prefixWord ++ tailWord_3931292) baseStart_3931292 baseEnd_3931292 := by
    simpa [prefixWord, tailWord_3931292, baseEnd_3931292] using wordTrace_append hprefix tailTrace_3931292
  have hstable : (prefixWord ++ tailWord_3931292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931292).length < 2 ^ (prefixWord ++ tailWord_3931292).sum := by decide
  have hdescent : baseEnd_3931292 < baseStart_3931292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931305 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 6, 7]
def baseStart_3931305 : Nat := 118140960795 + 3931305 * 2 ^ 59
def prefixEnd_3931305 : Nat := 4983230072969 + 3 ^ 40 * 3931305 * 2
def baseEnd_3931305 : Nat := 672883021474615494935921

theorem tailTrace_3931305 : CollatzResearch.WordTrace tailWord_3931305 prefixEnd_3931305 672883021474615494935921 := by
  unfold tailWord_3931305
  simp only [CollatzResearch.WordTrace]
  refine ⟨143386473022560873285155369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95590982015040582190103579 143386473022560873285155369)
  ·
    refine ⟨107539854766920654963866527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143386473022560873285155369 107539854766920654963866527)
    ·
      refine ⟨161309782150380982445799791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107539854766920654963866527 161309782150380982445799791)
      ·
        refine ⟨241964673225571473668699687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161309782150380982445799791 241964673225571473668699687)
        ·
          refine ⟨362947009838357210503049531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241964673225571473668699687 362947009838357210503049531)
          ·
            refine ⟨544420514757535815754574297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362947009838357210503049531 544420514757535815754574297)
            ·
              refine ⟨408315386068151861815930723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544420514757535815754574297 408315386068151861815930723)
              ·
                refine ⟨612473079102227792723896085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408315386068151861815930723 612473079102227792723896085)
                ·
                  refine ⟨28709675582916927783932629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 612473079102227792723896085 28709675582916927783932629)
                  ·
                    refine ⟨672883021474615494935921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28709675582916927783932629 672883021474615494935921)
                    ·
                      rfl

theorem cell23_3931305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 7].length) (baseStart_3931305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931305 prefixEnd_3931305 := by exact prefixLift 3931305
  have htrace : WordTrace (prefixWord ++ tailWord_3931305) baseStart_3931305 baseEnd_3931305 := by
    simpa [prefixWord, tailWord_3931305, baseEnd_3931305] using wordTrace_append hprefix tailTrace_3931305
  have hstable : (prefixWord ++ tailWord_3931305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931305).length < 2 ^ (prefixWord ++ tailWord_3931305).sum := by decide
  have hdescent : baseEnd_3931305 < baseStart_3931305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931306 : List Nat := [3, 1, 5, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_3931306 : Nat := 118140960795 + 3931306 * 2 ^ 59
def prefixEnd_3931306 : Nat := 4983230072969 + 3 ^ 40 * 3931306 * 2
def baseEnd_3931306 : Nat := 2018649577904500980895259

theorem tailTrace_3931306 : CollatzResearch.WordTrace tailWord_3931306 prefixEnd_3931306 2018649577904500980895259 := by
  unfold tailWord_3931306
  simp only [CollatzResearch.WordTrace]
  refine ⟨35846627373889312613985443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95591006330371500303961181 35846627373889312613985443)
  ·
    refine ⟨53769941060833968920978165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35846627373889312613985443 53769941060833968920978165)
    ·
      refine ⟨5040931974453184586341703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53769941060833968920978165 5040931974453184586341703)
      ·
        refine ⟨7561397961679776879512555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5040931974453184586341703 7561397961679776879512555)
        ·
          refine ⟨11342096942519665319268833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7561397961679776879512555 11342096942519665319268833)
          ·
            refine ⟨8506572706889748989451625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11342096942519665319268833 8506572706889748989451625)
            ·
              refine ⟨6379929530167311742088719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8506572706889748989451625 6379929530167311742088719)
              ·
                refine ⟨9569894295250967613133079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6379929530167311742088719 9569894295250967613133079)
                ·
                  refine ⟨14354841442876451419699619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9569894295250967613133079 14354841442876451419699619)
                  ·
                    refine ⟨21532262164314677129549429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14354841442876451419699619 21532262164314677129549429)
                    ·
                      refine ⟨2018649577904500980895259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21532262164314677129549429 2018649577904500980895259)
                      ·
                        rfl

theorem cell23_3931306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_3931306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931306 prefixEnd_3931306 := by exact prefixLift 3931306
  have htrace : WordTrace (prefixWord ++ tailWord_3931306) baseStart_3931306 baseEnd_3931306 := by
    simpa [prefixWord, tailWord_3931306, baseEnd_3931306] using wordTrace_append hprefix tailTrace_3931306
  have hstable : (prefixWord ++ tailWord_3931306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931306).length < 2 ^ (prefixWord ++ tailWord_3931306).sum := by decide
  have hdescent : baseEnd_3931306 < baseStart_3931306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931309 : List Nat := [1, 5, 2, 1, 3, 2, 9]
def baseStart_3931309 : Nat := 118140960795 + 3931309 * 2 ^ 59
def prefixEnd_3931309 : Nat := 4983230072969 + 3 ^ 40 * 3931309 * 2
def baseEnd_3931309 : Nat := 24921618745018079866145

theorem tailTrace_3931309 : CollatzResearch.WordTrace tailWord_3931309 prefixEnd_3931309 24921618745018079866145 := by
  unfold tailWord_3931309
  simp only [CollatzResearch.WordTrace]
  refine ⟨143386618914546381968300981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95591079276364254645533987 143386618914546381968300981)
  ·
    refine ⟨13442495523238723309528217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143386618914546381968300981 13442495523238723309528217)
    ·
      refine ⟨10081871642429042482146163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13442495523238723309528217 10081871642429042482146163)
      ·
        refine ⟨15122807463643563723219245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10081871642429042482146163 15122807463643563723219245)
        ·
          refine ⟨5671052798866336396207217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15122807463643563723219245 5671052798866336396207217)
          ·
            refine ⟨4253289599149752297155413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5671052798866336396207217 4253289599149752297155413)
            ·
              refine ⟨24921618745018079866145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4253289599149752297155413 24921618745018079866145)
              ·
                rfl

theorem cell23_3931309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 9].length) (baseStart_3931309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931309 prefixEnd_3931309 := by exact prefixLift 3931309
  have htrace : WordTrace (prefixWord ++ tailWord_3931309) baseStart_3931309 baseEnd_3931309 := by
    simpa [prefixWord, tailWord_3931309, baseEnd_3931309] using wordTrace_append hprefix tailTrace_3931309
  have hstable : (prefixWord ++ tailWord_3931309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931309).length < 2 ^ (prefixWord ++ tailWord_3931309).sum := by decide
  have hdescent : baseEnd_3931309 < baseStart_3931309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931319 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 4, 1, 3]
def baseStart_3931319 : Nat := 118140960795 + 3931319 * 2 ^ 59
def prefixEnd_3931319 : Nat := 4983230072969 + 3 ^ 40 * 3931319 * 2
def baseEnd_3931319 : Nat := 2018656253153009430032699

theorem tailTrace_3931319 : CollatzResearch.WordTrace tailWord_3931319 prefixEnd_3931319 2018656253153009430032699 := by
  unfold tailWord_3931319
  simp only [CollatzResearch.WordTrace]
  refine ⟨143386983644510153676165011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95591322429673435784110007 143386983644510153676165011)
  ·
    refine ⟨215080475466765230514247517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143386983644510153676165011 215080475466765230514247517)
    ·
      refine ⟨80655178300036961442842819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215080475466765230514247517 80655178300036961442842819)
      ·
        refine ⟨120982767450055442164264229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80655178300036961442842819 120982767450055442164264229)
        ·
          refine ⟨22684268896885395405799543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120982767450055442164264229 22684268896885395405799543)
          ·
            refine ⟨34026403345328093108699315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22684268896885395405799543 34026403345328093108699315)
            ·
              refine ⟨51039605017992139663048973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34026403345328093108699315 51039605017992139663048973)
              ·
                refine ⟨19139851881747052373643365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51039605017992139663048973 19139851881747052373643365)
                ·
                  refine ⟨3588722227827572320058131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19139851881747052373643365 3588722227827572320058131)
                  ·
                    refine ⟨5383083341741358480087197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3588722227827572320058131 5383083341741358480087197)
                    ·
                      refine ⟨2018656253153009430032699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5383083341741358480087197 2018656253153009430032699)
                      ·
                        rfl

theorem cell23_3931319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 1, 3].length) (baseStart_3931319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931319 prefixEnd_3931319 := by exact prefixLift 3931319
  have htrace : WordTrace (prefixWord ++ tailWord_3931319) baseStart_3931319 baseEnd_3931319 := by
    simpa [prefixWord, tailWord_3931319, baseEnd_3931319] using wordTrace_append hprefix tailTrace_3931319
  have hstable : (prefixWord ++ tailWord_3931319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931319).length < 2 ^ (prefixWord ++ tailWord_3931319).sum := by decide
  have hdescent : baseEnd_3931319 < baseStart_3931319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931330 : List Nat := [3, 5, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_3931330 : Nat := 118140960795 + 3931330 * 2 ^ 59
def prefixEnd_3931330 : Nat := 4983230072969 + 3 ^ 40 * 3931330 * 2
def baseEnd_3931330 : Nat := 672887300480069628998383

theorem tailTrace_3931330 : CollatzResearch.WordTrace tailWord_3931330 prefixEnd_3931330 672887300480069628998383 := by
  unfold tailWord_3931330
  simp only [CollatzResearch.WordTrace]
  refine ⟨35846846211867575638703861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95591589898313535036543629 35846846211867575638703861)
  ·
    refine ⟨3360641832362585216128487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35846846211867575638703861 3360641832362585216128487)
    ·
      refine ⟨5040962748543877824192731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3360641832362585216128487 5040962748543877824192731)
      ·
        refine ⟨7561444122815816736289097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5040962748543877824192731 7561444122815816736289097)
        ·
          refine ⟨5671083092111862552216823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7561444122815816736289097 5671083092111862552216823)
          ·
            refine ⟨8506624638167793828325235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5671083092111862552216823 8506624638167793828325235)
            ·
              refine ⟨12759936957251690742487853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8506624638167793828325235 12759936957251690742487853)
              ·
                refine ⟨4784976358969384028432945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12759936957251690742487853 4784976358969384028432945)
                ·
                  refine ⟨3588732269227038021324709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4784976358969384028432945 3588732269227038021324709)
                  ·
                    refine ⟨672887300480069628998383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3588732269227038021324709 672887300480069628998383)
                    ·
                      rfl

theorem cell23_3931330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_3931330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931330 prefixEnd_3931330 := by exact prefixLift 3931330
  have htrace : WordTrace (prefixWord ++ tailWord_3931330) baseStart_3931330 baseEnd_3931330 := by
    simpa [prefixWord, tailWord_3931330, baseEnd_3931330] using wordTrace_append hprefix tailTrace_3931330
  have hstable : (prefixWord ++ tailWord_3931330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931330).length < 2 ^ (prefixWord ++ tailWord_3931330).sum := by decide
  have hdescent : baseEnd_3931330 < baseStart_3931330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931346 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 3, 3, 2]
def baseStart_3931346 : Nat := 118140960795 + 3931346 * 2 ^ 59
def prefixEnd_3931346 : Nat := 4983230072969 + 3 ^ 40 * 3931346 * 2
def baseEnd_3931346 : Nat := 2018670117130680824395075

theorem tailTrace_3931346 : CollatzResearch.WordTrace tailWord_3931346 prefixEnd_3931346 2018670117130680824395075 := by
  unfold tailWord_3931346
  simp only [CollatzResearch.WordTrace]
  refine ⟨35846992103853084321849473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95591978943608224858265261 35846992103853084321849473)
  ·
    refine ⟨26885244077889813241387105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35846992103853084321849473 26885244077889813241387105)
    ·
      refine ⟨20163933058417359931040329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26885244077889813241387105 20163933058417359931040329)
      ·
        refine ⟨15122949793813019948280247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20163933058417359931040329 15122949793813019948280247)
        ·
          refine ⟨22684424690719529922420371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15122949793813019948280247 22684424690719529922420371)
          ·
            refine ⟨34026637036079294883630557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22684424690719529922420371 34026637036079294883630557)
            ·
              refine ⟨12759988888529735581361459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34026637036079294883630557 12759988888529735581361459)
              ·
                refine ⟨19139983332794603372042189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12759988888529735581361459 19139983332794603372042189)
                ·
                  refine ⟨7177493749797976264515821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19139983332794603372042189 7177493749797976264515821)
                  ·
                    refine ⟨2691560156174241099193433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7177493749797976264515821 2691560156174241099193433)
                    ·
                      refine ⟨2018670117130680824395075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2691560156174241099193433 2018670117130680824395075)
                      ·
                        rfl

theorem cell23_3931346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_3931346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931346 prefixEnd_3931346 := by exact prefixLift 3931346
  have htrace : WordTrace (prefixWord ++ tailWord_3931346) baseStart_3931346 baseEnd_3931346 := by
    simpa [prefixWord, tailWord_3931346, baseEnd_3931346] using wordTrace_append hprefix tailTrace_3931346
  have hstable : (prefixWord ++ tailWord_3931346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931346).length < 2 ^ (prefixWord ++ tailWord_3931346).sum := by decide
  have hdescent : baseEnd_3931346 < baseStart_3931346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931359 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 3, 4, 2]
def baseStart_3931359 : Nat := 118140960795 + 3931359 * 2 ^ 59
def prefixEnd_3931359 : Nat := 4983230072969 + 3 ^ 40 * 3931359 * 2
def baseEnd_3931359 : Nat := 2018676792379189273532515

theorem tailTrace_3931359 : CollatzResearch.WordTrace tailWord_3931359 prefixEnd_3931359 2018676792379189273532515 := by
  unfold tailWord_3931359
  simp only [CollatzResearch.WordTrace]
  refine ⟨143388442564365240507621131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95592295042910160338414087 143388442564365240507621131)
  ·
    refine ⟨215082663846547860761431697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143388442564365240507621131 215082663846547860761431697)
    ·
      refine ⟨161311997884910895571073773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215082663846547860761431697 161311997884910895571073773)
      ·
        refine ⟨60491999206841585839152665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161311997884910895571073773 60491999206841585839152665)
        ·
          refine ⟨45368999405131189379364499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60491999206841585839152665 45368999405131189379364499)
          ·
            refine ⟨68053499107696784069046749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45368999405131189379364499 68053499107696784069046749)
            ·
              refine ⟨25520062165386294025892531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68053499107696784069046749 25520062165386294025892531)
              ·
                refine ⟨38280093248079441038838797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25520062165386294025892531 38280093248079441038838797)
                ·
                  refine ⟨14355034968029790389564549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38280093248079441038838797 14355034968029790389564549)
                  ·
                    refine ⟨2691569056505585698043353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14355034968029790389564549 2691569056505585698043353)
                    ·
                      refine ⟨2018676792379189273532515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2691569056505585698043353 2018676792379189273532515)
                      ·
                        rfl

theorem cell23_3931359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_3931359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931359 prefixEnd_3931359 := by exact prefixLift 3931359
  have htrace : WordTrace (prefixWord ++ tailWord_3931359) baseStart_3931359 baseEnd_3931359 := by
    simpa [prefixWord, tailWord_3931359, baseEnd_3931359] using wordTrace_append hprefix tailTrace_3931359
  have hstable : (prefixWord ++ tailWord_3931359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931359).length < 2 ^ (prefixWord ++ tailWord_3931359).sum := by decide
  have hdescent : baseEnd_3931359 < baseStart_3931359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931393 : List Nat := [1, 2, 4, 1, 1, 3, 2, 3, 2, 2, 2]
def baseStart_3931393 : Nat := 118140960795 + 3931393 * 2 ^ 59
def prefixEnd_3931393 : Nat := 4983230072969 + 3 ^ 40 * 3931393 * 2
def baseEnd_3931393 : Nat := 2018694250721442140507359

theorem tailTrace_3931393 : CollatzResearch.WordTrace tailWord_3931393 prefixEnd_3931393 2018694250721442140507359 := by
  unfold tailWord_3931393
  simp only [CollatzResearch.WordTrace]
  refine ⟨143389682646242064314358833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95593121764161376209572555 143389682646242064314358833)
  ·
    refine ⟨107542261984681548235769125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143389682646242064314358833 107542261984681548235769125)
    ·
      refine ⟨20164174122127790294206711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107542261984681548235769125 20164174122127790294206711)
      ·
        refine ⟨30246261183191685441310067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20164174122127790294206711 30246261183191685441310067)
        ·
          refine ⟨45369391774787528161965101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30246261183191685441310067 45369391774787528161965101)
          ·
            refine ⟨17013521915545323060736913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45369391774787528161965101 17013521915545323060736913)
            ·
              refine ⟨12760141436658992295552685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17013521915545323060736913 12760141436658992295552685)
              ·
                refine ⟨4785053038747122110832257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12760141436658992295552685 4785053038747122110832257)
                ·
                  refine ⟨3588789779060341583124193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4785053038747122110832257 3588789779060341583124193)
                  ·
                    refine ⟨2691592334295256187343145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3588789779060341583124193 2691592334295256187343145)
                    ·
                      refine ⟨2018694250721442140507359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2691592334295256187343145 2018694250721442140507359)
                      ·
                        rfl

theorem cell23_3931393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_3931393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931393 prefixEnd_3931393 := by exact prefixLift 3931393
  have htrace : WordTrace (prefixWord ++ tailWord_3931393) baseStart_3931393 baseEnd_3931393 := by
    simpa [prefixWord, tailWord_3931393, baseEnd_3931393] using wordTrace_append hprefix tailTrace_3931393
  have hstable : (prefixWord ++ tailWord_3931393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931393).length < 2 ^ (prefixWord ++ tailWord_3931393).sum := by decide
  have hdescent : baseEnd_3931393 < baseStart_3931393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931416 : List Nat := [2, 1, 2, 3, 1, 4, 2, 3, 5]
def baseStart_3931416 : Nat := 118140960795 + 3931416 * 2 ^ 59
def prefixEnd_3931416 : Nat := 4983230072969 + 3 ^ 40 * 3931416 * 2
def baseEnd_3931416 : Nat := 224300673419610616724417

theorem tailTrace_3931416 : CollatzResearch.WordTrace tailWord_3931416 prefixEnd_3931416 224300673419610616724417 := by
  unfold tailWord_3931416
  simp only [CollatzResearch.WordTrace]
  refine ⟨71695260762579369621223051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95593681016772492828297401 71695260762579369621223051)
  ·
    refine ⟨107542891143869054431834577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71695260762579369621223051 107542891143869054431834577)
    ·
      refine ⟨80657168357901790823875933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107542891143869054431834577 80657168357901790823875933)
      ·
        refine ⟨30246438134213171558953475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80657168357901790823875933 30246438134213171558953475)
        ·
          refine ⟨45369657201319757338430213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30246438134213171558953475 45369657201319757338430213)
          ·
            refine ⟨8506810725247454500955665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45369657201319757338430213 8506810725247454500955665)
            ·
              refine ⟨6380108043935590875716749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8506810725247454500955665 6380108043935590875716749)
              ·
                refine ⟨2392540516475846578393781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6380108043935590875716749 2392540516475846578393781)
                ·
                  refine ⟨224300673419610616724417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2392540516475846578393781 224300673419610616724417)
                  ·
                    rfl

theorem cell23_3931416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 5].length) (baseStart_3931416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931416 prefixEnd_3931416 := by exact prefixLift 3931416
  have htrace : WordTrace (prefixWord ++ tailWord_3931416) baseStart_3931416 baseEnd_3931416 := by
    simpa [prefixWord, tailWord_3931416, baseEnd_3931416] using wordTrace_append hprefix tailTrace_3931416
  have hstable : (prefixWord ++ tailWord_3931416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931416).length < 2 ^ (prefixWord ++ tailWord_3931416).sum := by decide
  have hdescent : baseEnd_3931416 < baseStart_3931416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931472 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 10]
def baseStart_3931472 : Nat := 118140960795 + 3931472 * 2 ^ 59
def prefixEnd_3931472 : Nat := 4983230072969 + 3 ^ 40 * 3931472 * 2
def baseEnd_3931472 : Nat := 224303868410349703491055

theorem tailTrace_3931472 : CollatzResearch.WordTrace tailWord_3931472 prefixEnd_3931472 224303868410349703491055 := by
  unfold tailWord_3931472
  simp only [CollatzResearch.WordTrace]
  refine ⟨71696282006477930403242335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95595042675303907204323113 71696282006477930403242335)
  ·
    refine ⟨107544423009716895604863503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71696282006477930403242335 107544423009716895604863503)
    ·
      refine ⟨161316634514575343407295255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107544423009716895604863503 161316634514575343407295255)
      ·
        refine ⟨241974951771863015110942883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161316634514575343407295255 241974951771863015110942883)
        ·
          refine ⟨362962427657794522666414325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241974951771863015110942883 362962427657794522666414325)
          ·
            refine ⟨34027727592918236499976343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 362962427657794522666414325 34027727592918236499976343)
            ·
              refine ⟨51041591389377354749964515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34027727592918236499976343 51041591389377354749964515)
              ·
                refine ⟨76562387084066032124946773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51041591389377354749964515 76562387084066032124946773)
                ·
                  refine ⟨224303868410349703491055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 76562387084066032124946773 224303868410349703491055)
                  ·
                    rfl

theorem cell23_3931472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 10].length) (baseStart_3931472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931472 prefixEnd_3931472 := by exact prefixLift 3931472
  have htrace : WordTrace (prefixWord ++ tailWord_3931472) baseStart_3931472 baseEnd_3931472 := by
    simpa [prefixWord, tailWord_3931472, baseEnd_3931472] using wordTrace_append hprefix tailTrace_3931472
  have hstable : (prefixWord ++ tailWord_3931472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931472).length < 2 ^ (prefixWord ++ tailWord_3931472).sum := by decide
  have hdescent : baseEnd_3931472 < baseStart_3931472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931516 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 5, 1, 3]
def baseStart_3931516 : Nat := 118140960795 + 3931516 * 2 ^ 59
def prefixEnd_3931516 : Nat := 4983230072969 + 3 ^ 40 * 3931516 * 2
def baseEnd_3931516 : Nat := 2018757408841945159269293

theorem tailTrace_3931516 : CollatzResearch.WordTrace tailWord_3931516 prefixEnd_3931516 2018757408841945159269293 := by
  unfold tailWord_3931516
  simp only [CollatzResearch.WordTrace]
  refine ⟨71697084412398228160543201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95596112549864304214057601 71697084412398228160543201)
  ·
    refine ⟨53772813309298671120407401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71697084412398228160543201 53772813309298671120407401)
    ·
      refine ⟨40329609981974003340305551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53772813309298671120407401 40329609981974003340305551)
      ·
        refine ⟨60494414972961005010458327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40329609981974003340305551 60494414972961005010458327)
        ·
          refine ⟨90741622459441507515687491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60494414972961005010458327 90741622459441507515687491)
          ·
            refine ⟨136112433689162261273531237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90741622459441507515687491 136112433689162261273531237)
            ·
              refine ⟨25521081316717923988787107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136112433689162261273531237 25521081316717923988787107)
              ·
                refine ⟨38281621975076885983180661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25521081316717923988787107 38281621975076885983180661)
                ·
                  refine ⟨3588902060163458060923187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38281621975076885983180661 3588902060163458060923187)
                  ·
                    refine ⟨5383353090245187091384781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3588902060163458060923187 5383353090245187091384781)
                    ·
                      refine ⟨2018757408841945159269293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5383353090245187091384781 2018757408841945159269293)
                      ·
                        rfl

theorem cell23_3931516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_3931516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931516 prefixEnd_3931516 := by exact prefixLift 3931516
  have htrace : WordTrace (prefixWord ++ tailWord_3931516) baseStart_3931516 baseEnd_3931516 := by
    simpa [prefixWord, tailWord_3931516, baseEnd_3931516] using wordTrace_append hprefix tailTrace_3931516
  have hstable : (prefixWord ++ tailWord_3931516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931516).length < 2 ^ (prefixWord ++ tailWord_3931516).sum := by decide
  have hdescent : baseEnd_3931516 < baseStart_3931516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931544 : List Nat := [2, 1, 2, 5, 3, 1, 2, 2, 1, 4]
def baseStart_3931544 : Nat := 118140960795 + 3931544 * 2 ^ 59
def prefixEnd_3931544 : Nat := 4983230072969 + 3 ^ 40 * 3931544 * 2
def baseEnd_3931544 : Nat := 672923928766757016573055

theorem tailTrace_3931544 : CollatzResearch.WordTrace tailWord_3931544 prefixEnd_3931544 672923928766757016573055 := by
  unfold tailWord_3931544
  simp only [CollatzResearch.WordTrace]
  refine ⟨71697595034347508551552843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95596793379130011402070457 71697595034347508551552843)
  ·
    refine ⟨107546392551521262827329265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71697595034347508551552843 107546392551521262827329265)
    ·
      refine ⟨80659794413640947120496949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107546392551521262827329265 80659794413640947120496949)
      ·
        refine ⟨7561855726278838792546589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80659794413640947120496949 7561855726278838792546589)
        ·
          refine ⟨2835695897354564547204971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7561855726278838792546589 2835695897354564547204971)
          ·
            refine ⟨4253543846031846820807457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2835695897354564547204971 4253543846031846820807457)
            ·
              refine ⟨3190157884523885115605593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4253543846031846820807457 3190157884523885115605593)
              ·
                refine ⟨2392618413392913836704195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3190157884523885115605593 2392618413392913836704195)
                ·
                  refine ⟨3588927620089370755056293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2392618413392913836704195 3588927620089370755056293)
                  ·
                    refine ⟨672923928766757016573055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3588927620089370755056293 672923928766757016573055)
                    ·
                      rfl

theorem cell23_3931544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 1, 4].length) (baseStart_3931544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931544 prefixEnd_3931544 := by exact prefixLift 3931544
  have htrace : WordTrace (prefixWord ++ tailWord_3931544) baseStart_3931544 baseEnd_3931544 := by
    simpa [prefixWord, tailWord_3931544, baseEnd_3931544] using wordTrace_append hprefix tailTrace_3931544
  have hstable : (prefixWord ++ tailWord_3931544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931544).length < 2 ^ (prefixWord ++ tailWord_3931544).sum := by decide
  have hdescent : baseEnd_3931544 < baseStart_3931544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931556 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 2, 6, 2]
def baseStart_3931556 : Nat := 118140960795 + 3931556 * 2 ^ 59
def prefixEnd_3931556 : Nat := 4983230072969 + 3 ^ 40 * 3931556 * 2
def baseEnd_3931556 : Nat := 2018777948068125002769109

theorem tailTrace_3931556 : CollatzResearch.WordTrace tailWord_3931556 prefixEnd_3931556 2018777948068125002769109 := by
  unfold tailWord_3931556
  simp only [CollatzResearch.WordTrace]
  refine ⟨71697813872325771576271261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95597085163101028768361681 71697813872325771576271261)
  ·
    refine ⟨26886680202122164341101723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71697813872325771576271261 26886680202122164341101723)
    ·
      refine ⟨40330020303183246511652585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26886680202122164341101723 40330020303183246511652585)
      ·
        refine ⟨30247515227387434883739439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40330020303183246511652585 30247515227387434883739439)
        ·
          refine ⟨45371272841081152325609159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30247515227387434883739439 45371272841081152325609159)
          ·
            refine ⟨68056909261621728488413739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45371272841081152325609159 68056909261621728488413739)
            ·
              refine ⟨102085363892432592732620609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68056909261621728488413739 102085363892432592732620609)
              ·
                refine ⟨76564022919324444549465457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102085363892432592732620609 76564022919324444549465457)
                ·
                  refine ⟨57423017189493333412099093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76564022919324444549465457 57423017189493333412099093)
                  ·
                    refine ⟨2691703930757500003692145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57423017189493333412099093 2691703930757500003692145)
                    ·
                      refine ⟨2018777948068125002769109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2691703930757500003692145 2018777948068125002769109)
                      ·
                        rfl

theorem cell23_3931556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_3931556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931556 prefixEnd_3931556 := by exact prefixLift 3931556
  have htrace : WordTrace (prefixWord ++ tailWord_3931556) baseStart_3931556 baseEnd_3931556 := by
    simpa [prefixWord, tailWord_3931556, baseEnd_3931556] using wordTrace_append hprefix tailTrace_3931556
  have hstable : (prefixWord ++ tailWord_3931556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931556).length < 2 ^ (prefixWord ++ tailWord_3931556).sum := by decide
  have hdescent : baseEnd_3931556 < baseStart_3931556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931576 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 3, 2, 3]
def baseStart_3931576 : Nat := 118140960795 + 3931576 * 2 ^ 59
def prefixEnd_3931576 : Nat := 4983230072969 + 3 ^ 40 * 3931576 * 2
def baseEnd_3931576 : Nat := 2018788217681214924519017

theorem tailTrace_3931576 : CollatzResearch.WordTrace tailWord_3931576 prefixEnd_3931576 2018788217681214924519017 := by
  unfold tailWord_3931576
  simp only [CollatzResearch.WordTrace]
  refine ⟨71698178602289543284135291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95597571469719391045513721 71698178602289543284135291)
  ·
    refine ⟨107547267903434314926202937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71698178602289543284135291 107547267903434314926202937)
    ·
      refine ⟨80660450927575736194652203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107547267903434314926202937 80660450927575736194652203)
      ·
        refine ⟨120990676391363604291978305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80660450927575736194652203 120990676391363604291978305)
        ·
          refine ⟨90743007293522703218983729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120990676391363604291978305 90743007293522703218983729)
          ·
            refine ⟨68057255470142027414237797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90743007293522703218983729 68057255470142027414237797)
            ·
              refine ⟨12760735400651630140169587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68057255470142027414237797 12760735400651630140169587)
              ·
                refine ⟨19141103100977445210254381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12760735400651630140169587 19141103100977445210254381)
                ·
                  refine ⟨7177913662866541953845393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19141103100977445210254381 7177913662866541953845393)
                  ·
                    refine ⟨5383435247149906465384045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7177913662866541953845393 5383435247149906465384045)
                    ·
                      refine ⟨2018788217681214924519017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5383435247149906465384045 2018788217681214924519017)
                      ·
                        rfl

theorem cell23_3931576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_3931576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931576 prefixEnd_3931576 := by exact prefixLift 3931576
  have htrace : WordTrace (prefixWord ++ tailWord_3931576) baseStart_3931576 baseEnd_3931576 := by
    simpa [prefixWord, tailWord_3931576, baseEnd_3931576] using wordTrace_append hprefix tailTrace_3931576
  have hstable : (prefixWord ++ tailWord_3931576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931576).length < 2 ^ (prefixWord ++ tailWord_3931576).sum := by decide
  have hdescent : baseEnd_3931576 < baseStart_3931576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931577 : List Nat := [1, 2, 1, 4, 5, 1, 1, 1, 2, 3, 2]
def baseStart_3931577 : Nat := 118140960795 + 3931577 * 2 ^ 59
def prefixEnd_3931577 : Nat := 4983230072969 + 3 ^ 40 * 3931577 * 2
def baseEnd_3931577 : Nat := 2018788731161869420606513

theorem tailTrace_3931577 : CollatzResearch.WordTrace tailWord_3931577 prefixEnd_3931577 2018788731161869420606513 := by
  unfold tailWord_3931577
  simp only [CollatzResearch.WordTrace]
  refine ⟨143396393677575463739056985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95597595785050309159371323 143396393677575463739056985)
  ·
    refine ⟨107547295258181597804292739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143396393677575463739056985 107547295258181597804292739)
    ·
      refine ⟨161320942887272396706439109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107547295258181597804292739 161320942887272396706439109)
      ·
        refine ⟨30247676791363574382457333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161320942887272396706439109 30247676791363574382457333)
        ·
          refine ⟨2835719699190335098355375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30247676791363574382457333 2835719699190335098355375)
          ·
            refine ⟨4253579548785502647533063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2835719699190335098355375 4253579548785502647533063)
            ·
              refine ⟨6380369323178253971299595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4253579548785502647533063 6380369323178253971299595)
              ·
                refine ⟨9570553984767380956949393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6380369323178253971299595 9570553984767380956949393)
                ·
                  refine ⟨7177915488575535717712045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9570553984767380956949393 7177915488575535717712045)
                  ·
                    refine ⟨2691718308215825894142017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7177915488575535717712045 2691718308215825894142017)
                    ·
                      refine ⟨2018788731161869420606513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2691718308215825894142017 2018788731161869420606513)
                      ·
                        rfl

theorem cell23_3931577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_3931577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931577 prefixEnd_3931577 := by exact prefixLift 3931577
  have htrace : WordTrace (prefixWord ++ tailWord_3931577) baseStart_3931577 baseEnd_3931577 := by
    simpa [prefixWord, tailWord_3931577, baseEnd_3931577] using wordTrace_append hprefix tailTrace_3931577
  have hstable : (prefixWord ++ tailWord_3931577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931577).length < 2 ^ (prefixWord ++ tailWord_3931577).sum := by decide
  have hdescent : baseEnd_3931577 < baseStart_3931577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931616 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 2, 7, 2]
def baseStart_3931616 : Nat := 118140960795 + 3931616 * 2 ^ 59
def prefixEnd_3931616 : Nat := 4983230072969 + 3 ^ 40 * 3931616 * 2
def baseEnd_3931616 : Nat := 2018808756907394768018833

theorem tailTrace_3931616 : CollatzResearch.WordTrace tailWord_3931616 prefixEnd_3931616 2018808756907394768018833 := by
  unfold tailWord_3931616
  simp only [CollatzResearch.WordTrace]
  refine ⟨71698908062217086699863351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95598544082956115599817801 71698908062217086699863351)
  ·
    refine ⟨107548362093325630049795027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71698908062217086699863351 107548362093325630049795027)
    ·
      refine ⟨161322543139988445074692541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107548362093325630049795027 161322543139988445074692541)
      ·
        refine ⟨60495953677495666903009703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161322543139988445074692541 60495953677495666903009703)
        ·
          refine ⟨90743930516243500354514555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60495953677495666903009703 90743930516243500354514555)
          ·
            refine ⟨136115895774365250531771833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90743930516243500354514555 136115895774365250531771833)
            ·
              refine ⟨102086921830773937898828875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136115895774365250531771833 102086921830773937898828875)
              ·
                refine ⟨153130382746160906848243313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102086921830773937898828875 153130382746160906848243313)
                ·
                  refine ⟨114847787059620680136182485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 153130382746160906848243313 114847787059620680136182485)
                  ·
                    refine ⟨2691745009209859690691777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 114847787059620680136182485 2691745009209859690691777)
                    ·
                      refine ⟨2018808756907394768018833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2691745009209859690691777 2018808756907394768018833)
                      ·
                        rfl

theorem cell23_3931616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_3931616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931616 prefixEnd_3931616 := by exact prefixLift 3931616
  have htrace : WordTrace (prefixWord ++ tailWord_3931616) baseStart_3931616 baseEnd_3931616 := by
    simpa [prefixWord, tailWord_3931616, baseEnd_3931616] using wordTrace_append hprefix tailTrace_3931616
  have hstable : (prefixWord ++ tailWord_3931616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931616).length < 2 ^ (prefixWord ++ tailWord_3931616).sum := by decide
  have hdescent : baseEnd_3931616 < baseStart_3931616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931623 : List Nat := [1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_3931623 : Nat := 118140960795 + 3931623 * 2 ^ 59
def prefixEnd_3931623 : Nat := 4983230072969 + 3 ^ 40 * 3931623 * 2
def baseEnd_3931623 : Nat := 2018812351271976240631301

theorem tailTrace_3931623 : CollatzResearch.WordTrace tailWord_3931623 prefixEnd_3931623 2018812351271976240631301 := by
  unfold tailWord_3931623
  simp only [CollatzResearch.WordTrace]
  refine ⟨143398071435408813595231523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95598714290272542396821015 143398071435408813595231523)
  ·
    refine ⟨215097107153113220392847285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143398071435408813595231523 215097107153113220392847285)
    ·
      refine ⟨20165353795604364411829433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 215097107153113220392847285 20165353795604364411829433)
      ·
        refine ⟨15124015346703273308872075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20165353795604364411829433 15124015346703273308872075)
        ·
          refine ⟨22686023020054909963308113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15124015346703273308872075 22686023020054909963308113)
          ·
            refine ⟨17014517265041182472481085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22686023020054909963308113 17014517265041182472481085)
            ·
              refine ⟨6380443974390443427180407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17014517265041182472481085 6380443974390443427180407)
              ·
                refine ⟨9570665961585665140770611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6380443974390443427180407 9570665961585665140770611)
                ·
                  refine ⟨14355998942378497711155917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9570665961585665140770611 14355998942378497711155917)
                  ·
                    refine ⟨5383499603391936641683469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14355998942378497711155917 5383499603391936641683469)
                    ·
                      refine ⟨2018812351271976240631301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5383499603391936641683469 2018812351271976240631301)
                      ·
                        rfl

theorem cell23_3931623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_3931623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931623 prefixEnd_3931623 := by exact prefixLift 3931623
  have htrace : WordTrace (prefixWord ++ tailWord_3931623) baseStart_3931623 baseEnd_3931623 := by
    simpa [prefixWord, tailWord_3931623, baseEnd_3931623] using wordTrace_append hprefix tailTrace_3931623
  have hstable : (prefixWord ++ tailWord_3931623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931623).length < 2 ^ (prefixWord ++ tailWord_3931623).sum := by decide
  have hdescent : baseEnd_3931623 < baseStart_3931623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931639 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 4, 6]
def baseStart_3931639 : Nat := 118140960795 + 3931639 * 2 ^ 59
def prefixEnd_3931639 : Nat := 4983230072969 + 3 ^ 40 * 3931639 * 2
def baseEnd_3931639 : Nat := 672940188987482726010409

theorem tailTrace_3931639 : CollatzResearch.WordTrace tailWord_3931639 prefixEnd_3931639 672940188987482726010409 := by
  unfold tailWord_3931639
  simp only [CollatzResearch.WordTrace]
  refine ⟨143398655003350848327813971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95599103335567232218542647 143398655003350848327813971)
  ·
    refine ⟨215097982505026272491720957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143398655003350848327813971 215097982505026272491720957)
    ·
      refine ⟨80661743439384852184395359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215097982505026272491720957 80661743439384852184395359)
      ·
        refine ⟨120992615159077278276593039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80661743439384852184395359 120992615159077278276593039)
        ·
          refine ⟨181488922738615917414889559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120992615159077278276593039 181488922738615917414889559)
          ·
            refine ⟨272233384107923876122334339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181488922738615917414889559 272233384107923876122334339)
            ·
              refine ⟨408350076161885814183501509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272233384107923876122334339 408350076161885814183501509)
              ·
                refine ⟨76565639280353590159406533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 408350076161885814183501509 76565639280353590159406533)
                ·
                  refine ⟨14356057365066298154888725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76565639280353590159406533 14356057365066298154888725)
                  ·
                    refine ⟨672940188987482726010409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14356057365066298154888725 672940188987482726010409)
                    ·
                      rfl

theorem cell23_3931639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_3931639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931639 prefixEnd_3931639 := by exact prefixLift 3931639
  have htrace : WordTrace (prefixWord ++ tailWord_3931639) baseStart_3931639 baseEnd_3931639 := by
    simpa [prefixWord, tailWord_3931639, baseEnd_3931639] using wordTrace_append hprefix tailTrace_3931639
  have hstable : (prefixWord ++ tailWord_3931639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931639).length < 2 ^ (prefixWord ++ tailWord_3931639).sum := by decide
  have hdescent : baseEnd_3931639 < baseStart_3931639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931663 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 8, 2, 2]
def baseStart_3931663 : Nat := 118140960795 + 3931663 * 2 ^ 59
def prefixEnd_3931663 : Nat := 4983230072969 + 3 ^ 40 * 3931663 * 2
def baseEnd_3931663 : Nat := 2018832890498156084131117

theorem tailTrace_3931663 : CollatzResearch.WordTrace tailWord_3931663 prefixEnd_3931663 2018832890498156084131117 := by
  unfold tailWord_3931663
  simp only [CollatzResearch.WordTrace]
  refine ⟨143399530355263900426687643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95599686903509266951125095 143399530355263900426687643)
  ·
    refine ⟨215099295532895850640031465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143399530355263900426687643 215099295532895850640031465)
    ·
      refine ⟨161324471649671887980023599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215099295532895850640031465 161324471649671887980023599)
      ·
        refine ⟨241986707474507831970035399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161324471649671887980023599 241986707474507831970035399)
        ·
          refine ⟨362980061211761747955053099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241986707474507831970035399 362980061211761747955053099)
          ·
            refine ⟨544470091817642621932579649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362980061211761747955053099 544470091817642621932579649)
            ·
              refine ⟨408352568863231966449434737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544470091817642621932579649 408352568863231966449434737)
              ·
                refine ⟨306264426647423974837076053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408352568863231966449434737 306264426647423974837076053)
                ·
                  refine ⟨3589036249774499705121985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 306264426647423974837076053 3589036249774499705121985)
                  ·
                    refine ⟨2691777187330874778841489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3589036249774499705121985 2691777187330874778841489)
                    ·
                      refine ⟨2018832890498156084131117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2691777187330874778841489 2018832890498156084131117)
                      ·
                        rfl

theorem cell23_3931663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 2, 2].length) (baseStart_3931663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931663 prefixEnd_3931663 := by exact prefixLift 3931663
  have htrace : WordTrace (prefixWord ++ tailWord_3931663) baseStart_3931663 baseEnd_3931663 := by
    simpa [prefixWord, tailWord_3931663, baseEnd_3931663] using wordTrace_append hprefix tailTrace_3931663
  have hstable : (prefixWord ++ tailWord_3931663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931663).length < 2 ^ (prefixWord ++ tailWord_3931663).sum := by decide
  have hdescent : baseEnd_3931663 < baseStart_3931663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931676 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_3931676 : Nat := 118140960795 + 3931676 * 2 ^ 59
def prefixEnd_3931676 : Nat := 4983230072969 + 3 ^ 40 * 3931676 * 2
def baseEnd_3931676 : Nat := 2018839565746664533268557

theorem tailTrace_3931676 : CollatzResearch.WordTrace tailWord_3931676 prefixEnd_3931676 2018839565746664533268557 := by
  unfold tailWord_3931676
  simp only [CollatzResearch.WordTrace]
  refine ⟨71700002252108401823455441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95600003002811202431273921 71700002252108401823455441)
  ·
    refine ⟨53775001689081301367591581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71700002252108401823455441 53775001689081301367591581)
    ·
      refine ⟨20165625633405488012846843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53775001689081301367591581 20165625633405488012846843)
      ·
        refine ⟨30248438450108232019270265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20165625633405488012846843 30248438450108232019270265)
        ·
          refine ⟨22686328837581174014452699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30248438450108232019270265 22686328837581174014452699)
          ·
            refine ⟨34029493256371761021679049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22686328837581174014452699 34029493256371761021679049)
            ·
              refine ⟨25522119942278820766259287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34029493256371761021679049 25522119942278820766259287)
              ·
                refine ⟨38283179913418231149388931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25522119942278820766259287 38283179913418231149388931)
                ·
                  refine ⟨57424769870127346724083397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38283179913418231149388931 57424769870127346724083397)
                  ·
                    refine ⟨10767144350648877510765637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57424769870127346724083397 10767144350648877510765637)
                    ·
                      refine ⟨2018839565746664533268557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10767144350648877510765637 2018839565746664533268557)
                      ·
                        rfl

theorem cell23_3931676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_3931676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931676 prefixEnd_3931676 := by exact prefixLift 3931676
  have htrace : WordTrace (prefixWord ++ tailWord_3931676) baseStart_3931676 baseEnd_3931676 := by
    simpa [prefixWord, tailWord_3931676, baseEnd_3931676] using wordTrace_append hprefix tailTrace_3931676
  have hstable : (prefixWord ++ tailWord_3931676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931676).length < 2 ^ (prefixWord ++ tailWord_3931676).sum := by decide
  have hdescent : baseEnd_3931676 < baseStart_3931676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931678 : List Nat := [4, 3, 3, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_3931678 : Nat := 118140960795 + 3931678 * 2 ^ 59
def prefixEnd_3931678 : Nat := 4983230072969 + 3 ^ 40 * 3931678 * 2
def baseEnd_3931678 : Nat := 2018840592707973525443549

theorem tailTrace_3931678 : CollatzResearch.WordTrace tailWord_3931678 prefixEnd_3931678 2018840592707973525443549 := by
  unfold tailWord_3931678
  simp only [CollatzResearch.WordTrace]
  refine ⟨17925009681276194748560461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95600051633473038658989125 17925009681276194748560461)
  ·
    refine ⟨6721878630478573030710173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17925009681276194748560461 6721878630478573030710173)
    ·
      refine ⟨2520704486429464886516315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6721878630478573030710173 2520704486429464886516315)
      ·
        refine ⟨3781056729644197329774473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2520704486429464886516315 3781056729644197329774473)
        ·
          refine ⟨2835792547233147997330855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3781056729644197329774473 2835792547233147997330855)
          ·
            refine ⟨4253688820849721995996283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2835792547233147997330855 4253688820849721995996283)
            ·
              refine ⟨6380533231274582993994425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4253688820849721995996283 6380533231274582993994425)
              ·
                refine ⟨4785399923455937245495819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6380533231274582993994425 4785399923455937245495819)
                ·
                  refine ⟨7178099885183905868243729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4785399923455937245495819 7178099885183905868243729)
                  ·
                    refine ⟨5383574913887929401182797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7178099885183905868243729 5383574913887929401182797)
                    ·
                      refine ⟨2018840592707973525443549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5383574913887929401182797 2018840592707973525443549)
                      ·
                        rfl

theorem cell23_3931678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_3931678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931678 prefixEnd_3931678 := by exact prefixLift 3931678
  have htrace : WordTrace (prefixWord ++ tailWord_3931678) baseStart_3931678 baseEnd_3931678 := by
    simpa [prefixWord, tailWord_3931678, baseEnd_3931678] using wordTrace_append hprefix tailTrace_3931678
  have hstable : (prefixWord ++ tailWord_3931678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931678).length < 2 ^ (prefixWord ++ tailWord_3931678).sum := by decide
  have hdescent : baseEnd_3931678 < baseStart_3931678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931696 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 3]
def baseStart_3931696 : Nat := 118140960795 + 3931696 * 2 ^ 59
def prefixEnd_3931696 : Nat := 4983230072969 + 3 ^ 40 * 3931696 * 2
def baseEnd_3931696 : Nat := 2018849835359754455018465

theorem tailTrace_3931696 : CollatzResearch.WordTrace tailWord_3931696 prefixEnd_3931696 2018849835359754455018465 := by
  unfold tailWord_3931696
  simp only [CollatzResearch.WordTrace]
  refine ⟨71700366982072173531319471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95600489309429564708425961 71700366982072173531319471)
  ·
    refine ⟨107550550473108260296979207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71700366982072173531319471 107550550473108260296979207)
    ·
      refine ⟨161325825709662390445468811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107550550473108260296979207 161325825709662390445468811)
      ·
        refine ⟨241988738564493585668203217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161325825709662390445468811 241988738564493585668203217)
        ·
          refine ⟨181491553923370189251152413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241988738564493585668203217 181491553923370189251152413)
          ·
            refine ⟨68059332721263820969182155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181491553923370189251152413 68059332721263820969182155)
            ·
              refine ⟨102088999081895731453773233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68059332721263820969182155 102088999081895731453773233)
              ·
                refine ⟨76566749311421798590329925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102088999081895731453773233 76566749311421798590329925)
                ·
                  refine ⟨14356265495891587235686861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76566749311421798590329925 14356265495891587235686861)
                  ·
                    refine ⟨5383599560959345213382573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14356265495891587235686861 5383599560959345213382573)
                    ·
                      refine ⟨2018849835359754455018465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5383599560959345213382573 2018849835359754455018465)
                      ·
                        rfl

theorem cell23_3931696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 3].length) (baseStart_3931696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931696 prefixEnd_3931696 := by exact prefixLift 3931696
  have htrace : WordTrace (prefixWord ++ tailWord_3931696) baseStart_3931696 baseEnd_3931696 := by
    simpa [prefixWord, tailWord_3931696, baseEnd_3931696] using wordTrace_append hprefix tailTrace_3931696
  have hstable : (prefixWord ++ tailWord_3931696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931696).length < 2 ^ (prefixWord ++ tailWord_3931696).sum := by decide
  have hdescent : baseEnd_3931696 < baseStart_3931696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931713 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_3931713 : Nat := 118140960795 + 3931713 * 2 ^ 59
def prefixEnd_3931713 : Nat := 4983230072969 + 3 ^ 40 * 3931713 * 2
def baseEnd_3931713 : Nat := 2018858564530880888505887

theorem tailTrace_3931713 : CollatzResearch.WordTrace tailWord_3931713 prefixEnd_3931713 2018858564530880888505887 := by
  unfold tailWord_3931713
  simp only [CollatzResearch.WordTrace]
  refine ⟨143401354005082758966007793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95600902670055172644005195 143401354005082758966007793)
  ·
    refine ⟨107551015503812069224505845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143401354005082758966007793 107551015503812069224505845)
    ·
      refine ⟨10082907703482381489797423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107551015503812069224505845 10082907703482381489797423)
      ·
        refine ⟨15124361555223572234696135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10082907703482381489797423 15124361555223572234696135)
        ·
          refine ⟨22686542332835358352044203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15124361555223572234696135 22686542332835358352044203)
          ·
            refine ⟨34029813499253037528066305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22686542332835358352044203 34029813499253037528066305)
            ·
              refine ⟨25522360124439778146049729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34029813499253037528066305 25522360124439778146049729)
              ·
                refine ⟨19141770093329833609537297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25522360124439778146049729 19141770093329833609537297)
                ·
                  refine ⟨14356327569997375207152973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19141770093329833609537297 14356327569997375207152973)
                  ·
                    refine ⟨5383622838749015702682365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14356327569997375207152973 5383622838749015702682365)
                    ·
                      refine ⟨2018858564530880888505887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5383622838749015702682365 2018858564530880888505887)
                      ·
                        rfl

theorem cell23_3931713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_3931713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931713 prefixEnd_3931713 := by exact prefixLift 3931713
  have htrace : WordTrace (prefixWord ++ tailWord_3931713) baseStart_3931713 baseEnd_3931713 := by
    simpa [prefixWord, tailWord_3931713, baseEnd_3931713] using wordTrace_append hprefix tailTrace_3931713
  have hstable : (prefixWord ++ tailWord_3931713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931713).length < 2 ^ (prefixWord ++ tailWord_3931713).sum := by decide
  have hdescent : baseEnd_3931713 < baseStart_3931713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3931736 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 1, 3, 4]
def baseStart_3931736 : Nat := 118140960795 + 3931736 * 2 ^ 59
def prefixEnd_3931736 : Nat := 4983230072969 + 3 ^ 40 * 3931736 * 2
def baseEnd_3931736 : Nat := 2018870374585934298518281

theorem tailTrace_3931736 : CollatzResearch.WordTrace tailWord_3931736 prefixEnd_3931736 2018870374585934298518281 := by
  unfold tailWord_3931736
  simp only [CollatzResearch.WordTrace]
  refine ⟨71701096441999716947047531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95601461922666289262730041 71701096441999716947047531)
  ·
    refine ⟨107551644662999575420571297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71701096441999716947047531 107551644662999575420571297)
    ·
      refine ⟨80663733497249681565428473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107551644662999575420571297 80663733497249681565428473)
      ·
        refine ⟨60497800122937261174071355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80663733497249681565428473 60497800122937261174071355)
        ·
          refine ⟨90746700184405891761107033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60497800122937261174071355 90746700184405891761107033)
          ·
            refine ⟨68060025138304418820830275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90746700184405891761107033 68060025138304418820830275)
            ·
              refine ⟨102090037707456628231245413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68060025138304418820830275 102090037707456628231245413)
              ·
                refine ⟨19141882070148117793358515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102090037707456628231245413 19141882070148117793358515)
                ·
                  refine ⟨28712823105222176690037773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19141882070148117793358515 28712823105222176690037773)
                  ·
                    refine ⟨10767308664458316258764165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28712823105222176690037773 10767308664458316258764165)
                    ·
                      refine ⟨2018870374585934298518281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10767308664458316258764165 2018870374585934298518281)
                      ·
                        rfl

theorem cell23_3931736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_3931736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3931736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3931736 prefixEnd_3931736 := by exact prefixLift 3931736
  have htrace : WordTrace (prefixWord ++ tailWord_3931736) baseStart_3931736 baseEnd_3931736 := by
    simpa [prefixWord, tailWord_3931736, baseEnd_3931736] using wordTrace_append hprefix tailTrace_3931736
  have hstable : (prefixWord ++ tailWord_3931736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3931736).length < 2 ^ (prefixWord ++ tailWord_3931736).sum := by decide
  have hdescent : baseEnd_3931736 < baseStart_3931736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3931736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
